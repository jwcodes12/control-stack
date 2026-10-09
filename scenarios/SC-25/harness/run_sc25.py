#!/usr/bin/env python3
"""SC-25 audit-before-execute queue (unprivileged). Preregistration: prereg/SC25-AUDIT-QUEUE.md (PREREG-SC25-AUDITQ-v1).

Defensive reference test on one Linux host. A benign agent (this runner's client threads) submits operations (JSON
content) to a queue/executor process. A separate auditor process records PASS/FAIL verdicts with the digest and
the full content it saw; a separate approver process approves irreversible-class operations (trusted classifier).
The executor runs an operation only if a PASS for exactly its CURRENT content digest exists, re-validated atomically
at fire time, plus an exact-digest approval by another principal if irreversible; an operation with no verdict
after TIMEOUT expires and never executes; an admin HALT stops everything. "Execution" appends to a disposable
effect log owned by the executor. Each hypothesis is repeated --reps times on fresh processes:

  H1 every effect-log entry has an auditor PASS for exactly its content and, if irreversible, an approval; FAIL
     verdicts and missing approvals block                                         (sc25_safe, sc25_content_safe)
  H2 amend after audit (with and without an intervening check) is refused at fire time; a re-audit of the new
     content lets it run                          (deployed halves of digest_unchecked_breaks, nonatomic_check_race_breaks)
  H3 an operation not audited within TIMEOUT expires and never executes, even after a later PASS
                                                       (expired_never_executes; deployed half of fail_open_timeout_breaks)
  H4 usefulness: >= 95% of 100 honest operations execute within L_USE seconds of submission
  H5 admin HALT: nothing executes after the halt, already-audited operations included         (halt_freezes,
                                                                                               no_halt_check_breaks)
  H6 NEGATIVE_CONTROL configurations, each must be caught by the reconciliation: fail-open timeout, digest unchecked,
     non-atomic check/fire, constant digest, agent-declared class    (fail_open_timeout_breaks, digest_unchecked_breaks,
                                  nonatomic_check_race_breaks, digest_only_executes_unaudited, agent_declared_class_breaks)

Receipts go to --out, which must not exist. No root, no accounts, no network: Unix sockets in a fresh
/var/tmp/sc25-run-* directory, removed afterwards. Python 3.9 compatible (system interpreter).
"""
import argparse
import datetime
import hashlib
import json
import math
import os
import platform
import re
import select
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import threading
import time
import traceback
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
import reconcile  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "SC25-AUDIT-QUEUE.md"
PREREG_ID = "PREREG-SC25-AUDITQ-v1"
HYPS = ["H1", "H2", "H3", "H4", "H5", "H6"]
CONTROLS = {"H6"}

# Preregistered constants (prereg §2-§3). Changing any of them needs a new prereg ID.
TIMEOUT = 0.5            # s without any verdict -> the executor expires the operation
WAIT_PAST_TIMEOUT = 0.3  # s the runner waits beyond TIMEOUT before late audits / fires (H3, H6a)
H4_OPS = 100             # honest operations (H4); every 5th is irreversible
THREADS = 4              # agent client threads (H4, H5)
USEFUL_FRAC = 0.95       # H4
H5_PRE, H5_POST = 0.5, 0.5   # s of traffic before and after the HALT
LIFETIME = 30.0
READY_TIMEOUT = 10.0
RPC_TIMEOUT = 5.0
WALL_LIMIT = 115
# Tolerances fixed from dry-run calibration (prereg §3.0).
TAU_X = 0.10             # s, expiry no later than TIMEOUT + TAU_X after submission (calibrated)
L_USE = 0.30             # s, H4 latency bound submission -> executed (calibrated)

H6_CONFIGS = {
    "a_fail_open_timeout": ["--fail-open-timeout"],
    "b_digest_unchecked": ["--digest-unchecked"],
    "c_nonatomic": ["--nonatomic"],
    "d_const_digest": ["--digest", "const"],
    "e_agent_class": ["--agent-class"],
}


# ---------------------------------------------------------------- plumbing
class Rec:
    def __init__(self, hyp, rep):
        self.hyp, self.rep = hyp, rep
        self.checks, self.raw, self.error = [], {}, None

    def check(self, name, expected, observed, ok):
        self.checks.append({"name": name, "expected": expected, "observed": observed, "pass": bool(ok)})

    def passed(self):
        return self.error is None and bool(self.checks) and all(c["pass"] for c in self.checks)

    def as_dict(self):
        return {"hyp": self.hyp, "rep": self.rep, "negative_control": self.hyp in CONTROLS, "pass": self.passed(),
                "error": self.error, "checks": self.checks, "raw": self.raw}


class Ctx:
    def __init__(self):
        self.work = Path(tempfile.mkdtemp(prefix="sc25-run-", dir="/var/tmp"))
        self.work.chmod(0o700)
        self.logs = self.work / "logs"
        self.logs.mkdir()
        self.py = sys.executable

    def script(self, name, *args):
        return [self.py, "-I", "-S", "-B", str(HERE / name)] + [str(a) for a in args]


def read_tag(p, tag, timeout=READY_TIMEOUT):
    fd, buf, t0 = p.stdout.fileno(), b"", time.monotonic()
    while b"\n" not in buf:
        rem = timeout - (time.monotonic() - t0)
        if rem <= 0:
            raise TimeoutError("no %s within %.1fs from pid %d" % (tag, timeout, p.pid))
        r, _, _ = select.select([fd], [], [], rem)
        if not r:
            continue
        chunk = os.read(fd, 65536)
        if not chunk:
            raise RuntimeError("EOF before %s from pid %d (rc=%s)" % (tag, p.pid, p.poll()))
        buf += chunk
    line = buf.split(b"\n", 1)[0].decode()
    if not line.startswith(tag + " "):
        raise RuntimeError("unexpected output: %r" % line)
    return json.loads(line[len(tag) + 1:])


def ancestors():
    out, pid = set(), os.getpid()
    while pid > 1:
        out.add(pid)
        try:
            with open("/proc/%d/status" % pid) as fh:
                pid = int([l for l in fh if l.startswith("PPid:")][0].split()[1])
        except (OSError, IndexError, ValueError):
            break
    return out


def proc_scan(marker):
    """live processes (not this runner or its ancestors) with a command-line ARGUMENT that starts with marker
    (every child of a run gets paths under its own work directory as arguments)"""
    out, skip = [], ancestors()
    for d in os.listdir("/proc"):
        if not d.isdigit() or int(d) in skip:
            continue
        try:
            with open("/proc/%s/cmdline" % d, "rb") as fh:
                args = [x.decode("utf-8", "replace") for x in fh.read().split(b"\0") if x]
            with open("/proc/%s/stat" % d) as fh:
                st = fh.read()
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue
        state = st[st.rindex(")") + 2:].split()[0]
        if any(x.startswith(marker) for x in args) and state not in ("Z", "X"):
            out.append({"pid": int(d), "state": state, "cmd": " ".join(args)[:200]})
    return out


def rpc(path, obj, timeout=RPC_TIMEOUT):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    try:
        s.connect(str(path))
        f = s.makefile("rwb", buffering=0)
        f.write((json.dumps(obj) + "\n").encode())
        line = f.readline()
        if not line:
            raise ConnectionError("no reply")
        return json.loads(line)
    finally:
        s.close()


class Stack:
    """auditor + approver + executor for one repetition (or one control configuration)"""

    def __init__(self, ctx, tag, flags=()):
        self.ctx, self.tag = ctx, tag
        self.d = ctx.work / tag
        self.d.mkdir()
        self.procs = []
        dig = "const" if "const" in flags else "sha256"
        svc = self.d / "svc.sock"
        self.aud_sock, self.app_sock = self.d / "auditor.sock", self.d / "approver.sock"
        self.aud_log, self.app_log = self.d / "auditor.jsonl", self.d / "approver.jsonl"
        self.eff_log, self.journal = self.d / "effects.jsonl", self.d / "executor-journal.jsonl"
        for role, sock, log, name in (("auditor", self.aud_sock, self.aud_log, "auditor-1"),
                                      ("approver", self.app_sock, self.app_log, "approver-1")):
            p = self._spawn(role, ctx.script("principal.py", "--role", role, "--name", name, "--sock", sock,
                                             "--executor", svc, "--log", log, "--digest", dig,
                                             "--lifetime", LIFETIME))
            read_tag(p, "READY")
        self.ex = self._spawn("executor", ctx.script("executor.py", "--dir", self.d, "--auditor", self.aud_sock,
                                                     "--approver", self.app_sock, "--effects", self.eff_log,
                                                     "--journal", self.journal, "--timeout", TIMEOUT,
                                                     "--lifetime", LIFETIME, *flags))
        self.config = read_tag(self.ex, "READY")["config"]
        self.agent, self.admin = self.d / "agent.sock", self.d / "admin.sock"

    def _spawn(self, name, argv):
        with open(str(self.ctx.logs / ("%s-%s.stderr" % (self.tag, name))), "wb") as se:
            p = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=se, close_fds=True)
        self.procs.append(p)
        return p

    # agent / scheduler / admin calls
    def submit(self, id_, content, declared=None):
        return rpc(self.agent, {"op": "submit", "id": id_, "content": content,
                                "declared": reconcile.classify(content) if declared is None else declared})

    def amend(self, id_, content):
        return rpc(self.agent, {"op": "amend", "id": id_, "content": content})

    def check_(self, id_):
        return rpc(self.agent, {"op": "check", "id": id_})

    def fire(self, id_):
        return rpc(self.agent, {"op": "fire", "id": id_})

    def audit(self, id_):
        return rpc(self.aud_sock, {"op": "audit", "id": id_})

    def approve(self, id_):
        return rpc(self.app_sock, {"op": "approve", "id": id_})

    def halt(self):
        return rpc(self.admin, {"op": "halt"})

    def logs(self):
        return (reconcile.load(str(self.eff_log)), reconcile.load(str(self.aud_log)),
                reconcile.load(str(self.app_log)))

    def journal_events(self):
        if not self.journal.exists():
            return []
        return [json.loads(l) for l in open(str(self.journal)) if l.strip()]

    def close(self):
        for p in self.procs:
            if p.poll() is None:
                try:
                    p.kill()
                except OSError:
                    pass
        for p in self.procs:
            try:
                p.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
            if p.stdout:
                p.stdout.close()


def content(i, action="update", amount=10, note="routine maintenance"):
    return {"action": action, "target": "item-%d" % i, "amount": amount, "note": note}


def keep(out, st, extra=None):
    d = out / "logs" / st.tag
    d.mkdir(parents=True)
    for f in (st.eff_log, st.aud_log, st.app_log, st.journal):
        if f.exists():
            shutil.copy2(str(f), str(d / f.name))
    if extra is not None:
        with open(str(d / "client.json"), "w") as fh:
            json.dump(extra, fh, indent=1, sort_keys=True)


def check_reconcile(R, eff, aud, app, name="reconciliation"):
    rc = reconcile.reconcile(eff, aud, app)
    R.raw.setdefault("reconcile", {})[name] = rc
    R.check("%s: every executed op has an auditor PASS of exactly its content committed before it, an approval by "
            "another principal if irreversible, and runs once (sc25_safe, sc25_content_safe)" % name,
            {"unaudited": 0, "unapproved": 0, "dup": 0, "uncommitted": 0},
            {"effects": rc["effects"], "unaudited": len(rc["unaudited"]), "unapproved": len(rc["unapproved"]),
             "dup": len(rc["dup"]), "uncommitted": len(rc["uncommitted_effect"])}, rc["ok"])
    return rc


# ---------------------------------------------------------------- hypotheses
def h1(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h1" % rep)
    plan, res = [], {}
    for i in range(20):
        plan.append(("rev-%d" % i, content(i), "exec"))
    for i, act in enumerate(["transfer", "delete", "deploy", "transfer", "delete"]):
        plan.append(("irr-%d" % i, content(100 + i, action=act, amount=50), "exec-approved"))
    for i in range(3):
        plan.append(("fail-%d" % i, content(200 + i, note="FORBIDDEN step"), "audit-fail"))
    for i in range(2):
        plan.append(("noappr-%d" % i, content(300 + i, action="transfer", amount=20), "no-approval"))
    try:
        for id_, c, kind in plan:
            r = {"submit": st.submit(id_, c), "audit": st.audit(id_)}
            if kind == "exec-approved":
                r["approve"] = st.approve(id_)
            r["fire"] = st.fire(id_)
            r["fire_again"] = st.fire(id_) if kind.startswith("exec") else None
            res[id_] = r
    finally:
        st.close()
    eff, aud, app = st.logs()
    keep(out, st, res)
    want = sorted(i for i, _, k in plan if k.startswith("exec"))
    got = sorted(e["id"] for e in eff)
    R.raw.update(executed=got, refusals={i: res[i]["fire"].get("error") for i, _, k in plan if not k.startswith("exec")})
    R.check("exactly the 25 audited (and, if irreversible, approved) operations executed", want, got, want == got)
    reasons = {i: res[i]["fire"].get("error") for i, _, k in plan if not k.startswith("exec")}
    exp = {i: ("no PASS for the current digest" if k == "audit-fail" else "no approval for the current digest")
           for i, _, k in plan if not k.startswith("exec")}
    R.check("FAIL verdicts and missing approvals refused with the right reason (audit_fail_blocks)", exp, reasons,
            exp == reasons)
    again = [i for i, _, k in plan if k.startswith("exec") and res[i]["fire_again"].get("ok")]
    R.check("a second fire of an executed operation is refused", [], again, not again)
    check_reconcile(R, eff, aud, app)
    mt = reconcile.mutation_selftest(eff, aud, app)
    R.check("reconciliation sensitivity: each injected defect in a copy of the stored logs is flagged", True, mt,
            all(mt.values()) and len(mt) >= 6)


def h2(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h2" % rep)
    res = {}
    try:
        for i in range(5):  # shape A: submit, audit, amend, fire; then re-audit and fire
            id_ = "A-%d" % i
            r = {"submit": st.submit(id_, content(i, amount=10)), "audit1": st.audit(id_),
                 "amend": st.amend(id_, content(i, amount=11, note="amended after audit")), "fire1": st.fire(id_)}
            r["audit2"] = st.audit(id_)
            r["fire2"] = st.fire(id_)
            res[id_] = r
        for i in range(5):  # shape B: submit, audit, check, amend, fire (the race shape); amended content fails audit
            id_ = "B-%d" % i
            r = {"submit": st.submit(id_, content(50 + i)), "audit1": st.audit(id_), "check": st.check_(id_),
                 "amend": st.amend(id_, content(50 + i, note="FORBIDDEN amended after check")),
                 "fire1": st.fire(id_)}
            r["audit2"] = st.audit(id_)
            r["fire2"] = st.fire(id_)
            res[id_] = r
    finally:
        st.close()
    eff, aud, app = st.logs()
    keep(out, st, res)
    first = {i: (r["audit1"]["rec"]["pass"], r["fire1"].get("ok"), r["fire1"].get("error")) for i, r in res.items()}
    R.raw.update(first_fire=first, executed=sorted(e["id"] for e in eff))
    okA = all(res["A-%d" % i]["audit1"]["rec"]["pass"] and not res["A-%d" % i]["fire1"].get("ok") and
              res["A-%d" % i]["fire1"].get("error") == "no PASS for the current digest" for i in range(5))
    R.check("H2 shape A (audit, amend, fire): fire refused although the original content had a PASS", True, first, okA)
    okB = all(res["B-%d" % i]["check"].get("ok") and not res["B-%d" % i]["fire1"].get("ok") for i in range(5))
    R.check("H2 shape B (audit, check, amend, fire): fire refused although the check had passed (atomic "
            "re-validation)", True, {i: (res[i]["check"].get("ok"), res[i]["fire1"].get("error"))
                                     for i in res if i.startswith("B")}, okB)
    exA = {e["id"]: e["content"] for e in eff if e["id"].startswith("A")}
    okA2 = all(exA.get("A-%d" % i) == content(i, amount=11, note="amended after audit") for i in range(5))
    R.check("after a PASS for the amended content, shape A executes exactly the amended content", True,
            sorted(exA), okA2 and len(exA) == 5)
    exB = [e["id"] for e in eff if e["id"].startswith("B")]
    R.check("shape B (amended to content that fails audit) never executes", [], exB, not exB)
    check_reconcile(R, eff, aud, app)


def h3(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h3" % rep)
    res = {}
    try:
        for i in range(10):
            res["T-%d" % i] = {"submit": st.submit("T-%d" % i, content(400 + i))}
        for i in range(5):
            id_ = "P-%d" % i
            res[id_] = {"submit": st.submit(id_, content(500 + i)), "audit": st.audit(id_), "fire": st.fire(id_)}
        time.sleep(TIMEOUT + WAIT_PAST_TIMEOUT)
        for i in range(10):
            id_ = "T-%d" % i
            res[id_]["late_audit"] = st.audit(id_)
            res[id_]["fire"] = st.fire(id_)
    finally:
        st.close()
    eff, aud, app = st.logs()
    ev = st.journal_events()
    keep(out, st, res)
    expd = {e["id"]: (e["t"] - e["t_submit"]) / 1e9 for e in ev if e["ev"] == "expired"}
    late = {k: round(v - TIMEOUT, 4) for k, v in expd.items()}
    R.raw.update(expiry_after_submit_s=expd, expiry_lateness_s=late, executed=sorted(e["id"] for e in eff))
    tids = ["T-%d" % i for i in range(10)]
    R.check("all 10 unaudited operations expired", tids, sorted(expd), sorted(expd) == tids)
    R.check("expiry happened after TIMEOUT and no later than TIMEOUT + TAU_X", "[0, %.2f] s late" % TAU_X, late,
            all(0 <= v <= TAU_X for v in late.values()) and len(late) == 10)
    lp = all(res[t]["late_audit"].get("ok") and res[t]["late_audit"]["rec"]["pass"] for t in tids)
    R.check("non-vacuity: a PASS verdict was recorded later for each expired operation", True, lp, lp)
    ref = {t: res[t]["fire"].get("error") for t in tids}
    R.check("H3: expired operations never execute, even with a later PASS (expired_never_executes)",
            {t: "expired" for t in tids}, ref, all(v == "expired" for v in ref.values()) and
            not [e for e in eff if e["id"].startswith("T")])
    pe = sorted(e["id"] for e in eff if e["id"].startswith("P"))
    R.check("promptly audited operations in the same run execute", ["P-%d" % i for i in range(5)], pe,
            pe == ["P-%d" % i for i in range(5)])
    check_reconcile(R, eff, aud, app)


def pipeline(st, id_, c, lat):
    t0 = time.monotonic_ns()
    st.submit(id_, c)
    st.audit(id_)
    if reconcile.classify(c):
        st.approve(id_)
    r = st.fire(id_)
    t1 = time.monotonic_ns()
    lat[id_] = {"ok": bool(r.get("ok")), "lat_s": (t1 - t0) / 1e9, "error": r.get("error"), "t1": t1}


def h4(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h4" % rep)
    lat = {}
    try:
        def worker(k):
            for j in range(H4_OPS // THREADS):
                i = k * (H4_OPS // THREADS) + j
                c = content(600 + i, action="transfer" if i % 5 == 0 else "update", amount=5 + i % 50)
                pipeline(st, "U-%03d" % i, c, lat)
        ts = [threading.Thread(target=worker, args=(k,)) for k in range(THREADS)]
        t0 = time.monotonic()
        for t in ts:
            t.start()
        for t in ts:
            t.join(timeout=60)
        wall = time.monotonic() - t0
    finally:
        st.close()
    eff, aud, app = st.logs()
    keep(out, st, lat)
    ls = sorted(v["lat_s"] for v in lat.values() if v["ok"])
    within = sum(1 for v in lat.values() if v["ok"] and v["lat_s"] <= L_USE)
    pc = lambda q: None if not ls else round(ls[min(len(ls) - 1, int(round(q * (len(ls) - 1))))] * 1e3, 2)
    R.raw.update(latency_ms={"p50": pc(0.5), "p95": pc(0.95), "p99": pc(0.99), "max": pc(1.0)}, wall_s=round(wall, 3),
                 executed=len(ls), errors={k: v["error"] for k, v in lat.items() if not v["ok"]})
    R.check("H4: >= %.0f%% of %d honest operations executed within L_USE = %.2f s" % (USEFUL_FRAC * 100, H4_OPS,
                                                                                       L_USE),
            ">= %d" % math.ceil(USEFUL_FRAC * H4_OPS), {"within": within, "executed": len(ls), "sent": len(lat),
                                                        "latency_ms": R.raw["latency_ms"]},
            len(lat) == H4_OPS and within >= math.ceil(USEFUL_FRAC * H4_OPS))
    check_reconcile(R, eff, aud, app)


def h5(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h5" % rep)
    lat, stop, res = {}, threading.Event(), {}
    try:
        for i in range(3):  # audited and checked, not yet fired
            id_ = "Q-%d" % i
            res[id_] = {"submit": st.submit(id_, content(700 + i)), "audit": st.audit(id_), "check": st.check_(id_)}

        def worker(k):
            j = 0
            while not stop.is_set():
                pipeline(st, "H-%d-%03d" % (k, j), content(800 + 100 * k + j), lat)
                j += 1
        ts = [threading.Thread(target=worker, args=(k,)) for k in range(THREADS)]
        for t in ts:
            t.start()
        time.sleep(H5_PRE)
        t_send = time.monotonic_ns()
        h = st.halt()
        time.sleep(H5_POST)
        stop.set()
        for t in ts:
            t.join(timeout=10)
        for i in range(3):
            res["Q-%d" % i]["fire_after_halt"] = st.fire("Q-%d" % i)
        res["submit_after_halt"] = st.submit("Z-0", content(999))
    finally:
        st.close()
    eff, aud, app = st.logs()
    keep(out, st, {"pipelines": lat, "ops": res})
    t_h = h["t"]
    after = [e["id"] for e in eff if e["t"] is not None and e["t"] > t_h]
    before = [e["id"] for e in eff if e["t"] is not None and e["t"] <= t_h]
    post_ok = [k for k, v in lat.items() if v["ok"] and v["t1"] > t_h and k not in before]
    started_after = [k for k, v in lat.items() if not v["ok"] and v["error"] != "halted" and v["t1"] > t_h]
    R.raw.update(t_halt_send=t_send, t_halt=t_h, executed_before=len(before), executed_after=after,
                 pipelines_after=len([v for v in lat.values() if v["t1"] > t_h]))
    R.check("precondition: operations executed before the HALT", ">= 1", len(before), len(before) >= 1)
    R.check("H5: no effect committed after the HALT (halt_freezes)", [], after, not after and not post_ok)
    qa = {i: res["Q-%d" % i]["fire_after_halt"].get("error") for i in range(3)}
    R.check("audited and checked operations do not fire after the HALT (no_halt_check_breaks, deployed half)",
            {i: "halted" for i in range(3)}, qa, all(v == "halted" for v in qa.values()))
    R.check("submissions after the HALT refused", "halted", res["submit_after_halt"].get("error"),
            res["submit_after_halt"].get("error") == "halted")
    R.check("every client pipeline that finished after the HALT ended refused", [], started_after, not started_after)
    check_reconcile(R, eff, aud, app)


def h6(ctx, out, rep, R):
    fired = {}
    for name, flags in H6_CONFIGS.items():
        st = Stack(ctx, "r%d-h6%s" % (rep, name[0]), flags)
        res = {}
        ids = ["%s-%d" % (name[0].upper(), i) for i in range(3)]
        try:
            for i, id_ in enumerate(ids):
                if name.startswith("a"):
                    res[id_] = {"submit": st.submit(id_, content(900 + i))}
                elif name.startswith("e"):
                    c = content(900 + i, action="transfer", amount=40)
                    res[id_] = {"submit": st.submit(id_, c, declared=False), "audit": st.audit(id_),
                                "fire": st.fire(id_)}
                else:
                    r = {"submit": st.submit(id_, content(900 + i)), "audit": st.audit(id_)}
                    if name.startswith("c"):
                        r["check"] = st.check_(id_)
                    r["amend"] = st.amend(id_, content(900 + i, amount=999, note="amended after audit"))
                    r["fire"] = st.fire(id_)
                    res[id_] = r
            if name.startswith("a"):
                time.sleep(TIMEOUT + WAIT_PAST_TIMEOUT)
                for id_ in ids:
                    res[id_]["fire"] = st.fire(id_)
        finally:
            st.close()
        eff, aud, app = st.logs()
        keep(out, st, res)
        rc = reconcile.reconcile(eff, aud, app)
        kind = "unapproved" if name.startswith("e") else "unaudited"
        flagged = sorted(x["id"] for x in rc[kind])
        fires = sorted(e["id"] for e in eff) == ids and flagged == ids and not rc["ok"]
        fired[name] = {"config": st.config, "executed": sorted(e["id"] for e in eff), "flagged_" + kind: flagged,
                       "fires": fires}
    R.raw["controls"] = fired
    for name, f in fired.items():
        R.check("H6 CONTROL %s fires: all 3 operations execute and reconciliation flags each" % name,
                {"executed": 3, "flagged": 3}, {k: v for k, v in f.items() if k != "config"}, f["fires"])


H = {"H1": h1, "H2": h2, "H3": h3, "H4": h4, "H5": h5, "H6": h6}


# ---------------------------------------------------------------- receipt
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def git(*args):
    r = subprocess.run(["git", "-C", str(REPO)] + list(args), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       universal_newlines=True)
    return r.stdout.strip() if r.returncode == 0 else "ERROR: " + r.stderr.strip()


def tracked_files():
    return sorted(HERE.glob("*.py")) + [HERE / "README.md", PREREG]


def calibration():
    txt = PREREG.read_text() if PREREG.exists() else ""
    st = re.search(r"^CALIBRATION-STATUS: (\w+)\s*$", txt, re.M)
    vals = {k: float(v) for k, v in re.findall(r"^((?:TAU|L)_\w+) = ([0-9.]+)\s*$", txt, re.M)}
    return {"status": st.group(1) if st else None, "prereg_values": vals,
            "harness_values": {"TAU_X": TAU_X, "L_USE": L_USE}}


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    models = ["ControlStack/Scenarios/SC25Audit.lean", "ControlStack/Scenarios/SC25Content.lean"]
    return {
        "prereg_id": PREREG_ID, "kind": args.kind, "argv": sys.argv,
        "git_commit": git("rev-parse", "HEAD"), "git_branch": git("rev-parse", "--abbrev-ref", "HEAD"),
        "git_status_harness_and_prereg": git("status", "--porcelain", "--untracked-files=all", "--", *rel),
        "git_dirty_any": bool(git("status", "--porcelain")),
        "sha256": {str(p.relative_to(REPO)): sha(p) for p in tracked_files() if p.exists()},
        "model_sha256": {m: sha(REPO / m) for m in models},
        "calibration": calibration(),
        "uname_r": platform.release(), "uname_a": " ".join(platform.uname()), "python": sys.version,
        "python_executable": sys.executable, "nproc": os.cpu_count(), "uid": os.getuid(),
        "clock": "time.monotonic_ns (CLOCK_MONOTONIC); principal, executor and client stamps on one host",
        "constants": {k: globals()[k] for k in ("TIMEOUT", "WAIT_PAST_TIMEOUT", "H4_OPS", "THREADS", "USEFUL_FRAC",
                                                 "H5_PRE", "H5_POST", "LIFETIME", "RPC_TIMEOUT", "WALL_LIMIT", "TAU_X",
                                                 "L_USE", "H6_CONFIGS")},
    }


def preflight(args, m):
    problems = []
    if sys.version_info < (3, 9):
        problems.append("python >= 3.9 required")
    if not sys.platform.startswith("linux"):
        problems.append("linux required")
    stale = proc_scan("/var/tmp/sc25-run-")
    if stale:
        problems.append("processes of an earlier sc25 run still alive: %s" % [e["pid"] for e in stale])
    if args.kind == "evidence":
        if m["git_status_harness_and_prereg"]:
            problems.append("evidence run needs committed, unmodified harness and prereg files")
        c = m["calibration"]
        if c["status"] != "FIXED":
            problems.append("prereg calibration status is %s, not FIXED (prereg §3.0)" % c["status"])
        for k, v in c["harness_values"].items():
            if c["prereg_values"].get(k) != float(v):
                problems.append("harness %s %s != prereg %s" % (k, v, c["prereg_values"].get(k)))
    return problems


def summary_md(m, verdicts, results):
    lines = ["# SC-25 audit-before-execute queue (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- calibration: %s, TAU_X = %s s, L_USE = %s s" % (m["calibration"]["status"], TAU_X, L_USE),
             "- kernel: `%s`, python `%s`" % (m["uname_r"], m["python"].split()[0]),
             "- started %s, finished %s, wall %.1f s" % (m["started"], m["finished"], m["wall_s"]),
             "- overall: **%s**" % verdicts["overall"], "",
             "| hypothesis | kind | reps passed | verdict |", "|---|---|---|---|"]
    for h in HYPS:
        if h in verdicts["per_hypothesis"]:
            v = verdicts["per_hypothesis"][h]
            lines.append("| %s | %s | %d/%d | %s |" % (h, "NEGATIVE_CONTROL" if h in CONTROLS else "claim",
                                                     v["passed"], v["reps"], v["verdict"]))
    lines += ["", "## Key measurements per repetition", ""]
    for r in results:
        raw, s = r["raw"], ""
        if r["hyp"] == "H3":
            s = "max expiry lateness %s s" % (max(raw.get("expiry_lateness_s", {}).values() or [None]))
        elif r["hyp"] == "H4":
            s = "latency ms %s, executed %s" % (raw.get("latency_ms"), raw.get("executed"))
        elif r["hyp"] == "H5":
            s = "executed before halt %s, after %s" % (raw.get("executed_before"), raw.get("executed_after"))
        elif r["hyp"] == "H6":
            s = "controls fired: %s" % {k: v["fires"] for k, v in raw.get("controls", {}).items()}
        else:
            s = "effects %s" % (raw.get("reconcile", {}).get("reconciliation", {}).get("effects"))
        lines.append("- %s rep %d: %s" % (r["hyp"], r["rep"], s))
    lines += ["", "## Failed checks", ""]
    bad = [(r["hyp"], r["rep"], c) for r in results for c in r["checks"] if not c["pass"]]
    errs = [(r["hyp"], r["rep"], r["error"]) for r in results if r["error"]]
    for h, rp, c in bad:
        lines.append("- %s rep %d: %s — expected %s, observed %s" % (h, rp, c["name"], json.dumps(c["expected"]),
                                                                   json.dumps(c["observed"], default=str)[:400]))
    for h, rp, e in errs:
        lines.append("- %s rep %d: ERROR %s" % (h, rp, e.splitlines()[-1] if e else e))
    if not bad and not errs:
        lines.append("none")
    return "\n".join(lines) + "\n"


class WallLimit(Exception):
    pass


def main():
    ap = argparse.ArgumentParser(description="SC-25 audit-before-execute queue check (unprivileged).")
    ap.add_argument("--out", required=True, help="receipt directory (must not exist)")
    ap.add_argument("--kind", choices=["dry", "evidence"], required=True)
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--only", default=",".join(HYPS), help="comma list of hypotheses (dry runs only)")
    args = ap.parse_args()
    if os.geteuid() == 0:
        sys.exit("refusing to run as root: this harness is unprivileged by design")
    hyps = [h for h in args.only.split(",") if h]
    if any(h not in HYPS for h in hyps):
        sys.exit("unknown hypothesis in --only")
    if args.kind == "evidence" and (hyps != HYPS or args.reps != 5):
        sys.exit("evidence runs use all hypotheses and --reps 5 (prereg §4)")
    out = Path(args.out)
    if out.exists():
        sys.exit("refusing to overwrite existing --out %s" % out)
    if not out.parent.is_dir():
        sys.exit("parent of --out does not exist: %s" % out.parent)
    m = meta(args)
    problems = preflight(args, m)
    if args.kind == "evidence" and problems:
        sys.exit("refusing evidence run: " + "; ".join(problems))
    out.mkdir()
    (out / "logs").mkdir()
    m["started"] = datetime.datetime.utcnow().isoformat() + "Z"
    m["loadavg_start"] = os.getloadavg()
    t_start = time.monotonic()
    results, infra, aborted, ctx, residue = [], None, None, None, None
    if problems:
        infra = problems
    else:
        def on_alarm(signum, frame):
            raise WallLimit("wall limit %d s reached" % WALL_LIMIT)
        signal.signal(signal.SIGALRM, on_alarm)
        signal.alarm(WALL_LIMIT)
        try:
            ctx = Ctx()
            for rep in range(1, args.reps + 1):
                for h in hyps:
                    R = Rec(h, rep)
                    t = time.monotonic()
                    try:
                        H[h](ctx, out, rep, R)
                    except WallLimit:
                        R.error = traceback.format_exc()
                        results.append(R.as_dict())
                        raise
                    except Exception:
                        R.error = traceback.format_exc()
                    R.raw["elapsed_s"] = round(time.monotonic() - t, 3)
                    left = proc_scan(str(ctx.work))
                    R.raw["after"] = {"left_procs": left, "loadavg": os.getloadavg()}
                    results.append(R.as_dict())
                    print("%s rep %d: %s (%.1fs)" % (h, rep, "PASS" if R.passed() else "FAIL", R.raw["elapsed_s"]),
                          flush=True)
                    if left:
                        aborted = "residue after %s rep %d: %s" % (h, rep, left)
                        raise RuntimeError(aborted)
        except BaseException:
            aborted = aborted or traceback.format_exc()
        finally:
            signal.alarm(0)
            if ctx is not None:
                for f in sorted(ctx.logs.iterdir()):
                    shutil.copy2(str(f), str(out / "logs" / f.name))
                residue = proc_scan(str(ctx.work))
                for e in residue:
                    try:
                        os.kill(e["pid"], signal.SIGKILL)
                    except OSError:
                        pass
                shutil.rmtree(str(ctx.work), ignore_errors=True)
    m["finished"] = datetime.datetime.utcnow().isoformat() + "Z"
    m["wall_s"] = round(time.monotonic() - t_start, 2)
    m["loadavg_end"] = os.getloadavg()
    cleanup = {"residue_killed": residue, "workdir_removed": ctx is None or not ctx.work.exists()}
    per = {}
    for h in hyps:
        rs = [r for r in results if r["hyp"] == h]
        n_ok = sum(r["pass"] for r in rs)
        per[h] = {"reps": args.reps, "ran": len(rs), "passed": n_ok, "negative_control": h in CONTROLS,
                  "verdict": "NOT-RUN" if infra else "PASS" if len(rs) == args.reps and n_ok == args.reps else "FAIL"}
    verdicts = {"prereg_id": PREREG_ID, "kind": args.kind, "infra_error": infra, "aborted": aborted,
                "cleanup_ok": not residue and cleanup["workdir_removed"], "per_hypothesis": per,
                "calibration": m["calibration"]}
    verdicts["overall"] = ("INFRA-ERROR" if infra else
                           "PASS" if not aborted and verdicts["cleanup_ok"] and all(
                               v["verdict"] == "PASS" for v in per.values()) else "FAIL")
    dump = lambda name, obj: (out / name).write_text(json.dumps(obj, indent=1, sort_keys=True, default=str) + "\n")
    dump("meta.json", m)
    dump("verdicts.json", verdicts)
    dump("cleanup.json", cleanup)
    with open(str(out / "results.jsonl"), "w") as fh:
        for r in results:
            fh.write(json.dumps(r, sort_keys=True, default=str) + "\n")
    (out / "summary.md").write_text(summary_md(m, verdicts, results))
    print(json.dumps({"overall": verdicts["overall"], "per_hypothesis": per, "aborted": aborted, "infra": infra},
                     indent=1, default=str))
    return 0 if verdicts["overall"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
