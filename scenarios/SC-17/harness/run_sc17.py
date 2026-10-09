#!/usr/bin/env python3
"""SC-17 drift reconcile (unprivileged). Preregistration: prereg/SC17-DRIFT-RECONCILE.md (PREREG-SC17-DRIFT-v1).

Defensive reference test on one Linux host. The desired grant set is owned by an apply gate: a diff applies only if
a separate reviewer (not the author) approved exactly that diff and the RESULTING state satisfies the ceiling (no
subject may hold both read:secrets and exec:prod). The live grant set is served by a "cluster" process. This runner
performs benign out-of-band mutations (adds a grant straight to the live set) at d per tick, and a reconciler process
reverts drift every W ticks. Each hypothesis is repeated --reps times on fresh processes:

  H1 drift is bounded: at every instant (cluster mutation log) and every sample, out-of-band live grants <= d*W +
     TAU_N, and every out-of-band grant lives <= W ticks + TAU_L      (drift_bounded, drift_lifetime, live_eq;
                                                                        applies revert drift: no_drift_detection_breaks)
  H2 the ceiling is checked on the resulting state: two individually acceptable diffs that compose into the forbidden
     pair are refused                                      (sc17_safe; deployed half of text_ceiling_composition_breaks)
  H3 approve-then-amend is refused; only the reviewer approves; no double apply
                                                                  (deployed half of approve_then_amend_breaks)
  H4 usefulness: honest applies succeed within L_APPLY and the live state equals the desired state after each
  H5 NEGATIVE_CONTROL: (a) reconciler disabled -> out-of-band lifetime grows with run length
     (no_schedule_unbounded_lifetime); (b) text-only ceiling -> the composed escalation is applied and the
     reconciliation flags it (text_ceiling_composition_breaks)

Receipts go to --out, which must not exist. No root, no accounts, no network: Unix sockets in a fresh
/var/tmp/sc17-run-* directory, removed afterwards. Python 3.9 compatible (system interpreter).
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
PREREG = REPO / "prereg" / "SC17-DRIFT-RECONCILE.md"
PREREG_ID = "PREREG-SC17-DRIFT-v1"
HYPS = ["H1", "H2", "H3", "H4", "H5"]
CONTROLS = {"H5"}

# Preregistered constants (prereg §2-§3). Changing any of them needs a new prereg ID.
TICK = 0.05                 # s per tick
D = 2                       # out-of-band mutations per tick (the attacker-capability premise, here the injector rate)
W = 4                       # reconcile period in ticks
DRIFT_S = 3.0               # s of out-of-band injection (H1)
APPLY_AT = (1.0, 2.0)       # s into the H1 injection: honest applies during drift
SETTLE = W * TICK + 0.3     # s after injection stops, before the logs are read (H1)
SAMPLE = 0.01               # s between samples of the live state
CTRL_DRIFT_S = 2.0          # s of injection with the reconciler disabled (H5a)
CHECKPOINTS = (0.5, 1.0, 1.5, 2.0)
H4_APPLIES = 20
INIT = [["svc-web", "read", "config"], ["svc-db", "read", "secrets"]]
LIFETIME = 30.0
READY_TIMEOUT = 10.0
WALL_LIMIT = 115
# Tolerances fixed from dry-run calibration (prereg §3.0).
TAU_N = 3                   # grants (calibrated)
TAU_L = 0.05                # s (calibrated)
L_APPLY = 0.15              # s (calibrated)

DA = {"adds": [["alice", "read", "secrets"]], "dels": []}
DB = {"adds": [["alice", "exec", "prod"]], "dels": []}
DC = {"adds": [["bob", "exec", "prod"]], "dels": []}


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
        self.work = Path(tempfile.mkdtemp(prefix="sc17-run-", dir="/var/tmp"))
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
    """live processes (not this runner or its ancestors) with a command-line ARGUMENT that starts with marker"""
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


class Conn:
    def __init__(self, path, timeout=5.0):
        self.s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.s.settimeout(timeout)
        self.s.connect(str(path))
        self.f = self.s.makefile("rwb", buffering=0)

    def call(self, obj):
        self.f.write((json.dumps(obj) + "\n").encode())
        line = self.f.readline()
        if not line:
            raise ConnectionError("no reply")
        return json.loads(line)

    def close(self):
        self.s.close()


def rpc(path, obj):
    c = Conn(path)
    try:
        return c.call(obj)
    finally:
        c.close()


class Stack:
    """cluster + reviewer + apply gate (+ reconciler)"""

    def __init__(self, ctx, tag, reconciler=True, gate_flags=()):
        self.ctx, self.tag = ctx, tag
        d = self.d = ctx.work / tag
        d.mkdir()
        self.procs = []
        (d / "init.json").write_text(json.dumps(INIT))
        self.cluster_log, self.gate_log = d / "cluster.jsonl", d / "gate.jsonl"
        self.rev_log, self.rec_log = d / "reviewer.jsonl", d / "reconciler.jsonl"
        read_tag(self._spawn("cluster", ctx.script("cluster.py", "--dir", d, "--init", d / "init.json", "--log",
                                                   self.cluster_log, "--lifetime", LIFETIME)), "READY")
        rv = self._spawn("reviewer", ctx.script("reviewer.py", "--sock", d / "reviewer-svc.sock", "--gate",
                                                d / "reviewer.sock", "--log", self.rev_log, "--lifetime", LIFETIME))
        rpid = read_tag(rv, "READY")["pid"]
        g = self._spawn("gate", ctx.script("gate.py", "--dir", d, "--init", d / "init.json", "--cluster-ctl",
                                           d / "ctl.sock", "--reviewer-pid", rpid, "--log", self.gate_log,
                                           "--lifetime", LIFETIME, *gate_flags))
        self.config = read_tag(g, "READY")["config"]
        self.config["reconciler"] = reconciler
        if reconciler:
            read_tag(self._spawn("reconciler", ctx.script("reconciler.py", "--gate", d / "read.sock", "--cluster-ctl",
                                                          d / "ctl.sock", "--period", W * TICK, "--log", self.rec_log,
                                                          "--lifetime", LIFETIME)), "READY")
        self.replies = []

    def _spawn(self, name, argv):
        with open(str(self.ctx.logs / ("%s-%s.stderr" % (self.tag, name))), "wb") as se:
            p = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=se, close_fds=True)
        self.procs.append(p)
        return p

    def _r(self, sock, obj):
        r = rpc(self.d / sock, obj)
        self.replies.append({"sock": sock, "req": obj, "reply": r, "t": time.monotonic_ns()})
        return r

    def propose(self, id_, diff):
        return self._r("agent.sock", {"op": "propose", "id": id_, "diff": diff})

    def amend(self, id_, diff):
        return self._r("agent.sock", {"op": "amend", "id": id_, "diff": diff})

    def apply(self, id_):
        return self._r("agent.sock", {"op": "apply", "id": id_})

    def review(self, id_):
        return self._r("reviewer-svc.sock", {"op": "review", "id": id_})

    def agent_approves(self, id_, diff):
        return self._r("reviewer.sock", {"op": "approve", "id": id_, "diff": diff})

    def desired(self):
        return rpc(self.d / "read.sock", {"op": "get_desired"})

    def live(self):
        return rpc(self.d / "ctl.sock", {"op": "get"})

    def honest(self, id_, diff):
        t0 = time.monotonic()
        p, r, a = self.propose(id_, diff), self.review(id_), self.apply(id_)
        return {"propose": p, "review": r, "apply": a, "lat_s": time.monotonic() - t0}

    def events(self):
        return reconcile.load_jsonl(str(self.cluster_log))

    def audit(self):
        return reconcile.audit_applies(reconcile.load_committed(str(self.gate_log)),
                                       reconcile.load_committed(str(self.rev_log)), self.events())

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


class Injector(threading.Thread):
    """benign out-of-band mutations: D new grants at the start of every tick, for `seconds`"""

    def __init__(self, st, seconds):
        super().__init__(daemon=True)
        self.st, self.seconds, self.n, self.t0, self.err = st, seconds, 0, None, None

    def run(self):
        c = Conn(self.st.d / "oob.sock")
        try:
            self.t0 = time.monotonic_ns()
            for k in range(int(round(self.seconds / TICK))):
                due = self.t0 + int(k * TICK * 1e9)
                time.sleep(max(0.0, (due - time.monotonic_ns()) / 1e9))
                for _ in range(D):
                    c.call({"op": "add", "grant": ["oob-%d" % self.n, "admin", "cluster-%d" % k]})
                    self.n += 1
        except Exception as e:
            self.err = repr(e)
        finally:
            c.close()


class Sampler(threading.Thread):
    def __init__(self, st):
        super().__init__(daemon=True)
        self.st, self.stop, self.samples = st, threading.Event(), []

    def run(self):
        c = Conn(self.st.d / "ctl.sock")
        try:
            while not self.stop.is_set():
                r = c.call({"op": "get"})
                live, base = {tuple(g) for g in r["live"]}, {tuple(g) for g in r["base"]}
                self.samples.append((r["t"], sum(1 for g in live if reconcile.is_oob(g)), len(live - base)))
                self.stop.wait(SAMPLE)
        finally:
            c.close()


def keep(out, st, extra=None):
    d = out / "logs" / st.tag
    d.mkdir(parents=True)
    for f in (st.cluster_log, st.gate_log, st.rev_log, st.rec_log, st.d / "init.json"):
        if f.exists():
            shutil.copy2(str(f), str(d / f.name))
    with open(str(d / "client.json"), "w") as fh:
        json.dump({"replies": st.replies, "extra": extra}, fh, default=str)


def check_audit(R, au):
    R.raw["audit"] = au
    R.check("every apply: reviewer record of exactly the applied diff by a non-author before it; resulting state "
            "within the ceiling; live = desired right after the push; no live state over the ceiling (sc17_safe)",
            {"defects": [], "live_states_over_ceiling": []},
            {"applies": au["applies"], "defects": au["defects"], "live_states_over_ceiling":
             au["live_states_over_ceiling"][:5]}, au["ok"])


# ---------------------------------------------------------------- hypotheses
def h1(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h1" % rep)
    applied = []
    try:
        sm, inj = Sampler(st), Injector(st, DRIFT_S)
        sm.start()
        inj.start()
        t_start = time.monotonic()
        for i, at in enumerate(APPLY_AT):
            time.sleep(max(0.0, t_start + at - time.monotonic()))
            applied.append(st.honest("h1-%d" % i, {"adds": [["svc-%d" % i, "read", "config"]], "dels": []}))
        inj.join(timeout=DRIFT_S + 5)
        time.sleep(SETTLE)
        sm.stop.set()
        sm.join(timeout=2)
        t_end = time.monotonic_ns()
    finally:
        st.close()
    keep(out, st, {"samples": sm.samples})
    ev = st.events()
    dr = reconcile.drift(ev, t_end=t_end)
    au = reconcile.audit_applies(reconcile.load_committed(str(st.gate_log)), reconcile.load_committed(str(st.rev_log)),
                                 ev)
    recs = reconcile.load_jsonl(str(st.rec_log))
    bn, bl = D * W + TAU_N, W * TICK + TAU_L
    s_oob = max((s[1] for s in sm.samples), default=0)
    s_base = max((s[2] for s in sm.samples), default=0)
    R.raw.update(drift=dr, sampled={"n": len(sm.samples), "max_oob": s_oob, "max_live_minus_base": s_base},
                 injected=inj.n, injector_error=inj.err, reconciler_runs=len(recs),
                 reconciler_max_late_s=max((r.get("late_s", 0) for r in recs), default=None),
                 applies=[a["apply"] for a in applied])
    nt = int(round(DRIFT_S / TICK)) * D
    R.check("non-vacuity: every out-of-band grant was injected and became live; drift reached at least d",
            {"injected": nt, "born": nt, "max_oob_live": ">= %d" % D},
            {"injected": inj.n, "born": dr["n_born"], "max_oob_live": dr["max_oob_live"], "error": inj.err},
            inj.n == nt and dr["n_born"] == nt and dr["max_oob_live"] >= D)
    R.check("H1 count: out-of-band live grants <= d*W + TAU_N at every instant of the cluster log and every sample "
            "(drift_bounded)", "<= %d" % bn,
            {"log_max_oob": dr["max_oob_live"], "log_max_live_minus_base": dr["max_live_minus_base"],
             "sampled_max_oob": s_oob, "sampled_max_live_minus_base": s_base},
            max(dr["max_oob_live"], dr["max_live_minus_base"], s_oob, s_base) <= bn)
    R.check("H1 lifetime: every out-of-band grant was reverted, each within W ticks + TAU_L (drift_lifetime)",
            {"alive_at_end": 0, "max_lifetime_s": "<= %.3f" % bl},
            {"alive_at_end": len(dr["alive_at_end"]), "max_lifetime_s": round(dr["max_lifetime_s"], 4)},
            not dr["alive_at_end"] and dr["max_lifetime_s"] <= bl)
    R.check("honest applies during drift succeed", [True] * len(APPLY_AT), [bool(a["apply"].get("ok")) for a in applied],
            all(a["apply"].get("ok") for a in applied))
    check_audit(R, au)
    mt = reconcile.mutation_selftest(reconcile.load_committed(str(st.gate_log)),
                                     reconcile.load_committed(str(st.rev_log)), ev, bl)
    R.check("reconciliation sensitivity: each injected defect in a copy of the stored logs is flagged", True, mt,
            all(mt.values()) and len(mt) == 3)


def h2(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h2" % rep)
    try:
        ra, rb, rc = st.honest("A", DA), st.honest("B", DB), st.honest("C", DC)
        final = st.desired()
    finally:
        st.close()
    keep(out, st)
    R.raw.update(apply_A=ra["apply"], apply_B=rb["apply"], apply_C=rc["apply"], final_desired=final["desired"])
    R.check("diff A (alice read:secrets) and diff C (bob exec:prod) apply", [True, True],
            [bool(ra["apply"].get("ok")), bool(rc["apply"].get("ok"))], ra["apply"].get("ok") and rc["apply"].get("ok"))
    R.check("H2: diff B (alice exec:prod), acceptable on its own, is refused because the RESULTING state would give "
            "alice the forbidden pair (text_ceiling_composition_breaks, deployed half)", "ceiling refusal",
            rb["apply"].get("error"), not rb["apply"].get("ok") and "ceiling" in str(rb["apply"].get("error")))
    R.check("final desired state within the ceiling", [], reconcile.forbidden(final["desired"]),
            not reconcile.forbidden(final["desired"]))
    check_audit(R, st.audit())


def h3(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h3" % rep)
    X = {"adds": [["carol", "read", "config"]], "dels": []}
    Y = {"adds": [["carol", "write", "config"]], "dels": []}
    try:
        res = {"propose": st.propose("P", X), "review": st.review("P"), "amend": st.amend("P", Y)}
        res["apply_after_amend"] = st.apply("P")
        res["agent_self_approval"] = st.agent_approves("P", Y)
        res["apply_after_self_approval"] = st.apply("P")
        res["re_review"] = st.review("P")
        res["apply"] = st.apply("P")
        res["apply_again"] = st.apply("P")
        gate = reconcile.load_committed(str(st.gate_log))
    finally:
        st.close()
    keep(out, st)
    R.raw["steps"] = res
    R.check("H3: apply after approve-then-amend refused (approve_then_amend_breaks, deployed half)",
            "no approval of exactly the current diff", res["apply_after_amend"].get("error"),
            res["apply_after_amend"].get("error") == "no approval of exactly the current diff")
    R.check("the agent cannot approve (only the registered reviewer; reviewer != author)",
            {"approve": "not the reviewer", "apply": "no approval of exactly the current diff"},
            {"approve": res["agent_self_approval"].get("error"),
             "apply": res["apply_after_self_approval"].get("error")},
            res["agent_self_approval"].get("error") == "not the reviewer" and
            res["apply_after_self_approval"].get("error") == "no approval of exactly the current diff")
    R.check("after the reviewer approves the amended diff it applies, exactly once", {"apply": True,
                                                                                      "again": "already applied",
                                                                                      "applied_diff": Y},
            {"apply": res["apply"].get("ok"), "again": res["apply_again"].get("error"),
             "applied_diff": [g["diff"] for g in gate]},
            res["apply"].get("ok") and res["apply_again"].get("error") == "already applied" and
            [g["diff"] for g in gate] == [Y])
    check_audit(R, st.audit())


def h4(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h4" % rep)
    res = []
    try:
        for i in range(H4_APPLIES):
            r = st.honest("U-%d" % i, {"adds": [["svc-%d" % i, "read", "metrics"]], "dels": []})
            d, l = st.desired(), st.live()
            r["live_eq_desired"] = sorted(map(tuple, d["desired"])) == sorted(map(tuple, l["live"]))
            res.append(r)
    finally:
        st.close()
    keep(out, st)
    ls = sorted(r["lat_s"] for r in res)
    okn = sum(1 for r in res if r["apply"].get("ok"))
    eq = sum(1 for r in res if r["live_eq_desired"])
    R.raw.update(latency_ms={"p50": round(ls[len(ls) // 2] * 1e3, 2), "max": round(ls[-1] * 1e3, 2)},
                 max_latency_s=ls[-1])
    R.check("H4: all %d honest applies succeed within L_APPLY = %.2f s and live = desired after each" %
            (H4_APPLIES, L_APPLY), {"ok": H4_APPLIES, "live_eq_desired": H4_APPLIES, "max_s": "<= %.2f" % L_APPLY},
            {"ok": okn, "live_eq_desired": eq, "latency_ms": R.raw["latency_ms"]},
            okn == eq == H4_APPLIES and ls[-1] <= L_APPLY)
    check_audit(R, st.audit())


def h5(ctx, out, rep, R):
    # (a) reconciler disabled
    st = Stack(ctx, "r%d-h5a" % rep, reconciler=False)
    try:
        inj = Injector(st, CTRL_DRIFT_S)
        inj.start()
        inj.join(timeout=CTRL_DRIFT_S + 5)
        t_end = time.monotonic_ns()
    finally:
        st.close()
    keep(out, st)
    dr = reconcile.drift(st.events(), t_end=t_end, checkpoints=CHECKPOINTS, t0=inj.t0)
    series = [c["oob_live"] for c in dr["checkpoints"]]
    bn, bl = D * W + TAU_N, W * TICK + TAU_L
    fa = (dr["n_died"] == 0 and len(dr["alive_at_end"]) == inj.n and dr["max_age_alive_s"] > bl and
          all(b > a for a, b in zip(series, series[1:])) and series[-1] > bn)
    R.raw["a"] = {"config": st.config, "series": series, "alive": len(dr["alive_at_end"]),
                  "max_age_alive_s": round(dr["max_age_alive_s"], 3), "died": dr["n_died"]}
    R.check("H5a CONTROL fires: without the reconciler no out-of-band grant is reverted, the oldest outlives W ticks "
            "+ TAU_L by far, and drift keeps growing past d*W + TAU_N (no_schedule_unbounded_lifetime)",
            {"died": 0, "max_age_s": "> %.2f" % bl, "series": "strictly increasing, last > %d" % bn},
            {k: v for k, v in R.raw["a"].items() if k != "config"}, fa)
    # (b) text-only ceiling
    st = Stack(ctx, "r%d-h5b" % rep, gate_flags=["--text-ceiling"])
    try:
        ra, rb = st.honest("A", DA), st.honest("B", DB)
    finally:
        st.close()
    keep(out, st)
    au = st.audit()
    flagged_b = [d for d in au["defects"] if d["id"] == "B" and any("ceiling" in w for w in d["why"])]
    fb = bool(ra["apply"].get("ok") and rb["apply"].get("ok") and flagged_b and au["live_states_over_ceiling"])
    R.raw["b"] = {"config": st.config, "apply_A": ra["apply"], "apply_B": rb["apply"], "audit": au}
    R.check("H5b CONTROL fires: the text-only ceiling applies the composed escalation and the reconciliation flags "
            "it (text_ceiling_composition_breaks)", {"B applied": True, "flagged": True},
            {"B applied": bool(rb["apply"].get("ok")), "flagged": [d["why"] for d in flagged_b],
             "live_states_over_ceiling": len(au["live_states_over_ceiling"])}, fb)


H = {"H1": h1, "H2": h2, "H3": h3, "H4": h4, "H5": h5}


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
            "harness_values": {"TAU_N": TAU_N, "TAU_L": TAU_L, "L_APPLY": L_APPLY}}


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    models = ["ControlStack/Scenarios/SC17Infra.lean", "ControlStack/Scenarios/SC17Drift.lean"]
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
        "clock": "time.monotonic_ns (CLOCK_MONOTONIC); cluster, gate, reviewer and runner stamps on one host",
        "constants": {k: globals()[k] for k in ("TICK", "D", "W", "DRIFT_S", "APPLY_AT", "SETTLE", "SAMPLE",
                                                 "CTRL_DRIFT_S", "CHECKPOINTS", "H4_APPLIES", "INIT", "LIFETIME",
                                                 "WALL_LIMIT", "TAU_N", "TAU_L", "L_APPLY")},
    }


def preflight(args, m):
    problems = []
    if sys.version_info < (3, 9):
        problems.append("python >= 3.9 required")
    if not sys.platform.startswith("linux"):
        problems.append("linux required")
    stale = proc_scan("/var/tmp/sc17-run-")
    if stale:
        problems.append("processes of an earlier sc17 run still alive: %s" % [e["pid"] for e in stale])
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
    lines = ["# SC-17 drift reconcile (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- calibration: %s, TAU_N = %s, TAU_L = %s s, L_APPLY = %s s" % (m["calibration"]["status"], TAU_N, TAU_L, L_APPLY),
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
        if r["hyp"] == "H1" and raw.get("drift"):
            dr = raw["drift"]
            s = "max oob live %s (sampled %s), max lifetime %.3f s, reconciler max late %s s" % (
                dr["max_oob_live"], raw["sampled"]["max_oob"], dr["max_lifetime_s"], raw.get("reconciler_max_late_s"))
        elif r["hyp"] == "H4":
            s = "latency ms %s" % raw.get("latency_ms")
        elif r["hyp"] == "H5":
            s = "a: %s; b: B applied %s" % ({k: v for k, v in raw.get("a", {}).items() if k != "config"},
                                           raw.get("b", {}).get("apply_B", {}).get("ok"))
        else:
            s = "applies %s" % raw.get("audit", {}).get("applies")
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
    ap = argparse.ArgumentParser(description="SC-17 drift reconcile check (unprivileged).")
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
