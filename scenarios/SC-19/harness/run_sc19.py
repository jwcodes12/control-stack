#!/usr/bin/env python3
"""SC-19 two-phase destructive operations (unprivileged). Preregistration: prereg/SC19-TWO-PHASE.md
(PREREG-SC19-TWOPHASE-v1).

Defensive reference test on one Linux host. A disposable SQLite "production" DB holds objects per target, each target
with a version bumped by every write. A snapshot service copies the DB and records per-target versions; a separate
trusted verifier restores each snapshot into a scratch DB and checks counts and hashes before marking it verified.
Destructive operations (delete all rows of a target) go prepare -> approve (a separate approver, never the author,
approves the exact operation digest) -> commit, where the commit re-checks inside one IMMEDIATE transaction: a
verified snapshot exists at the CURRENT version of the target, and the affected count recomputed at commit is <= R.
A benign writer process adds rows concurrently. Each hypothesis is repeated --reps times on fresh processes:

  H1 every committed destructive op had a verified snapshot of exactly the destroyed version and rows, affected <= R,
     and a non-author approval of its exact digest (reconciliation from the verifier/approver logs + DB history);
     missing approval, self-approval, an unverified snapshot and an oversize target are refused
                                                                    (sc19_safe, sc19_safe_authenticated)
  H2 a write after the snapshot: the commit is refused until a fresh snapshot is taken and verified
                                                                    (deployed half of stale_snapshot_breaks)
  H3 a concurrent write grows the target beyond R between prepare and commit: refused
                                                                    (deployed half of blast_radius_race_breaks)
  H4 restore drill: after a committed delete, the verified snapshot restores the destroyed rows byte-exact
  H5 usefulness: honest destructive changes succeed within L_OP while a background writer runs
  H6 NEGATIVE_CONTROL: stale-snapshot, unverified-snapshot and prepare-time-count configurations commit and the
     reconciliation flags them  (stale_snapshot_breaks, unverified_snapshot_breaks, blast_radius_race_breaks)

Receipts go to --out, which must not exist. No root, no accounts, no network: Unix sockets and SQLite files in a
fresh /var/tmp/sc19-run-* directory, removed afterwards. Python 3.9 compatible (system interpreter, sqlite3).
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
import sqlite3
import subprocess
import sys
import tempfile
import time
import traceback
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
import dbutil  # noqa: E402
import reconcile  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "SC19-TWO-PHASE.md"
PREREG_ID = "PREREG-SC19-TWOPHASE-v1"
HYPS = ["H1", "H2", "H3", "H4", "H5", "H6"]
CONTROLS = {"H6"}

# Preregistered constants (prereg §2-§3). Changing any of them needs a new prereg ID.
R = 10                      # blast-radius cap: rows a destructive op may remove
H5_OPS = 20
BG_INTERVAL = 0.02          # s between background writes (H5)
LIFETIME = 30.0
READY_TIMEOUT = 10.0
WALL_LIMIT = 115
H6_CONFIGS = {"a_stale_snapshot": ["--stale-ok"], "b_unverified_snapshot": ["--unverified-ok"],
              "c_prepare_time_count": ["--prepare-count"]}
# Tolerance fixed from dry-run calibration (prereg §3.0).
L_OP = 0.70                 # s, H5: snapshot + verify + prepare + approve + commit (calibrated)


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
        self.work = Path(tempfile.mkdtemp(prefix="sc19-run-", dir="/var/tmp"))
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


def rpc(path, obj, timeout=15.0):
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
    """prod DB + snapshot service + verifier + approver + writer + gate"""

    def __init__(self, ctx, tag, targets, gate_flags=(), background=""):
        self.ctx, self.tag = ctx, tag
        d = self.d = ctx.work / tag
        d.mkdir()
        self.procs = []
        self.db = d / "prod.db"
        c = dbutil.connect(str(self.db))
        c.executescript(dbutil.SCHEMA)
        c.execute("BEGIN IMMEDIATE")
        for t, n in targets.items():
            dbutil.write_rows(c, t, n, kind="init")
        c.execute("COMMIT")
        c.close()
        self.gate_log, self.ver_log, self.app_log = d / "gate.jsonl", d / "verifier.jsonl", d / "approver.jsonl"
        self.snap_log, self.deleted = d / "snapshot.jsonl", d / "deleted.jsonl"
        lib = str(HERE)
        read_tag(self._spawn("snapshot", ctx.script("snapshot.py", "--lib", lib, "--db", self.db, "--store",
                                                    d / "snapstore", "--sock", d / "snapshot.sock", "--log",
                                                    self.snap_log, "--lifetime", LIFETIME)), "READY")
        read_tag(self._spawn("verifier", ctx.script("verifier.py", "--lib", lib, "--snapshot", d / "snapshot.sock",
                                                    "--scratch", d / "verifier-scratch", "--sock", d / "verifier.sock",
                                                    "--log", self.ver_log, "--lifetime", LIFETIME)), "READY")
        apid = read_tag(self._spawn("approver", ctx.script("approver.py", "--sock", d / "approver-svc.sock", "--gate",
                                                           d / "approver.sock", "--log", self.app_log, "--lifetime",
                                                           LIFETIME)), "READY")["pid"]
        read_tag(self._spawn("writer", ctx.script("writer.py", "--lib", lib, "--db", self.db, "--sock",
                                                  d / "writer.sock", "--log", d / "writer.jsonl", "--background",
                                                  background, "--interval", BG_INTERVAL, "--lifetime", LIFETIME)),
                 "READY")
        g = self._spawn("gate", ctx.script("gate.py", "--lib", lib, "--db", self.db, "--dir", d, "--verifier",
                                           d / "verifier.sock", "--snapshot", d / "snapshot.sock", "--approver-pid",
                                           apid, "--R", R, "--log", self.gate_log, "--deleted", self.deleted,
                                           "--lifetime", LIFETIME, *gate_flags))
        self.config = read_tag(g, "READY")["config"]
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

    def snapshot(self):
        return self._r("snapshot.sock", {"op": "snapshot"})["rec"]["snap_id"]

    def verify(self, sid):
        return self._r("verifier.sock", {"op": "verify", "snap_id": sid})

    def prepare(self, id_, t):
        return self._r("agent.sock", {"op": "prepare", "id": id_, "target": t, "kind": "delete_all"})

    def approve(self, id_):
        return self._r("approver-svc.sock", {"op": "approve", "id": id_})

    def agent_approve(self, id_, digest):
        return self._r("approver.sock", {"op": "approve", "id": id_, "digest": digest})

    def commit(self, id_, sid):
        return self._r("agent.sock", {"op": "commit", "id": id_, "snap_id": sid})

    def write(self, t, n):
        return self._r("writer.sock", {"op": "write", "target": t, "n": n})

    def honest(self, id_, t):
        t0 = time.monotonic()
        sid = self.snapshot()
        v = self.verify(sid)
        p = self.prepare(id_, t)
        a = self.approve(id_)
        c = self.commit(id_, sid)
        return {"snap": sid, "verify": v.get("ok"), "prepare": p, "approve": a, "commit": c,
                "lat_s": time.monotonic() - t0}

    def evidence(self):
        return (reconcile.load_committed(str(self.gate_log)), reconcile.load_committed(str(self.ver_log)),
                reconcile.load_committed(str(self.app_log)), reconcile.history(str(self.db)))

    def snap_file(self, sid):
        for r in reconcile.load_jsonl(str(self.snap_log)):
            if r["snap_id"] == sid:
                return r["file"]

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


def keep(out, st):
    d = out / "logs" / st.tag
    d.mkdir(parents=True)
    for f in (st.gate_log, st.ver_log, st.app_log, st.snap_log, st.deleted, st.d / "writer.jsonl"):
        if f.exists():
            shutil.copy2(str(f), str(d / f.name))
    with open(str(d / "db-history.json"), "w") as fh:
        json.dump(reconcile.history(str(st.db)), fh, indent=1)
    with open(str(d / "client.json"), "w") as fh:
        json.dump(st.replies, fh, default=str)


def check_reconcile(R_, rc, name="reconciliation"):
    R_.raw.setdefault("reconcile", {})[name] = rc
    R_.check("%s: every committed destructive op had a verified restore point of exactly the destroyed version and "
             "rows, affected <= R, and a non-author approval of its exact digest (sc19_safe)" % name,
             {"defects": []}, {"destroys": rc["destroys"], "defects": rc["defects"]}, rc["ok"])


# ---------------------------------------------------------------- hypotheses
def h1(ctx, out, rep, Rr):
    targets = {"t-%d" % i: 3 + i for i in range(6)}
    targets.update({"big": R + 5, "noappr": 4, "unver": 4, "selfappr": 4})
    st = Stack(ctx, "r%d-h1" % rep, targets)
    try:
        honest = [st.honest("op-%d" % i, "t-%d" % i) for i in range(6)]
        neg = {}
        sid = st.snapshot()
        st.verify(sid)
        st.prepare("op-big", "big")
        st.approve("op-big")
        neg["oversize target"] = st.commit("op-big", sid).get("error")
        sid = st.snapshot()
        st.verify(sid)
        st.prepare("op-noappr", "noappr")
        neg["no approval"] = st.commit("op-noappr", sid).get("error")
        sid = st.snapshot()
        st.prepare("op-unver", "unver")
        st.approve("op-unver")
        neg["unverified snapshot"] = st.commit("op-unver", sid).get("error")
        sid = st.snapshot()
        st.verify(sid)
        p = st.prepare("op-self", "selfappr")
        neg["agent approves its own op"] = st.agent_approve("op-self", p.get("digest")).get("error")
        neg["commit after self-approval attempt"] = st.commit("op-self", sid).get("error")
        ev = st.evidence()
    finally:
        st.close()
    keep(out, st)
    gates, verifs, apps, hist = ev
    Rr.raw.update(honest=[{k: h[k] for k in ("commit", "lat_s")} for h in honest], refusals=neg)
    Rr.check("the 6 honest destructive ops commit", [True] * 6, [bool(h["commit"].get("ok")) for h in honest],
             all(h["commit"].get("ok") for h in honest))
    exp = {"oversize target": "affected %d > R = %d" % (R + 5, R),
           "no approval": "no approval of exactly this operation by another principal",
           "unverified snapshot": "snapshot not verified",
           "agent approves its own op": "not the approver",
           "commit after self-approval attempt": "no approval of exactly this operation by another principal"}
    Rr.check("refused with the right reason: oversize, no approval, unverified snapshot, self-approval "
             "(sc19_safe_authenticated)", exp, neg, neg == exp)
    rc = reconcile.reconcile(gates, verifs, apps, hist, R)
    check_reconcile(Rr, rc)
    Rr.check("exactly the 6 honest ops appear as destroys", sorted("op-%d" % i for i in range(6)),
             sorted(g["id"] for g in gates), sorted(g["id"] for g in gates) == sorted("op-%d" % i for i in range(6)))
    mt = reconcile.mutation_selftest(gates, verifs, apps, hist, R)
    Rr.check("reconciliation sensitivity: each injected defect in a copy of the stored evidence is flagged", True, mt,
             all(mt.values()) and len(mt) == 5)


def h2(ctx, out, rep, Rr):
    st = Stack(ctx, "r%d-h2" % rep, {"w-%d" % i: 4 for i in range(3)})
    res = []
    try:
        for i in range(3):
            t, id_ = "w-%d" % i, "op-w%d" % i
            s1 = st.snapshot()
            st.verify(s1)
            st.prepare(id_, t)
            st.approve(id_)
            st.write(t, 2)
            first = st.commit(id_, s1)
            s2 = st.snapshot()
            st.verify(s2)
            second = st.commit(id_, s2)
            res.append({"first": first, "second": second})
        ev = st.evidence()
    finally:
        st.close()
    keep(out, st)
    Rr.raw["cases"] = res
    Rr.check("H2: commit with a snapshot older than a later write is refused (stale_snapshot_breaks, deployed half)",
             "snapshot is not at the current version", [r["first"].get("error") for r in res],
             all(not r["first"].get("ok") and "not at the current version" in str(r["first"].get("error"))
                 for r in res))
    Rr.check("after a fresh verified snapshot the op commits and destroys all 6 rows (4 + 2 written later)",
             [6, 6, 6], [r["second"].get("actual") for r in res], all(r["second"].get("actual") == 6 for r in res))
    check_reconcile(Rr, reconcile.reconcile(*ev, R))


def h3(ctx, out, rep, Rr):
    st = Stack(ctx, "r%d-h3" % rep, {"g-%d" % i: 8 for i in range(3)})
    res = []
    try:
        for i in range(3):
            t, id_ = "g-%d" % i, "op-g%d" % i
            p = st.prepare(id_, t)
            st.write(t, 5)
            s = st.snapshot()
            st.verify(s)
            st.approve(id_)
            res.append({"count_at_prepare": p.get("count"), "commit": st.commit(id_, s)})
        ev = st.evidence()
    finally:
        st.close()
    keep(out, st)
    Rr.raw["cases"] = res
    Rr.check("H3: prepared at 8 rows, grown to 13 > R by a concurrent write, refused at commit "
             "(blast_radius_race_breaks, deployed half)", "affected 13 > R = %d" % R,
             [(r["count_at_prepare"], r["commit"].get("error")) for r in res],
             all(r["count_at_prepare"] == 8 and r["commit"].get("error") == "affected 13 > R = %d" % R for r in res))
    check_reconcile(Rr, reconcile.reconcile(*ev, R))
    Rr.check("nothing destroyed", 0, len(ev[0]), not ev[0])


def h4(ctx, out, rep, Rr):
    st = Stack(ctx, "r%d-h4" % rep, {"d-%d" % i: 5 + i for i in range(3)})
    drills = []
    try:
        for i in range(3):
            h = st.honest("op-d%d" % i, "d-%d" % i)
            drills.append((h, "d-%d" % i, "op-d%d" % i))
        ev = st.evidence()
        deleted = reconcile.load_jsonl(str(st.deleted))
        res = []
        for h, t, id_ in drills:
            dr = reconcile.restore_drill(st.snap_file(h["snap"]), t, [r for r in deleted if r["op"] == id_])
            res.append(dict(dr, committed=bool(h["commit"].get("ok"))))
    finally:
        st.close()
    keep(out, st)
    Rr.raw["drills"] = res
    Rr.check("H4: every committed delete is recovered byte-exact from its verified snapshot",
             [{"committed": True, "byte_exact": True}] * 3,
             [{"committed": r["committed"], "byte_exact": r["byte_exact"], "rows": r["restored"]} for r in res],
             all(r["committed"] and r["byte_exact"] and r["restored"] == r["deleted"] > 0 for r in res))
    check_reconcile(Rr, reconcile.reconcile(*ev, R))


def h5(ctx, out, rep, Rr):
    tg = {"u-%d" % i: 5 for i in range(H5_OPS)}
    tg.update({"bg-%d" % i: 1 for i in range(4)})
    st = Stack(ctx, "r%d-h5" % rep, tg, background=",".join("bg-%d" % i for i in range(4)))
    try:
        res = [st.honest("op-u%d" % i, "u-%d" % i) for i in range(H5_OPS)]
        ev = st.evidence()
    finally:
        st.close()
    keep(out, st)
    ls = sorted(r["lat_s"] for r in res)
    okn = sum(1 for r in res if r["commit"].get("ok"))
    bg = sum(1 for h in ev[3] if h["target"].startswith("bg-") and h["kind"] == "write")
    Rr.raw.update(latency_ms={"p50": round(ls[len(ls) // 2] * 1e3, 2), "max": round(ls[-1] * 1e3, 2)},
                  max_latency_s=ls[-1], background_writes=bg)
    Rr.check("H5: all %d honest destructive changes commit within L_OP = %.2f s while the background writer runs" %
             (H5_OPS, L_OP), {"ok": H5_OPS, "max_s": "<= %.2f" % L_OP, "background_writes": "> 0"},
             {"ok": okn, "latency_ms": Rr.raw["latency_ms"], "background_writes": bg},
             okn == H5_OPS and ls[-1] <= L_OP and bg > 0)
    check_reconcile(Rr, reconcile.reconcile(*ev, R))


def h6(ctx, out, rep, Rr):
    fired = {}
    for name, flags in H6_CONFIGS.items():
        st = Stack(ctx, "r%d-h6%s" % (rep, name[0]), {"c-%d" % i: (8 if name.startswith("c") else 4) for i in range(2)},
                   gate_flags=flags)
        try:
            commits = []
            for i in range(2):
                t, id_ = "c-%d" % i, "op-c%d" % i
                if name.startswith("a"):
                    s = st.snapshot()
                    st.verify(s)
                    st.write(t, 2)
                    st.prepare(id_, t)
                    st.approve(id_)
                elif name.startswith("b"):
                    s = st.snapshot()
                    st.prepare(id_, t)
                    st.approve(id_)
                else:
                    st.prepare(id_, t)
                    st.write(t, 5)
                    s = st.snapshot()
                    st.verify(s)
                    st.approve(id_)
                commits.append(st.commit(id_, s))
            ev = st.evidence()
            deleted = reconcile.load_jsonl(str(st.deleted))
            drill = None
            if name.startswith("a") and ev[0]:
                g0 = ev[0][0]
                drill = reconcile.restore_drill(st.snap_file(g0["snap_id"]), g0["target"],
                                                [r for r in deleted if r["op"] == g0["id"]])
        finally:
            st.close()
        keep(out, st)
        rc = reconcile.reconcile(*ev, R)
        ids = ["op-c0", "op-c1"]
        fires = all(c.get("ok") for c in commits) and rc["flagged"] == ids and not rc["ok"]
        fired[name] = {"config": st.config, "commits": commits, "defects": rc["defects"], "fires": fires,
                       "restore_drill_of_stale_snapshot": drill}
    Rr.raw["controls"] = fired
    for name, f in fired.items():
        Rr.check("H6 CONTROL %s fires: the weakened gate commits and the reconciliation flags every commit" % name,
                 {"fires": True}, {"defects": [d["why"] for d in f["defects"]],
                                   "commits": [c.get("ok") for c in f["commits"]],
                                   "drill": f["restore_drill_of_stale_snapshot"]}, f["fires"])


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
            "harness_values": {"L_OP": L_OP}}


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    models = ["ControlStack/Scenarios/SC19Prod.lean", "ControlStack/Scenarios/AuthInstancesA.lean"]
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
        "clock": "time.monotonic_ns (CLOCK_MONOTONIC); one host",
        "sqlite": sqlite3.sqlite_version,
        "constants": {k: globals()[k] for k in ("R", "H5_OPS", "BG_INTERVAL", "LIFETIME", "WALL_LIMIT", "H6_CONFIGS",
                                                 "L_OP")},
    }


def preflight(args, m):
    problems = []
    if sys.version_info < (3, 9):
        problems.append("python >= 3.9 required")
    if not sys.platform.startswith("linux"):
        problems.append("linux required")
    stale = proc_scan("/var/tmp/sc19-run-")
    if stale:
        problems.append("processes of an earlier sc19 run still alive: %s" % [e["pid"] for e in stale])
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
    lines = ["# SC-19 two-phase destructive operations (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- calibration: %s, L_OP = %s s" % (m["calibration"]["status"], L_OP),
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
        if r["hyp"] == "H5":
            s = "latency ms %s, background writes %s" % (raw.get("latency_ms"), raw.get("background_writes"))
        elif r["hyp"] == "H4":
            s = "drills %s" % [(d.get("restored"), d.get("byte_exact")) for d in raw.get("drills", [])]
        elif r["hyp"] == "H6":
            s = "controls fired: %s" % {k: v["fires"] for k, v in raw.get("controls", {}).items()}
        else:
            s = "destroys %s" % (raw.get("reconcile", {}).get("reconciliation", {}).get("destroys"))
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
    ap = argparse.ArgumentParser(description="SC-19 two-phase destructive operations check (unprivileged).")
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
