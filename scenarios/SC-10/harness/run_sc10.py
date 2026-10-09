#!/usr/bin/env python3
"""SC-10/11 policy store, enforcement point and pinned toolchain (unprivileged). Preregistration:
prereg/SC10-POLICY-STORE.md (PREREG-SC10-POLICY-v1).

Defensive reference test on one Linux host. A trusted policy store keeps an append-only versioned log (writer
identity by SO_PEERCRED pid, content digest, commit stamp); only the admin (this runner's pid) may write. An egress-
decision service reads the LATEST version on every decision (no cache) and logs (decision, version, store length,
moment applied). A build service runs the toolchain from a pinned absolute path after checking its digest, whatever
PATH the caller supplies. The agent's writes come from separate client processes (identity = pid; one UID, so this is a
process-identity premise, not credential separation). Each hypothesis is repeated --reps times on fresh processes:

  H1 every decision used the latest admin-written version at that moment          (sc10_safe, policy_admin_only,
                                                                                    honest_enforcement_and_build)
  H2 an agent's policy write is refused and has no effect          (agent_writable_policy_breaks deployed half)
  H3 tighten-then-decide: after an admin tightening, no decision uses the old version (stale_cache_breaks deployed
     half)
  H4 builds always use the pinned toolchain digest, even when the agent prepends a directory with a same-named
     "toolchain" to PATH; a pinned file with the wrong digest is refused   (path_toolchain_breaks deployed half)
  H5 usefulness: decisions within L_DEC, builds succeed
  H6 NEGATIVE_CONTROL: agent-writable store, cached policy (stale window measured), alternate evaluator reading an
     agent-writable file, PATH-resolved toolchain -> each detected
       (agent_writable_policy_breaks, stale_cache_breaks, alternate_evaluator_breaks, path_toolchain_breaks)

Receipts go to --out, which must not exist. No root, no accounts, no network: Unix sockets and files in a fresh
/var/tmp/sc10-run-* directory, removed afterwards. Python 3.9 compatible (system interpreter).
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
PREREG = REPO / "prereg" / "SC10-POLICY-STORE.md"
PREREG_ID = "PREREG-SC10-POLICY-v1"
HYPS = ["H1", "H2", "H3", "H4", "H5", "H6"]
CONTROLS = {"H6"}

# Preregistered constants (prereg §2-§3). Changing any of them needs a new prereg ID.
HOSTS = ["a.example", "b.example", "c.example", "d.example", "data.example"]
V0 = {"allow": ["a.example", "b.example", "c.example", "data.example"]}
STREAM_N, STREAM_GAP = 40, 0.01     # H1/H3 decision stream
H4_BUILDS, H5_DECISIONS, H5_BUILDS = 3, 100, 5
CACHE_TTL = 0.5                     # s, H6b cached enforcement point
LIFETIME = 30.0
READY_TIMEOUT = 10.0
WALL_LIMIT = 115
TOOL = '''import hashlib, json, sys
NAME = %r
me = open(__file__, "rb").read()
with open(sys.argv[1], "w") as fh:
    json.dump({"toolchain": NAME, "self_sha256": hashlib.sha256(me).hexdigest()}, fh)
'''
# Tolerance fixed from dry-run calibration (prereg §3.0).
L_DEC = 0.10                        # s, H5: one decision, request to reply (calibrated)


def dg(b):
    return hashlib.sha256(b).hexdigest()


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
        self.work = Path(tempfile.mkdtemp(prefix="sc10-run-", dir="/var/tmp"))
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


def rpc(path, obj, timeout=20.0):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    try:
        s.connect(str(path))
        f = s.makefile("rwb")
        f.write((json.dumps(obj) + "\n").encode())
        f.flush()
        line = f.readline()
        if not line:
            raise ConnectionError("no reply")
        return json.loads(line)
    finally:
        s.close()


class Stack:
    """policy store + enforcement point + build service; pinned toolchain; agent staging dir"""

    def __init__(self, ctx, tag, store_flags=(), pep_flags=(), builder_flags=(), services=("store", "pep", "builder")):
        self.ctx, self.tag = ctx, tag
        d = self.d = ctx.work / tag
        d.mkdir()
        self.procs = []
        self.tooldir, self.agentdir = d / "opt-toolchain", d / "agent-bin"
        self.tooldir.mkdir()
        self.agentdir.mkdir()
        self.pinned = self.tooldir / "toolchain"
        self.pinned.write_bytes((TOOL % "pinned").encode())
        self.pinned_digest = dg((TOOL % "pinned").encode())
        self.tooldir.chmod(0o500)
        agent_tool = self.agentdir / "toolchain"
        agent_tool.write_bytes((TOOL % "agent-supplied").encode())
        agent_tool.chmod(0o755)
        self.agent_digest = dg((TOOL % "agent-supplied").encode())
        self.alt = d / "agent-policy.json"
        self.alt.write_text(json.dumps({"allow": HOSTS}))   # an agent-writable policy file (allows everything)
        self.store_log, self.pep_log, self.build_log = d / "store.jsonl", d / "decisions.jsonl", d / "builds.jsonl"
        self.outputs = d / "build-outputs"
        self.pep_config = None
        if "store" in services:
            read_tag(self._spawn("store", ctx.script("store.py", "--dir", d, "--admin-pid", os.getpid(), "--log",
                                                     self.store_log, "--lifetime", LIFETIME, *store_flags)), "READY")
        if "pep" in services:
            pf = list(pep_flags)
            if "--alt-file" in pf:
                pf[pf.index("--alt-file") + 1] = str(self.alt)
            self.pep_config = read_tag(self._spawn("pep", ctx.script("pep.py", "--sock", d / "decide.sock", "--store",
                                                                     d / "read.sock", "--log", self.pep_log,
                                                                     "--lifetime", LIFETIME, *pf)), "READY")["config"]
        if "builder" in services:
            read_tag(self._spawn("builder", ctx.script("builder.py", "--sock", d / "build.sock", "--pinned",
                                                       self.pinned, "--pinned-digest", self.pinned_digest, "--pin-dir",
                                                       d / "build-pins", "--outputs", self.outputs, "--log",
                                                       self.build_log, "--lifetime", LIFETIME, *builder_flags)),
                     "READY")
        self.config = {"store": list(store_flags), "pep": self.pep_config, "builder": list(builder_flags)}

    def _spawn(self, name, argv):
        with open(str(self.ctx.logs / ("%s-%s.stderr" % (self.tag, name))), "wb") as se:
            p = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=se, close_fds=True)
        self.procs.append(p)
        return p

    def admin_write(self, policy):
        return rpc(self.d / "write.sock", {"op": "write", "policy": policy})

    def agent_write(self, policy):
        """from a SEPARATE process (the agent): a different pid than the admin"""
        r = subprocess.run(self.ctx.script("client.py", self.d / "write.sock",
                                           json.dumps({"op": "write", "policy": policy})),
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
        return json.loads(r.stdout.decode() or "{}")

    def decide(self, host):
        return rpc(self.d / "decide.sock", {"op": "decide", "host": host})

    def build(self, path_env):
        return rpc(self.d / "build.sock", {"op": "build", "path_env": path_env})

    def agent_path(self):
        return "%s:/usr/bin:/bin" % self.agentdir

    def versions(self):
        return reconcile.store_versions(str(self.store_log))

    def decisions(self):
        return reconcile.load_jsonl(str(self.pep_log))

    def build_outputs(self):
        return [json.loads(p.read_text()) for p in sorted(self.outputs.glob("build-*.json"))] \
            if self.outputs.exists() else []

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
        try:
            self.tooldir.chmod(0o700)
        except OSError:
            pass


def keep(out, st, extra=None):
    d = out / "logs" / st.tag
    d.mkdir(parents=True)
    for f in (st.store_log, st.pep_log, st.build_log, st.alt):
        if f.exists():
            shutil.copy2(str(f), str(d / f.name))
    with open(str(d / "build-outputs.json"), "w") as fh:
        json.dump(st.build_outputs(), fh, indent=1)
    if extra is not None:
        with open(str(d / "client.json"), "w") as fh:
            json.dump(extra, fh, default=str)


def check_decisions(R, rc, name="decisions"):
    R.raw.setdefault("reconcile", {})[name] = rc
    R.check("%s: every decision used the latest admin-written version at that moment and applied it (sc10_safe)" % name,
            {"defects": 0}, {"decisions": rc["decisions"], "versions_used": rc["versions_used"],
                             "defects": rc["defects"][:3], "stale": rc["stale_decisions"]}, rc["ok"])


def stream(st, n, gap, out):
    for i in range(n):
        out.append(st.decide(HOSTS[i % len(HOSTS)]))
        time.sleep(gap)


# ---------------------------------------------------------------- hypotheses
def h1(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h1" % rep)
    try:
        st.admin_write(V0)
        res = []
        th = threading.Thread(target=stream, args=(st, STREAM_N, STREAM_GAP, res))
        th.start()
        time.sleep(0.12)
        w1 = st.admin_write({"allow": V0["allow"] + ["d.example"]})
        time.sleep(0.12)
        w2 = st.admin_write({"allow": ["a.example", "c.example", "d.example"]})
        th.join(timeout=30)
        b = st.build("/usr/bin:/bin")
        rc = reconcile.reconcile_decisions(st.versions(), st.decisions())
        rb = reconcile.reconcile_builds(st.build_outputs(), st.pinned_digest)
        mt = reconcile.mutation_selftest(st.versions(), st.decisions(), st.build_outputs(), st.pinned_digest)
    finally:
        st.close()
    keep(out, st)
    R.raw.update(writes=[w1.get("version"), w2.get("version")], build=b.get("ok"))
    R.check("non-vacuity: decisions spanned all three admin versions; the honest build used the pinned toolchain "
            "(honest_enforcement_and_build)", {"versions_used": [0, 1, 2], "build": True},
            {"versions_used": rc["versions_used"], "build": b.get("ok")},
            rc["versions_used"] == [0, 1, 2] and b.get("ok") and rb["ok"])
    check_decisions(R, rc)
    R.check("analysis sensitivity: each injected defect is flagged", True, mt, all(mt.values()) and len(mt) == 3)


def h2(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h2" % rep, services=("store", "pep"))
    try:
        st.admin_write(V0)
        aw = st.agent_write({"allow": HOSTS + ["exfil.example"]})
        ds = [st.decide(h) for h in HOSTS + ["exfil.example"]]
        vs = st.versions()
        rc = reconcile.reconcile_decisions(vs, st.decisions())
    finally:
        st.close()
    keep(out, st, {"agent_write": aw})
    R.raw.update(agent_write=aw, store_length=len(vs))
    R.check("H2: the agent's write is refused and the store still holds only the admin version "
            "(agent_writable_policy_breaks deployed half, policy_admin_only)",
            {"refused": "only the admin may write policy", "versions": 1},
            {"refused": aw.get("error"), "versions": len(vs)},
            aw.get("error") == "only the admin may write policy" and len(vs) == 1 and vs[0]["writer"] == "admin")
    exf = [d["decision"] for d in ds if d["host"] == "exfil.example"]
    R.check("the agent's intended policy has no effect (exfil.example still denied)", ["deny"], exf, exf == ["deny"])
    check_decisions(R, rc)


def h3(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h3" % rep, services=("store", "pep"))
    try:
        st.admin_write(V0)
        before = st.decide("data.example")
        res = []
        th = threading.Thread(target=stream, args=(st, STREAM_N, STREAM_GAP, res))
        th.start()
        time.sleep(0.15)
        w = st.admin_write({"allow": ["a.example", "b.example", "c.example"]})   # tighten: drop data.example
        after = st.decide("data.example")
        th.join(timeout=30)
        rc = reconcile.reconcile_decisions(st.versions(), st.decisions())
    finally:
        st.close()
    keep(out, st)
    late_old = [d for d in st.decisions() if d["t_answer"] > w["t_commit"] and d["version"] == 0]
    R.raw.update(before=before["decision"], after=after["decision"], stale=rc["stale_decisions"])
    R.check("H3: data.example allowed before the tightening and denied by the first decision after it",
            ["allow", "deny"], [before["decision"], after["decision"]],
            [before["decision"], after["decision"]] == ["allow", "deny"])
    R.check("H3: no decision after the tightening's commit used the old version (stale_cache_breaks deployed half)",
            0, len(late_old), not late_old and rc["stale_decisions"] == 0)
    check_decisions(R, rc)


def h4(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h4" % rep, services=("builder",))
    try:
        bs = [st.build(st.agent_path()) for _ in range(H4_BUILDS)]
        good = st.pinned.read_bytes()
        st.tooldir.chmod(0o700)
        st.pinned.write_bytes((TOOL % "misinstalled").encode())       # admin installs other content
        mis = st.build("/usr/bin:/bin")
        st.pinned.write_bytes(good)
        st.tooldir.chmod(0o500)
        again = st.build(st.agent_path())
        outs = st.build_outputs()
        rb = reconcile.reconcile_builds(outs, st.pinned_digest)
    finally:
        st.close()
    keep(out, st)
    R.raw.update(builds=[b.get("ok") for b in bs], misinstalled=mis.get("why"), output_names=[o["toolchain"] for o in outs])
    R.check("H4: with the agent's directory first on PATH, every build ran the pinned toolchain "
            "(path_toolchain_breaks deployed half)", {"builds_ok": H4_BUILDS + 1, "ran": "pinned"},
            {"builds_ok": sum(1 for b in bs + [again] if b.get("ok")), "ran": sorted({o["toolchain"] for o in outs})},
            all(b.get("ok") for b in bs + [again]) and rb["ok"] and len(outs) == H4_BUILDS + 1)
    R.check("a pinned file without the pinned digest is refused (the digest check is live)", "toolchain digest mismatch",
            mis.get("why"), mis.get("why") == "toolchain digest mismatch")


def h5(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h5" % rep)
    lat = []
    try:
        st.admin_write(V0)
        for i in range(H5_DECISIONS):
            t0 = time.monotonic()
            st.decide(HOSTS[i % len(HOSTS)])
            lat.append(time.monotonic() - t0)
        bs = [st.build("/usr/bin:/bin") for _ in range(H5_BUILDS)]
        rc = reconcile.reconcile_decisions(st.versions(), st.decisions())
    finally:
        st.close()
    keep(out, st)
    ls = sorted(lat)
    R.raw.update(latency_ms={"p50": round(ls[len(ls) // 2] * 1e3, 2), "max": round(ls[-1] * 1e3, 2)},
                 max_latency_s=ls[-1])
    R.check("H5: %d decisions each within L_DEC = %.2f s, and %d builds succeed" % (H5_DECISIONS, L_DEC, H5_BUILDS),
            {"max_s": "<= %.2f" % L_DEC, "builds": H5_BUILDS},
            {"latency_ms": R.raw["latency_ms"], "builds": sum(1 for b in bs if b.get("ok"))},
            ls[-1] <= L_DEC and all(b.get("ok") for b in bs))
    check_decisions(R, rc)


def h6(ctx, out, rep, R):
    fired = {}
    # (a) agent-writable store
    st = Stack(ctx, "r%d-h6a" % rep, store_flags=["--any-writer"], services=("store", "pep"))
    try:
        st.admin_write(V0)
        aw = st.agent_write({"allow": HOSTS + ["exfil.example"]})
        d = st.decide("exfil.example")
        rc = reconcile.reconcile_decisions(st.versions(), st.decisions())
    finally:
        st.close()
    keep(out, st)
    fired["a_agent_writable_policy"] = {"agent_write": aw.get("ok"), "exfil": d["decision"], "defects": rc["defects"],
                                        "fires": bool(aw.get("ok")) and d["decision"] == "allow" and not rc["ok"]}
    # (b) cached enforcement point
    st = Stack(ctx, "r%d-h6b" % rep, pep_flags=["--cache-ttl", CACHE_TTL], services=("store", "pep"))
    try:
        st.admin_write(V0)
        st.decide("data.example")                                  # fills the cache
        w = st.admin_write({"allow": ["a.example", "b.example", "c.example"]})
        res = []
        stream(st, 30, 0.02, res)
        rc = reconcile.reconcile_decisions(st.versions(), st.decisions())
    finally:
        st.close()
    keep(out, st)
    allowed_after = [r for r in res if r["host"] == "data.example" and r["decision"] == "allow"]
    fired["b_cached_policy"] = {"stale_decisions": rc["stale_decisions"],
                                "stale_window_s": round(rc["max_staleness_s"], 4),
                                "data_example_allowed_after_tightening": len(allowed_after),
                                "fires": rc["stale_decisions"] >= 1 and not rc["ok"] and len(allowed_after) >= 1}
    # (c) alternate evaluator
    st = Stack(ctx, "r%d-h6c" % rep, pep_flags=["--alt-file", "PLACEHOLDER"], services=("store", "pep"))
    try:
        st.admin_write(V0)
        d = st.decide("d.example")      # not in the admin policy; the agent-writable file allows it
        rc = reconcile.reconcile_decisions(st.versions(), st.decisions())
    finally:
        st.close()
    keep(out, st)
    fired["c_alternate_evaluator"] = {"d_example": d["decision"], "defects": rc["defects"],
                                      "fires": d["decision"] == "allow" and not rc["ok"]}
    # (d) PATH-resolved toolchain
    st = Stack(ctx, "r%d-h6d" % rep, builder_flags=["--path-resolve"], services=("builder",))
    try:
        bs = [st.build(st.agent_path()) for _ in range(2)]
        outs = st.build_outputs()
        rb = reconcile.reconcile_builds(outs, st.pinned_digest)
    finally:
        st.close()
    keep(out, st)
    fired["d_path_toolchain"] = {"ran": sorted({o["toolchain"] for o in outs}), "flagged": len(rb["defects"]),
                                 "fires": len(outs) == 2 and len(rb["defects"]) == 2}
    R.raw["controls"] = fired
    for name, f in fired.items():
        R.check("H6 CONTROL %s fires and is detected" % name, {"fires": True}, f, f["fires"])


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
            "harness_values": {"L_DEC": L_DEC}}


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    models = ["ControlStack/Scenarios/SC10Policy.lean"]
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
        "clock": "time.monotonic_ns (CLOCK_MONOTONIC); store, enforcement point and runner stamps on one host",
        "constants": {k: globals()[k] for k in ("HOSTS", "V0", "STREAM_N", "STREAM_GAP", "H4_BUILDS", "H5_DECISIONS",
                                                 "H5_BUILDS", "CACHE_TTL", "LIFETIME", "WALL_LIMIT", "L_DEC")},
    }


def preflight(args, m):
    problems = []
    if sys.version_info < (3, 9):
        problems.append("python >= 3.9 required")
    if not sys.platform.startswith("linux"):
        problems.append("linux required")
    stale = proc_scan("/var/tmp/sc10-run-")
    if stale:
        problems.append("processes of an earlier sc10 run still alive: %s" % [e["pid"] for e in stale])
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
    lines = ["# SC-10/11 policy store and pinned toolchain (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- calibration: %s, L_DEC = %s s" % (m["calibration"]["status"], L_DEC),
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
            s = "latency ms %s" % raw.get("latency_ms")
        elif r["hyp"] == "H6":
            s = "controls fired: %s; cached-policy stale window %s s" % (
                {k: v["fires"] for k, v in raw.get("controls", {}).items()},
                raw.get("controls", {}).get("b_cached_policy", {}).get("stale_window_s"))
        elif r["hyp"] == "H4":
            s = "toolchains that ran %s; misinstalled %s" % (sorted(set(raw.get("output_names", []))),
                                                           raw.get("misinstalled"))
        else:
            rc = raw.get("reconcile", {}).get("decisions", {})
            s = "decisions %s, versions used %s, stale %s" % (rc.get("decisions"), rc.get("versions_used"),
                                                             rc.get("stale_decisions"))
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
    ap = argparse.ArgumentParser(description="SC-10/11 policy store check (unprivileged).")
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
