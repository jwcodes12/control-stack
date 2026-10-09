#!/usr/bin/env python3
"""SC-15 merge gate (unprivileged). Preregistration: prereg/SC15-MERGE-GATE.md (PREREG-SC15-MERGE-v1).

Defensive reference test on one Linux host. A disposable bare git repository holds "main"; a benign scripted agent
(this runner) pushes single-commit change branches from its own clone. Separate processes: a reviewer and a security
reviewer record reviews of EXACT tree hashes; a trusted CI materialises exactly the reviewed tree and runs a fixed test
script on it; the merge gate computes the TRUSTED diff from git and fast-forwards main only if the exact tree has a
non-author review, a CI pass and, if it touches auth/ or ci/, a non-author security review. Each hypothesis is
repeated --reps times on fresh repositories and processes:

  H1 every commit on main has a review, a CI pass and (if sensitive) a security review of its exact tree by non-authors
     (reconciliation from the principals' logs and git history); missing reviews, failing CI and self-review refused
                                                              (sc15_safe, sc15_safe_authenticated, honest_merge)
  H2 amend after review (and after CI): merge refused until the new tree is reviewed and tested
                                          (deployed halves of stale_review_breaks, ci_other_content_breaks)
  H3 declared paths that understate the diff: the security review is still required (deployed half of
     declared_paths_breaks)
  H4 usefulness: honest changes merge within L_MERGE
  H5 admin HALT: no merge after the halt                         (halt_freezes, no_halt_check_breaks deployed half)
  H6 NEGATIVE_CONTROL: stale review, declared paths, CI on other content, self-review -> merged and flagged
         (stale_review_breaks, declared_paths_breaks, ci_other_content_breaks, self_review_breaks)
Nothing here says whether reviewed, tested code contains a backdoor: that is semantic and outside this test.

Receipts go to --out, which must not exist. No root, no accounts, no network: git (system /usr/bin/git, isolated
config) and Unix sockets in a fresh /var/tmp/sc15-run-* directory, removed afterwards. Python 3.9 compatible.
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
import time
import traceback
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
import gitutil  # noqa: E402
import reconcile  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "SC15-MERGE-GATE.md"
PREREG_ID = "PREREG-SC15-MERGE-v1"
HYPS = ["H1", "H2", "H3", "H4", "H5", "H6"]
CONTROLS = {"H6"}

# Preregistered constants (prereg §2-§3). Changing any of them needs a new prereg ID.
H4_CHANGES = 10
LIFETIME = 30.0
READY_TIMEOUT = 10.0
WALL_LIMIT = 115
H6_CONFIGS = {"a_stale_review": ["--any-review"], "b_declared_paths": ["--declared-paths"],
              "c_ci_other_content": ["--any-ci"], "d_self_review": ["--no-distinct"]}
SEED = {"README.md": "# demo service\n", "app/main.py": "def main():\n    return 0\n",
        "auth/login.py": "def login(user, password):\n    return False\n", "ci/pipeline.txt": "steps: test\n"}
# Tolerance fixed from dry-run calibration (prereg §3.0).
L_MERGE = 2.15              # s, H4: change + review (+ security) + CI + merge (calibrated)


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
        self.work = Path(tempfile.mkdtemp(prefix="sc15-run-", dir="/var/tmp"))
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


def rpc(path, obj, timeout=30.0):
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
    """bare repository + agent clone + reviewer + security reviewer + CI + merge gate"""

    def __init__(self, ctx, tag, gate_flags=(), agent_is_reviewer=False):
        self.ctx, self.tag = ctx, tag
        d = self.d = ctx.work / tag
        d.mkdir()
        self.procs = []
        self.home = str(d / "home")
        os.makedirs(self.home, mode=0o700)
        self.remote = str(d / "remote.git")
        g = lambda *a, **k: gitutil.git(self.home, *a, **k)
        g("init", "-q", "--bare", "-b", "main", self.remote)
        g("--git-dir", self.remote, "config", "core.logAllRefUpdates", "always")
        seed = str(d / "seed")
        g("clone", "-q", self.remote, seed)
        g("symbolic-ref", "HEAD", "refs/heads/main", cwd=seed)
        for p, c in SEED.items():
            os.makedirs(os.path.dirname(os.path.join(seed, p)) or seed, exist_ok=True)
            open(os.path.join(seed, p), "w").write(c)
        g("add", "-A", cwd=seed)
        g("commit", "-q", "-m", "genesis", cwd=seed)
        g("push", "-q", "origin", "main", cwd=seed)
        self.genesis = gitutil.rev(self.home, self.remote, "refs/heads/main")
        self.agent = str(d / "agent")
        g("clone", "-q", self.remote, self.agent)
        self.logs = {r: d / ("%s.jsonl" % r) for r in ("reviewer", "security", "ci")}
        self.gate_log = d / "gate.jsonl"
        pids = {}
        for role in ("reviewer", "security", "ci"):
            p = self._spawn(role, ctx.script("principal.py", "--lib", HERE, "--role", role, "--sock",
                                             d / ("%s-svc.sock" % role), "--gate-svc", d / "svc.sock", "--gate-role",
                                             d / ("ci.sock" if role == "ci" else "reviews.sock"), "--gitdir",
                                             self.remote, "--home", self.home, "--scratch", d / ("%s-scratch" % role),
                                             "--log", self.logs[role], "--lifetime", LIFETIME))
            pids[role] = read_tag(p, "READY")["pid"]
        rev = [str(pids["reviewer"])] + ([str(os.getpid())] if agent_is_reviewer else [])
        gt = self._spawn("gate", ctx.script("gate.py", "--lib", HERE, "--dir", d, "--gitdir", self.remote, "--home",
                                            self.home, "--reviewer-pids", ",".join(rev), "--security-pids",
                                            pids["security"], "--ci-pid", pids["ci"], "--log", self.gate_log,
                                            "--lifetime", LIFETIME, *gate_flags))
        self.config = read_tag(gt, "READY")["config"]
        self.config["agent_is_reviewer"] = agent_is_reviewer
        self.replies = []

    def _spawn(self, name, argv):
        with open(str(self.ctx.logs / ("%s-%s.stderr" % (self.tag, name))), "wb") as se:
            p = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=se, close_fds=True)
        self.procs.append(p)
        return p

    def _r(self, sock, obj):
        r = rpc(self.d / sock, obj)
        self.replies.append({"sock": sock, "req": obj, "reply": {k: v for k, v in r.items() if k != "rec"}})
        return r

    def _write(self, files):
        for p, c in files.items():
            full = os.path.join(self.agent, p)
            os.makedirs(os.path.dirname(full), exist_ok=True)
            open(full, "w").write(c)

    def change(self, id_, files, declared=None):
        g = lambda *a: gitutil.git(self.home, *a, cwd=self.agent)
        g("fetch", "-q", "origin")
        g("checkout", "-q", "-B", "change/" + id_, "origin/main")
        self._write(files)
        g("add", "-A")
        g("commit", "-q", "-m", "change " + id_)
        g("push", "-q", "-f", "origin", "change/" + id_)
        return self._r("agent.sock", {"op": "propose", "id": id_, "branch": "change/" + id_,
                                      "declared_paths": sorted(files) if declared is None else declared})

    def amend(self, id_, files):
        g = lambda *a: gitutil.git(self.home, *a, cwd=self.agent)
        g("checkout", "-q", "change/" + id_)
        self._write(files)
        g("add", "-A")
        g("commit", "-q", "--amend", "--no-edit")
        g("push", "-q", "-f", "origin", "change/" + id_)

    def review(self, id_):
        return self._r("reviewer-svc.sock", {"op": "review", "id": id_})

    def sec_review(self, id_):
        return self._r("security-svc.sock", {"op": "review", "id": id_})

    def ci(self, id_):
        return self._r("ci-svc.sock", {"op": "run", "id": id_})

    def self_review(self, id_):
        ch = rpc(self.d / "svc.sock", {"op": "get_change", "id": id_})
        return self._r("reviews.sock", {"op": "review", "id": id_, "tree": ch["tree"], "sec": False})

    def merge(self, id_):
        return self._r("agent.sock", {"op": "merge", "id": id_})

    def halt(self):
        return self._r("admin.sock", {"op": "halt"})

    def main(self):
        return gitutil.rev(self.home, self.remote, "refs/heads/main")

    def flow(self, id_, files, sensitive=False):
        t0 = time.monotonic()
        c = self.change(id_, files)
        r = self.review(id_)
        s = self.sec_review(id_) if sensitive else None
        ci = self.ci(id_)
        m = self.merge(id_)
        return {"merge": m, "lat_s": time.monotonic() - t0, "review": r.get("ok"), "ci": ci.get("ok")}

    def reconcile(self):
        hist = reconcile.main_history(gitutil, self.remote, self.home, self.genesis)
        ev = (hist, reconcile.load_committed(str(self.logs["reviewer"])),
              reconcile.load_committed(str(self.logs["security"])), reconcile.load_committed(str(self.logs["ci"])))
        return reconcile.reconcile(*ev), ev

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


def keep(out, st, extra=None):
    d = out / "logs" / st.tag
    d.mkdir(parents=True)
    for f in list(st.logs.values()) + [st.gate_log]:
        if f.exists():
            shutil.copy2(str(f), str(d / f.name))
    g = lambda *a: gitutil.git(st.home, "--git-dir", st.remote, *a)
    (d / "git-main-log.txt").write_text(g("log", "--first-parent", "--format=%H %T %s", "refs/heads/main"))
    (d / "git-main-reflog.txt").write_text(g("log", "-g", "--format=%H %gs", "refs/heads/main"))
    with open(str(d / "client.json"), "w") as fh:
        json.dump({"replies": st.replies, "extra": extra}, fh, default=str)


def check_reconcile(R, rc, name="reconciliation"):
    R.raw.setdefault("reconcile", {})[name] = rc
    R.check("%s: every commit on main has a non-author review, a CI pass and (if sensitive) a non-author security "
            "review of its exact tree, and is a merge point (sc15_safe)" % name, {"defects": []},
            {"commits_on_main": rc["commits_on_main"], "defects": rc["defects"]}, rc["ok"])


def feat(i, extra=""):
    return {"app/feature_%s.py" % i: "def feature_%s():\n    return %d\n%s" % (i, len(str(i)), extra)}


# ---------------------------------------------------------------- hypotheses
def h1(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h1" % rep, agent_is_reviewer=True)
    try:
        honest = []
        for i in range(4):
            honest.append(st.flow("c%d" % i, feat("c%d" % i)))
        honest.append(st.flow("s0", {"auth/login.py": "def login(user, password):\n    return check(user, password)\n"
                                     "def check(u, p):\n    return False\n"}, sensitive=True))
        honest.append(st.flow("s1", {"ci/pipeline.txt": "steps: lint, test\n"}, sensitive=True))
        neg = {}
        st.change("n-nosec", {"auth/session.py": "def session():\n    return None\n"})
        st.review("n-nosec")
        st.ci("n-nosec")
        neg["sensitive without security review"] = st.merge("n-nosec").get("error")
        st.change("n-cifail", feat("n", "# FAIL-TESTS\n"))
        st.review("n-cifail")
        st.ci("n-cifail")
        neg["failing CI"] = st.merge("n-cifail").get("error")
        st.change("n-self", feat("self"))
        neg["agent reviews its own change"] = st.self_review("n-self").get("error")
        st.ci("n-self")
        neg["merge after self-review attempt"] = st.merge("n-self").get("error")
        st.change("n-norev", feat("norev"))
        st.ci("n-norev")
        neg["no review"] = st.merge("n-norev").get("error")
        rc, ev = st.reconcile()
    finally:
        st.close()
    keep(out, st)
    R.raw.update(honest=[{"merge": h["merge"].get("ok"), "lat_s": round(h["lat_s"], 3)} for h in honest], refusals=neg)
    R.check("the 6 honest changes (2 sensitive, with security review) merge", [True] * 6,
            [bool(h["merge"].get("ok")) for h in honest], all(h["merge"].get("ok") for h in honest))
    exp = {"sensitive without security review": "security review required: trusted diff touches ['auth/session.py']",
           "failing CI": "no CI pass of the current tree",
           "agent reviews its own change": "reviewer is the author",
           "merge after self-review attempt": "no review of the current tree by a non-author",
           "no review": "no review of the current tree by a non-author"}
    R.check("refused with the right reason (sc15_safe_authenticated; distinct review)", exp, neg, neg == exp)
    R.check("main holds exactly the 6 honest merges", 6, rc["commits_on_main"], rc["commits_on_main"] == 6)
    check_reconcile(R, rc)
    mt = reconcile.mutation_selftest(*ev)
    R.check("reconciliation sensitivity: each injected defect in a copy of the stored evidence is flagged", True, mt,
            all(mt.values()) and len(mt) == 4)


def h2(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h2" % rep)
    cases = []
    try:
        for i in range(2):
            id_ = "a%d" % i
            st.change(id_, feat(id_))
            st.review(id_)
            st.ci(id_)
            st.amend(id_, feat(id_, "VALUE = %d\n" % (i + 100)))
            m1 = st.merge(id_)
            st.review(id_)
            m2 = st.merge(id_)
            st.ci(id_)
            m3 = st.merge(id_)
            tree_now = rpc(st.d / "svc.sock", {"op": "get_change", "id": id_})["tree"]
            cases.append({"after_amend": m1.get("error"), "after_re_review": m2.get("error"), "after_re_ci": m3.get("ok"),
                          "merged_tree_is_amended": m3.get("tree") == tree_now})
        rc, _ = st.reconcile()
    finally:
        st.close()
    keep(out, st, cases)
    R.raw["cases"] = cases
    R.check("H2: after amend, merge refused for want of a review of the new tree (stale_review_breaks deployed half); "
            "after re-review, refused for want of CI on the new tree (ci_other_content_breaks deployed half); after "
            "re-CI it merges the amended tree",
            [{"after_amend": "no review of the current tree by a non-author",
              "after_re_review": "no CI pass of the current tree", "after_re_ci": True,
              "merged_tree_is_amended": True}] * 2, cases,
            all(c == {"after_amend": "no review of the current tree by a non-author",
                      "after_re_review": "no CI pass of the current tree", "after_re_ci": True,
                      "merged_tree_is_amended": True} for c in cases))
    check_reconcile(R, rc)


def h3(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h3" % rep)
    cases = []
    try:
        for i in range(2):
            id_ = "d%d" % i
            st.change(id_, {"auth/token_%d.py" % i: "def token():\n    return 'static'\n", "app/notes_%d.txt" % i: "x\n"},
                      declared=["app/notes_%d.txt" % i])
            st.review(id_)
            st.ci(id_)
            m1 = st.merge(id_)
            st.sec_review(id_)
            m2 = st.merge(id_)
            cases.append({"without_security": m1.get("error"), "with_security": m2.get("ok")})
        rc, _ = st.reconcile()
    finally:
        st.close()
    keep(out, st, cases)
    R.raw["cases"] = cases
    R.check("H3: a change declared as app/ only but touching auth/ still needs a security review (trusted diff; "
            "declared_paths_breaks deployed half)", [{"without_security": "security review required", "with": True}] * 2,
            cases, all(str(c["without_security"]).startswith("security review required: trusted diff touches ['auth/")
                       and c["with_security"] for c in cases))
    check_reconcile(R, rc)


def h4(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h4" % rep)
    res = []
    try:
        for i in range(H4_CHANGES):
            if i % 5 == 4:
                res.append(st.flow("u%d" % i, {"auth/policy_%d.py" % i: "ALLOW = []\n"}, sensitive=True))
            else:
                res.append(st.flow("u%d" % i, feat("u%d" % i)))
        rc, _ = st.reconcile()
    finally:
        st.close()
    keep(out, st)
    ls = sorted(r["lat_s"] for r in res)
    okn = sum(1 for r in res if r["merge"].get("ok"))
    R.raw.update(latency_ms={"p50": round(ls[len(ls) // 2] * 1e3, 1), "max": round(ls[-1] * 1e3, 1)},
                 max_latency_s=ls[-1])
    R.check("H4: all %d honest changes merge, each within L_MERGE = %.2f s" % (H4_CHANGES, L_MERGE),
            {"ok": H4_CHANGES, "max_s": "<= %.2f" % L_MERGE}, {"ok": okn, "latency_ms": R.raw["latency_ms"]},
            okn == H4_CHANGES and ls[-1] <= L_MERGE)
    check_reconcile(R, rc)


def h5(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h5" % rep)
    try:
        for i in range(2):
            st.flow("p%d" % i, feat("p%d" % i))
        for i in range(2):
            st.change("q%d" % i, feat("q%d" % i))
            st.review("q%d" % i)
            st.ci("q%d" % i)
        before = st.main()
        st.halt()
        after = [st.merge("q%d" % i).get("error") for i in range(2)]
        main_after = st.main()
        rc, _ = st.reconcile()
    finally:
        st.close()
    keep(out, st)
    R.raw.update(refusals=after)
    R.check("H5: reviewed, tested changes are refused after the HALT and main does not move (halt_freezes, "
            "no_halt_check_breaks deployed half)", {"refusals": ["halted", "halted"], "main_moved": False,
                                                    "commits_on_main": 2},
            {"refusals": after, "main_moved": main_after != before, "commits_on_main": rc["commits_on_main"]},
            after == ["halted", "halted"] and main_after == before and rc["commits_on_main"] == 2)
    check_reconcile(R, rc)


def h6(ctx, out, rep, R):
    fired = {}
    for name, flags in H6_CONFIGS.items():
        st = Stack(ctx, "r%d-h6%s" % (rep, name[0]), flags, agent_is_reviewer=name.startswith("d"))
        merges = []
        try:
            for i in range(1):
                id_ = "%s%d" % (name[0], i)
                if name.startswith("a"):
                    st.change(id_, feat(id_))
                    st.review(id_)
                    st.amend(id_, feat(id_, "VALUE = 7\n"))
                    st.ci(id_)
                elif name.startswith("b"):
                    st.change(id_, {"auth/shortcut_%d.py" % i: "def allow():\n    return True\n"}, declared=["app/"])
                    st.review(id_)
                    st.ci(id_)
                elif name.startswith("c"):
                    files = feat(id_)
                    st.change(id_, files)
                    st.ci(id_)
                    st.amend(id_, feat(id_, "# FAIL-TESTS\n"))
                    st.review(id_)
                else:
                    st.change(id_, feat(id_))
                    st.self_review(id_)
                    st.ci(id_)
                merges.append(st.merge(id_))
            rc, _ = st.reconcile()
        finally:
            st.close()
        keep(out, st)
        fires = all(m.get("ok") for m in merges) and rc["commits_on_main"] == 1 and len(rc["defects"]) == 1
        fired[name] = {"config": st.config, "merges": [m.get("ok") for m in merges],
                       "defects": [d["why"] for d in rc["defects"]], "fires": fires}
    R.raw["controls"] = fired
    for name, f in fired.items():
        R.check("H6 CONTROL %s fires: the weakened gate merges and the reconciliation flags the merged commit" % name,
                {"fires": True}, {k: v for k, v in f.items() if k != "config"}, f["fires"])


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
            "harness_values": {"L_MERGE": L_MERGE}}


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    models = ["ControlStack/Scenarios/SC15Review.lean", "ControlStack/Scenarios/AuthInstancesB.lean"]
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
        "git": subprocess.run([gitutil.GIT, "--version"], stdout=subprocess.PIPE, universal_newlines=True).stdout.strip(),
        "constants": {k: globals()[k] for k in ("H4_CHANGES", "LIFETIME", "WALL_LIMIT", "H6_CONFIGS", "SEED",
                                                 "L_MERGE")},
    }


def preflight(args, m):
    problems = []
    if sys.version_info < (3, 9):
        problems.append("python >= 3.9 required")
    if not os.access(gitutil.GIT, os.X_OK):
        problems.append("%s not available" % gitutil.GIT)
    if not sys.platform.startswith("linux"):
        problems.append("linux required")
    stale = proc_scan("/var/tmp/sc15-run-")
    if stale:
        problems.append("processes of an earlier sc15 run still alive: %s" % [e["pid"] for e in stale])
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
    lines = ["# SC-15 merge gate (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- calibration: %s, L_MERGE = %s s" % (m["calibration"]["status"], L_MERGE),
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
        if r["hyp"] == "H4":
            s = "latency ms %s" % raw.get("latency_ms")
        elif r["hyp"] == "H6":
            s = "controls fired: %s" % {k: v["fires"] for k, v in raw.get("controls", {}).items()}
        else:
            s = "commits on main %s" % (raw.get("reconcile", {}).get("reconciliation", {}).get("commits_on_main"))
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
    ap = argparse.ArgumentParser(description="SC-15 merge gate check (unprivileged).")
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
