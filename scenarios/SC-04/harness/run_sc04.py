#!/usr/bin/env python3
"""SC-04 log canonicaliser (unprivileged). Preregistration: prereg/SC04-LOG-CANON.md (PREREG-SC04-LOGCANON-v1).

Defensive reference test on one Linux host. A benign agent process emits diagnostic log records; a trusted
canonicaliser maps each to one of K templates with f numeric fields quantised to Q levels and drops everything else
(including free text); a downstream receiver sees only the canonical records. Each hypothesis is repeated --reps times
on fresh processes:

  H1 the receiver's view is schema-only: a template in [0, K) and f integer fields in [0, Q), with no other key and no
     free text, for every record                                                            (log_channel premise)
  H2 empirical capacity: over many covert attempts (a benign random token as the "secret"), the number of distinct
     canonical views, and a best (maximum-likelihood) decoder's accuracy, against the proved bound (K*Q^f)^m/|M|
                                                                                             (log_channel)
  H3 usefulness: error counts per template in the canonical view equal the raw counts the agent emitted
  H4 NEGATIVE_CONTROL: a free-text field passed through -> the receiver recovers the token in one record
                                                                                             (free_text_leaks)

Receipts go to --out, which must not exist. No root, no accounts, no network: Unix sockets and files in a fresh
/var/tmp/sc04-run-* directory, removed afterwards. Python 3.9 compatible (system interpreter).
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
import analyse  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "SC04-LOG-CANON.md"
PREREG_ID = "PREREG-SC04-LOGCANON-v1"
HYPS = ["H1", "H2", "H3", "H4"]
CONTROLS = {"H4"}

# Preregistered constants (prereg §2-§3). Changing any of them needs a new prereg ID.
K, F, Q = 8, 2, 4              # templates, numeric fields, quantisation levels; alphabet = K*Q^f = 128
FIELD_MAX = 1000
N_TOKENS = 4000
M_VALUES = (1, 2)             # records per covert attempt
H1_RECORDS = 40
LIFETIME = 60.0
READY_TIMEOUT = 10.0
WALL_LIMIT = 115
# Fixed from dry-run timing (prereg §3.0): the per-template decoder accuracy tolerance is not a timing value; the
# only decision margin is EPS on the proved bound (floating point).
EPS = 1e-9


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
        self.work = Path(tempfile.mkdtemp(prefix="sc04-run-", dir="/var/tmp"))
        self.work.chmod(0o700)
        self.logs = self.work / "logs"
        self.logs.mkdir()
        self.py = sys.executable

    def script(self, name, *args):
        return [self.py, "-I", "-S", "-B", str(HERE / name)] + [str(a) for a in args]


class LineReader:
    def __init__(self, p):
        self.p, self.buf = p, b""

    def tag(self, tag, timeout=READY_TIMEOUT):
        t_end = time.monotonic() + timeout
        while b"\n" not in self.buf:
            rem = t_end - time.monotonic()
            if rem <= 0:
                raise TimeoutError("no %s within %.1fs from pid %d" % (tag, timeout, self.p.pid))
            r, _, _ = select.select([self.p.stdout.fileno()], [], [], rem)
            if not r:
                continue
            chunk = os.read(self.p.stdout.fileno(), 1 << 20)
            if not chunk:
                raise RuntimeError("EOF from pid %d (rc=%s)" % (self.p.pid, self.p.poll()))
            self.buf += chunk
        ln, self.buf = self.buf.split(b"\n", 1)
        ln = ln.decode()
        if not ln.startswith(tag + " "):
            raise RuntimeError("unexpected output: %r" % ln[:200])
        return json.loads(ln[len(tag) + 1:])


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
    """canonicaliser + agent"""

    def __init__(self, ctx, tag, free_field=None):
        self.ctx, self.tag = ctx, tag
        d = self.d = ctx.work / tag
        d.mkdir()
        self.procs = []
        self.view = d / "receiver-view.jsonl"
        cargs = ["--dir", d, "--view", self.view, "--k", K, "--f", F, "--q", Q, "--field-max", FIELD_MAX,
                 "--lifetime", LIFETIME]
        if free_field is not None:
            cargs += ["--free-field", free_field]
        self.canon_info = LineReader(self._spawn("canon", ctx.script("canon.py", *cargs))).tag("READY")
        with open(str(ctx.logs / ("%s-agent.stderr" % tag)), "wb") as se:
            self.agent = subprocess.Popen(ctx.script("agent.py", "--canon", d / "agent.sock", "--k", K, "--f", F,
                                                     "--q", Q, "--field-max", FIELD_MAX),
                                          stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=se, close_fds=True,
                                          bufsize=0)
        self.procs.append(self.agent)
        self.ar = LineReader(self.agent)
        self.ar.tag("READY")

    def _spawn(self, name, argv):
        with open(str(self.ctx.logs / ("%s-%s.stderr" % (self.tag, name))), "wb") as se:
            p = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=se, close_fds=True)
        self.procs.append(p)
        return p

    def emit(self, cmd):
        self.agent.stdin.write((json.dumps(cmd) + "\n").encode())
        return self.ar.tag("DONE", 15)["result"]

    def view_records(self):
        return rpc(self.d / "receiver.sock", {"op": "view"})["view"]

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
            for f in (p.stdin, p.stdout):
                if f:
                    try:
                        f.close()
                    except OSError:
                        pass


def keep(out, st):
    d = out / "logs" / st.tag
    d.mkdir(parents=True)
    import gzip
    if st.view.exists():
        with open(str(st.view), "rb") as src, gzip.open(str(d / "receiver-view.jsonl.gz"), "wb") as dst:
            shutil.copyfileobj(src, dst)


RAW_EVENTS = ["startup", "request", "db_query", "cache_miss", "retry", "timeout", "error", "shutdown"]


# ---------------------------------------------------------------- hypotheses
def h1(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h1" % rep)
    try:
        raw = []
        for i in range(H1_RECORDS):
            ev = RAW_EVENTS[i % K]
            rec = {"event": ev, "field0": (i * 37) % FIELD_MAX, "field1": (i * 101) % FIELD_MAX,
                   "message": "secret marker token-%d: transfer 999" % i, "note": "token-%d" % i, "level": "INFO"}
            raw.append(rec)
            st.emit({"op": "emit", "record": rec})
        view = st.view_records()
    finally:
        st.close()
    keep(out, st)
    sc = analyse.schema_check(view, K, F, Q)
    leaked = [r for r in raw if analyse.leak_check(view, r["note"])["token_in_view"]]
    R.raw.update(schema=sc, sample_view=view[:3], templates=st.canon_info["templates"])
    R.check("H1: every receiver record is schema-only (template in [0,%d), %d fields in [0,%d)), no free text "
            "(log_channel premise)" % (K, F, Q), {"records": H1_RECORDS, "defects": 0},
            {"records": sc["records"], "defects": sc["defects"]}, sc["ok"] and sc["records"] == H1_RECORDS)
    R.check("none of the per-record marker tokens appears in the receiver's view", 0, len(leaked), not leaked)


def h2(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h2" % rep)
    results = {}
    try:
        off = 0
        for m in M_VALUES:
            trials = []
            for ti in range(N_TOKENS):
                token = dg(("%d|%d|%d" % (rep, m, ti)).encode())[:16]
                for r in range(m):
                    st.emit({"op": "emit_secret", "token": token, "r": r})
                trials.append({"token": token})
            view = st.view_records()
            for j, t in enumerate(trials):
                t["view"] = view[off + j * m: off + (j + 1) * m]
            off += N_TOKENS * m
            results["m=%d" % m] = analyse.capacity(trials, K, F, Q)
    finally:
        st.close()
    keep(out, st)
    R.raw["capacity"] = results
    for m in M_VALUES:
        c = results["m=%d" % m]
        R.check("H2 capacity (m=%d): best-decoder accuracy <= the proved bound (K*Q^f)^m/|M| = %.4g (log_channel)"
                % (m, c["bound"]), {"acc": "<= %.4g" % c["bound"]},
                {"best_decoder_acc": round(c["best_decoder_acc"], 5), "distinct_views": c["distinct_views"],
                 "alphabet": c["alphabet"], "bound": round(c["bound"], 5)}, c["within_bound"])
    c1 = results["m=1"]
    R.check("H2 non-vacuity (m=1): distinct canonical views <= the alphabet K*Q^f, and the bound bit (< 1)",
            {"distinct_views": "<= %d" % c1["alphabet"], "bound": "< 1"},
            {"distinct_views": c1["distinct_views"], "bound": round(c1["bound"], 5)},
            c1["distinct_views"] <= c1["alphabet"] and c1["bound"] < 1.0)


def h3(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h3" % rep)
    raw_counts = {}
    try:
        import random
        rng = random.Random(rep)
        for _ in range(100):
            ev = RAW_EVENTS[rng.randrange(K)]
            raw_counts[ev] = raw_counts.get(ev, 0) + 1
            st.emit({"op": "emit", "record": {"event": ev, "field0": rng.randrange(FIELD_MAX),
                                              "message": "diagnostic %s" % ev}})
        view = st.view_records()
    finally:
        st.close()
    keep(out, st)
    tmpl = st.canon_info["templates"]
    canon_counts = {}
    for r in view:
        canon_counts[tmpl[r["template"]]] = canon_counts.get(tmpl[r["template"]], 0) + 1
    want = {ev: raw_counts.get(ev, 0) for ev in tmpl}
    got = {ev: canon_counts.get(ev, 0) for ev in tmpl}
    R.raw.update(raw_counts=want, canonical_counts=got)
    R.check("H3: per-template counts in the canonical view equal the raw emitted counts (diagnostics still "
            "answerable)", want, got, want == got and sum(got.values()) == 100)
    R.check("in particular the error-template count matches", want.get("error", 0), got.get("error", 0),
            want.get("error", 0) == got.get("error", 0))


def h4(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h4" % rep, free_field="note")
    try:
        token = dg(("leak|%d" % rep).encode())[:16]
        st.emit({"op": "emit", "record": {"event": "request", "field0": 1, "note": token,
                                          "message": "carrying %s" % token}})
        view = st.view_records()
    finally:
        st.close()
    keep(out, st)
    lc = analyse.leak_check(view, token)
    sc = analyse.schema_check(view, K, F, Q)
    R.raw.update(view=view, leak=lc, schema_defects=sc["n_defects"])
    R.check("H4 CONTROL fires: with a free-text field passed through, the receiver recovers the token in one record "
            "(free_text_leaks)", {"token_in_view": True}, lc, lc["token_in_view"])
    R.check("and that record fails the schema check (an extra free field is present)", True, sc["n_defects"] >= 1,
            sc["n_defects"] >= 1)


H = {"H1": h1, "H2": h2, "H3": h3, "H4": h4}


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
    vals = {k: float(v) for k, v in re.findall(r"^(N_TOKENS) = ([0-9.]+)\s*$", txt, re.M)}
    return {"status": st.group(1) if st else None, "prereg_values": vals,
            "harness_values": {"N_TOKENS": float(N_TOKENS)}}


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    models = ["ControlStack/Families/F2/ChannelInstances.lean"]
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
        "constants": {k: globals()[k] for k in ("K", "F", "Q", "FIELD_MAX", "N_TOKENS", "M_VALUES", "H1_RECORDS",
                                                 "LIFETIME", "WALL_LIMIT", "EPS")},
    }


def preflight(args, m):
    problems = []
    if sys.version_info < (3, 9):
        problems.append("python >= 3.9 required")
    if not sys.platform.startswith("linux"):
        problems.append("linux required")
    stale = proc_scan("/var/tmp/sc04-run-")
    if stale:
        problems.append("processes of an earlier sc04 run still alive: %s" % [e["pid"] for e in stale])
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
    lines = ["# SC-04 log canonicaliser (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- calibration: %s, N_TOKENS = %s, alphabet K*Q^f = %d" % (m["calibration"]["status"], N_TOKENS, K * Q ** F),
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
        if r["hyp"] == "H2":
            s = "; ".join("%s: acc %.4f <= bound %.4g (distinct views %d/%d)" % (
                k, v["best_decoder_acc"], v["bound"], v["distinct_views"], v["alphabet"])
                for k, v in raw.get("capacity", {}).items())
        elif r["hyp"] == "H1":
            s = "schema records %s, defects %s" % (raw.get("schema", {}).get("records"),
                                                 raw.get("schema", {}).get("n_defects"))
        elif r["hyp"] == "H4":
            s = "token recovered %s" % raw.get("leak", {}).get("token_in_view")
        else:
            s = "per-template counts match: %s" % (raw.get("raw_counts") == raw.get("canonical_counts"))
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
    ap = argparse.ArgumentParser(description="SC-04 log canonicaliser check (unprivileged).")
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
