#!/usr/bin/env python3
"""cstack: one front door for researchers. It dispatches to the existing tools and never duplicates their logic.

    python3 tools/cstack.py status [SC-XX]                    portfolio table, or one scenario in detail
    python3 tools/cstack.py check [--fast|--full] [--list] [--only NAME]
                                                              the local check suite; compact table; nonzero on failure
    python3 tools/cstack.py ledger [--portfolio|--stack|--lab] [extra args]
                                                              typed ledgers (portfolio_ledger / cert_ledger)
    python3 tools/cstack.py new SC-XX spec.json [--dry-run]   tools/new_scenario.py
    python3 tools/cstack.py evidence SC-XX                    preregs, frozen status, pinned-hash verification per
                                                              evidence run (against the pinned commit, via git show)
    python3 tools/cstack.py map [--gaps | --researcher COMPONENT] [extra args]
                                                              tools/stackmap.py

Sources: `status` reads manifests and calls build_results (theorem one-liners, evidence summaries, done criteria) and
portfolio_ledger (normalised premises). Nothing here re-runs Lean or an experiment except `check --full`, and every
status shown is recorded metadata. Unknown scenario ids fail closed (exit 2).
Exit codes: 0 ok; 1 a check, pin or dispatched tool failed; 2 usage error or unknown scenario.
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "tools"
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SID_RE = re.compile(r"SC-\d\d")


class UsageError(Exception):
    pass


def _import(name):
    """import a sibling tool module (their imports assume tools/ or the repo root on sys.path)"""
    for p in (str(TOOLS), str(ROOT)):
        if p not in sys.path:
            sys.path.insert(0, p)
    return __import__(name)


# ---------------------------------------------------------------- scenarios

def manifests(root=ROOT):
    out = {}
    for f in sorted((root / "scenarios").glob("SC-*/manifest.json")):
        m = json.loads(f.read_text(encoding="utf-8"))
        out[m["id"]] = m
    return out


def require_sid(sid, root=ROOT):
    """fail closed on anything that is not an existing scenario id"""
    if not isinstance(sid, str) or not SID_RE.fullmatch(sid):
        raise UsageError(f"not a scenario id: {sid!r} (expected SC-NN)")
    ms = manifests(root)
    if sid not in ms:
        raise UsageError(f"unknown scenario {sid}; known: {', '.join(sorted(ms))}")
    return ms[sid]


def evidence_runs(m, root=ROOT):
    """evidence run directories of a scenario: its own scenarios/SC-XX/evidence/run-* plus any run directory a manifest
    evidence entry cites (e.g. experiments/.../evidence/run-1)"""
    runs = set()
    d = root / "scenarios" / m["id"] / "evidence"
    if d.is_dir():
        runs |= {p for p in d.iterdir() if p.is_dir() and p.name.startswith("run-")}
    for e in m.get("evidence", []):
        mt = re.match(r"(.*/evidence/run-[^/]+)/", e.get("path", ""))
        if mt and (root / mt.group(1)).is_dir():
            runs.add(root / mt.group(1))
    return sorted(runs)


def run_verdict(run):
    for name in ("verdicts.json", "receipt.json"):
        f = run / name
        if f.is_file():
            try:
                d = json.loads(f.read_text(encoding="utf-8"))
            except ValueError:
                return "UNREADABLE"
            v = d.get("overall") or d.get("overall_gated") or d.get("verdict") or d.get("status")
            if v is None and isinstance(d.get("phases"), dict):
                vs = {str(p.get("verdict")) for p in d["phases"].values() if isinstance(p, dict)}
                v = "PASS" if vs and vs <= {"PASS"} else ",".join(sorted(vs)) or None
            return str(v) if v is not None else "NO_VERDICT"
    return "NO_VERDICT_FILE"


def status_portfolio(root=ROOT):
    br = _import("build_results")
    lines = ["| scenario | status | theorems | evidence runs | latest run | done criteria (R/P/A/O/X) |",
             "|---|---|---|---|---|---|"]
    for sid, m in manifests(root).items():
        runs = evidence_runs(m, root)
        latest = f"{runs[-1].name}: {run_verdict(runs[-1])}" if runs else "—"
        summ = {e["path"]: br.summarise_json(e["path"]) for e in m["evidence"] if e["path"].endswith(".json")}
        dc = br.done_criteria(m, summ)
        count = {k: sum(1 for _, s, _ in dc if s == k) for k in ("RECORDED", "PARTIAL", "ASSUMED", "OPEN", "REFUTED")}
        lines.append(f"| {sid} | {m['status']} | {len(m['theorems'])} | {len(runs)} | {latest} | "
                     + "/".join(str(count[k]) for k in ("RECORDED", "PARTIAL", "ASSUMED", "OPEN", "REFUTED")) + " |")
    return "\n".join(lines)


def status_scenario(sid, root=ROOT):
    m = require_sid(sid, root)
    br = _import("build_results")
    L = [f"{sid}: {m['title']}", f"status: {m['status']}", f"bad event: {m['bad_event']}", "", "theorems:"]
    for t in m["theorems"]:
        name, doc = br.find_decl(t["name"], t["path"])
        L.append(f"  - {t['name']}  ({t['path']})")
        if doc:
            L.append(f"      {doc}")
    L += ["", "evidence (manifest):"]
    summ = {}
    for e in m["evidence"]:
        s = br.summarise_json(e["path"]) if e["path"].endswith(".json") else None
        summ[e["path"]] = s
        extra = f" [{s[0] or '?'}: {s[1]}]" if s else ""
        L.append(f"  - {e.get('outcome', '?'):8} {e['path']}{extra}")
    runs = evidence_runs(m, root)
    L += ["", "evidence runs:"] + ([f"  - {r.relative_to(root)}: {run_verdict(r)}" for r in runs] or ["  (none)"])
    L += ["", "open premises (manifest assumptions not ESTABLISHED; normalised id from the portfolio ledger):"]
    owner = {}
    try:
        pl = _import("portfolio_ledger")
        for row in pl.build(root):
            for mem in row["members"]:
                owner[mem] = row["id"]
    except Exception as e:  # the ledger is fail-closed; show why rather than hide it
        L.append(f"  (portfolio ledger unavailable: {e})")
    for a in m["assumptions"]:
        if a.get("applicability") != "ESTABLISHED":
            norm = owner.get(f"{sid}:{a['id']}", "?")
            L.append(f"  - {a['id']} [{norm}] proof={a.get('proof')} evidence={a.get('evidence')} "
                     f"applicability={a.get('applicability')}")
    L += ["", "done criteria (RUNTIME-VM-HANDOFF §10; never reported as met):"]
    for i, (n, s, b) in enumerate(br.done_criteria(m, summ), 1):
        L.append(f"  {i}. {s:9} {n} — {b}")
    return "\n".join(L)


def portfolio_table(root=ROOT):
    """normalised premises from portfolio_ledger.build (no Lean), highest leverage first"""
    pl = _import("portfolio_ledger")
    rows = sorted(pl.build(root), key=lambda r: (-r["leverage"], r["id"]))
    L = ["| premise | kind | scenarios | best proof | best evidence | tested in | leverage |",
         "|---|---|---|---|---|---|---|"]
    for r in rows:
        L.append(f"| {r['id']} | {r['kind']} | {len(r['scenarios'])} | {r['best_proof']} | {r['best_evidence']} | "
                 f"{', '.join(r['tested_in']) or '—'} | {r['leverage']} |")
    L.append(f"\n{len(rows)} normalised premises. Full ledger: docs/ASSURANCE-LEDGER.md; JSON: "
             "cstack ledger --portfolio --json --no-lean")
    return "\n".join(L)


# ---------------------------------------------------------------- check

def check_steps(full=False, root=ROOT):
    """(name, argv, expected return codes) of the local suite; `full` adds Lean"""
    py = sys.executable
    steps = [
        ("registry --check", [py, "tools/build_registry.py", "--check"], {0}),
        ("status index --check", [py, "tools/build_status.py", "--check"], {0}),
        ("statement catalog --check", [py, "tools/build_statement_catalog.py", "--check"], {0}),
        ("results pages --check", [py, "tools/build_results.py", "--check"], {0}),
        ("overview --check", [py, "tools/build_overview.py", "--check"], {0}),
        ("assurance ledger --check" + ("" if full else " (no Lean)"),
         [py, "tools/portfolio_ledger.py", "--check"] + ([] if full else ["--no-lean"]), {0}),
        ("trust-root table --check" + ("" if full else " (no Lean)"),
         [py, "tools/gen_trust_root.py", "--check"] + ([] if full else ["--no-lean"]), {0}),
        ("stackmap --validate", [py, "tools/stackmap.py", "--validate"], {0}),
        ("check_scenarios", [py, "tools/check_scenarios.py"], {0}),
        ("test_check_scenarios", [py, "-m", "unittest", "tools.test_check_scenarios"], {0}),
    ]
    for t in sorted((root / "tools").glob("test_*.py")):
        if t.name in ("test_check_scenarios.py", "test_trusted_stack_broker.py"):
            continue  # the former runs as a module above; the latter needs root (CI runs it)
        steps.append((t.stem, [py, f"tools/{t.name}"], {0}))
    if full:
        steps.append(("lake build ControlStack", ["lake", "build", "ControlStack"], {0}))
        for c in sorted((root / "scenarios").glob("SC-*/claim.lean")):
            steps.append((f"claim {c.parent.name}", ["lake", "env", "lean", str(c.relative_to(root))], {0}))
        steps.append(("check_sc26_case", [py, "tools/check_sc26_case.py"], {0}))
    else:
        steps.append(("check_sc26_case --skip-lean", [py, "tools/check_sc26_case.py", "--skip-lean"], {0}))
    return steps


def axioms_ok(text):
    """a claim's `#print axioms` lines show standard axioms only, and there is no error or sorry"""
    reports = re.findall(r"depends on axioms: \[([^\]]*)\]", text)
    bad = [r for r in reports if {x.strip() for x in r.split(",") if x.strip()} - STD_AXIOMS]
    seen = reports or re.findall(r"does not depend on any axioms", text)
    return bool(seen) and not bad and "error:" not in text and "sorryAx" not in text


def run_check(full=False, only=None, root=ROOT, runner=subprocess.run, out=sys.stdout):
    steps = [s for s in check_steps(full, root) if only is None or only in s[0]]
    if not steps:
        raise UsageError(f"no check step matches {only!r}")
    rows, failed = [], []
    for name, argv, ok_rc in steps:
        t0 = time.monotonic()
        try:
            env = dict(os.environ, PYTHONPATH=str(root) + os.pathsep + os.environ.get("PYTHONPATH", ""))
            p = runner(argv, cwd=root, capture_output=True, text=True, timeout=7200, env=env)
            rc, text = p.returncode, (p.stdout or "") + (p.stderr or "")
        except (OSError, subprocess.TimeoutExpired) as e:
            rc, text = -1, str(e)
        ok = rc in ok_rc and (not name.startswith("claim ") or axioms_ok(text))
        dt = time.monotonic() - t0
        rows.append((name, "PASS" if ok else "FAIL", rc, dt))
        if not ok:
            failed.append((name, text))
    w = max(len(r[0]) for r in rows)
    print(f"{'step'.ljust(w)}  result  rc   seconds", file=out)
    for name, res, rc, dt in rows:
        print(f"{name.ljust(w)}  {res:6}  {rc:<4} {dt:7.1f}", file=out)
    print(f"\n{len(rows) - len(failed)}/{len(rows)} passed ({'full' if full else 'fast'} suite)", file=out)
    for name, text in failed:
        tail = "\n".join(text.strip().splitlines()[-15:])
        print(f"\n--- {name} (last lines) ---\n{tail}", file=out)
    return 1 if failed else 0


# ---------------------------------------------------------------- evidence

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def git(args, root=ROOT):
    return subprocess.run(["git"] + args, cwd=root, capture_output=True)


def git_blob_sha(commit, path, root=ROOT):
    p = git(["show", f"{commit}:{path}"], root)
    return hashlib.sha256(p.stdout).hexdigest() if p.returncode == 0 else None


def commit_exists(commit, root=ROOT):
    return bool(commit) and git(["cat-file", "-e", f"{commit}^{{commit}}"], root).returncode == 0


def path_at(commit, path, root=ROOT):
    return git(["cat-file", "-e", f"{commit}:{path}"], root).returncode == 0


def prereg_status(path, text):
    """declared freeze status from the file's own header (the conventions differ between preregs)"""
    head = "\n".join(text.splitlines()[:12])
    if re.search(r"Status:\**\s*FROZEN", head):
        return "FROZEN (declared)"
    if "DRAFT" in head or "DRAFT" in path.name or re.search(r"Draft only", head):
        return "DRAFT"
    if "**Freeze:**" in head or re.search(r"(Harness commit|^Commit): `[0-9a-f]{40}`", text, re.M):
        return "FREEZE-ON-RUN (frozen once a receipt records its hash)"
    return "UNSTATED"


def prereg_info(root=ROOT):
    """prereg path -> (id, declared status, sha256)"""
    out = {}
    for f in sorted((root / "prereg").glob("*.md")):
        text = f.read_text(encoding="utf-8")
        m = re.search(r"\*\*ID:\*\*\s*`([^`]+)`", text)
        out[f] = (m.group(1) if m else None, prereg_status(f, text), hashlib.sha256(f.read_bytes()).hexdigest())
    return out


def find_prereg(h, commit, root=ROOT):
    """the prereg path whose content hashes to h: in the working tree, else at the run's commit"""
    for f, (_, _, fh) in prereg_info(root).items():
        if fh == h:
            return str(f.relative_to(root))
    if commit_exists(commit, root):
        names = git(["ls-tree", "--name-only", commit, "prereg/"], root).stdout.decode().split()
        for n in names:
            if n.endswith(".md") and git_blob_sha(commit, n, root) == h:
                return n
    return None


def dirty_note(dirty):
    """the run's recorded `git status` (informational; the pin check is what matters)"""
    if dirty in ("", False):
        return "clean"
    if not dirty:
        return "not recorded"
    items = [x.strip() for x in str(dirty).splitlines() if x.strip()]
    return f"dirty, {len(items)} path(s): " + "; ".join(items[:4]) + ("; ..." if len(items) > 4 else "")


def run_pins(run, root=ROOT):
    """(prereg id, dirty note, groups) for one evidence run; each group is (source, commit, {path: recorded sha}).
    meta.json: git_commit + sha256 map. receipt.json: git commit + prereg_sha256 + harness/code hashes (names resolved
    against the run's harness directory at that commit), plus the prereg's own pin table at its `Harness commit:` /
    `Commit:`. Hashes of bundles that are not files (prompts, the Lean model) are left to the case rechecker."""
    meta = run / "meta.json"
    if meta.is_file():
        d = json.loads(meta.read_text(encoding="utf-8"))
        pins = {p: h for p, h in (d.get("sha256") or {}).items() if not p.startswith("<")}
        dirty = d.get("git_status_harness_and_prereg")
        return d.get("prereg_id"), dirty_note(dirty), [("meta.json", d.get("git_commit"), pins)]
    rec = run / "receipt.json"
    if not rec.is_file():
        return None, "no meta.json or receipt.json", []
    d = json.loads(rec.read_text(encoding="utf-8"))
    g = d.get("git") if isinstance(d.get("git"), dict) else {}
    commit = d.get("git_commit") or g.get("commit")
    dirty = g.get("status", g.get("dirty")) if g else next((v for k, v in d.items() if k.startswith("git_dirty")), None)
    note = dirty_note(dirty)
    pins, pid, groups = {}, d.get("prereg_id"), []
    pre = find_prereg(d.get("prereg_sha256"), commit, root) if d.get("prereg_sha256") else None
    if pre:
        pins[pre] = d["prereg_sha256"]
    elif d.get("prereg_sha256"):
        pins["<prereg not found by hash>"] = d["prereg_sha256"]
    base = run.parent.parent.relative_to(root)
    for key in ("harness_sha256", "code_sha256"):
        for name, h in (d.get(key) or {}).items():
            cands = [str(base / name), str(base / "harness" / name)]
            hit = [c for c in cands if commit_exists(commit, root) and path_at(commit, c, root)]
            pins[hit[0] if len(hit) == 1 else cands[0]] = h
    groups.append(("receipt.json", commit, pins))
    if pre and (root / pre).is_file():
        text = (root / pre).read_text(encoding="utf-8")
        pid = pid or (re.search(r"\*\*ID:\*\*\s*`([^`]+)`", text) or [None, None])[1]
        c = re.search(r"(?:Harness commit|^Commit): `([0-9a-f]{40})`", text, re.M)
        table = dict(re.findall(r"\| `([^`]+)` \| `([0-9a-f]{64})` \|", text))
        if table:
            groups.append((f"{pre} pin table", c.group(1) if c else None, table))
    return pid, note, groups


def verify_run(run, root=ROOT):
    """verify every pinned hash against its pinned commit (git show); the working tree comparison is informational.
    Returns (ok, lines, recorded {path: sha})."""
    try:
        pid, note, groups = run_pins(run, root)
    except (OSError, ValueError) as e:
        return False, [f"    UNREADABLE run metadata: {e}"], {}
    L = [f"    prereg: {pid or '?'}; tree at run: {note}"]
    if not groups:
        return False, L + ["    UNVERIFIABLE: no pinned hashes"], {}
    ok, recorded = True, {}
    for src, commit, pins in groups:
        L.append(f"    [{src}] commit {commit or 'NONE'}, {len(pins)} pinned file(s)")
        if not commit or not pins:
            ok = False
            L.append("      UNVERIFIABLE: no pinned commit or no pinned hashes")
            continue
        if not commit_exists(commit, root):
            ok = False
            L.append(f"      UNVERIFIABLE: commit {commit[:12]} is not in this clone (git fetch?)")
            continue
        for path, h in sorted(pins.items()):
            recorded[path] = h
            at = None if path.startswith("<") else git_blob_sha(commit, path, root)
            if at is None:
                ok, res = False, "MISSING_AT_COMMIT"
            elif at != h:
                ok, res = False, "MISMATCH"
            else:
                res = "OK"
            cur = sha(root / path) if not path.startswith("<") and (root / path).is_file() else None
            tree = "unchanged" if cur == h else ("evolved" if cur else "absent")
            L.append(f"      {res:17} {path} (working tree: {tree})")
    return ok, L, recorded


def standalone_usage(f):
    m = re.search(r"Standalone:\s*(python3 .*)", f.read_text(encoding="utf-8", errors="replace"))
    return m.group(1).strip() if m else None


def recheck_commands(sid, runs, root=ROOT):
    cmds = [f"python3 tools/cstack.py evidence {sid}   # this pin verification"]
    tool = root / "tools" / f"check_{sid.lower().replace('-', '')}_case.py"
    top = root / "scenarios" / sid / "evidence"
    if tool.is_file():
        rel = tool.relative_to(root)
        if "--run" in tool.read_text(encoding="utf-8"):
            cmds += [f"python3 {rel} --run {r.name}   # independent rechecker" for r in runs if r.parent == top]
        else:
            cmds.append(f"python3 {rel}   # independent rechecker")
    for r in sorted({r.parent.parent for r in runs}):
        for f in sorted(r.rglob("*.py")):
            if "evidence" in f.parts:
                continue
            if f.name.startswith("test_"):
                cmds.append(f"python3 -m unittest discover -s {f.parent.relative_to(root)} -p 'test_*.py'"
                            "   # harness unit tests (current tree)")
            elif f.name in ("reconcile.py", "check_trace.py", "ci_check.py"):
                use = standalone_usage(f)
                cmds.append(f"{f.relative_to(root)}: {use or 'see its docstring'}   # raw-data checker; needs the "
                            "run's workdir, which evidence/ does not keep")
    return list(dict.fromkeys(cmds))


def evidence(sid, root=ROOT, out=sys.stdout):
    m = require_sid(sid, root)
    num = sid.split("-")[1]
    info = prereg_info(root)
    cited = {root / e["path"] for e in m["evidence"]}
    runs = evidence_runs(m, root)
    results = [(r, verify_run(r, root)) for r in runs]
    pre = [f for f in info if f.name.startswith(f"SC{num}") or f in cited
           or any(str(f.relative_to(root)) in rec for _, (_, _, rec) in results)]
    print(f"{sid} preregistrations:", file=out)
    for f in pre:
        pid, st, h = info[f]
        rel = str(f.relative_to(root))
        by = [r.name if r.parent.parent.name == sid else str(r.relative_to(root))
              for r, (_, _, rec) in results if rec.get(rel)]
        same = all(rec.get(rel) == h for _, (_, _, rec) in results if rec.get(rel))
        runs_note = f"; recorded by {', '.join(by)} ({'unchanged since' if same else 'CHANGED since'})" if by else ""
        print(f"  - {rel}  id={pid or '?'}  status={st}{runs_note}", file=out)
    if not pre:
        print("  (none)", file=out)
    print(f"\n{sid} evidence runs:", file=out)
    all_ok = True
    for r, (ok, lines, _) in results:
        all_ok &= ok
        print(f"  - {r.relative_to(root)}  verdict={run_verdict(r)}  pins={'OK' if ok else 'FAIL'}", file=out)
        for ln in lines:
            print(ln, file=out)
    if not runs:
        print("  (none)", file=out)
    print("\nrecheck:", file=out)
    for c in recheck_commands(sid, runs, root):
        print(f"  {c}", file=out)
    return 0 if all_ok else 1


# ---------------------------------------------------------------- dispatch

def dispatch(argv, runner=subprocess.call):
    return runner([sys.executable] + argv, cwd=ROOT)


def main(argv=None, runner=subprocess.call):
    ap = argparse.ArgumentParser(prog="cstack", description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("status")
    s.add_argument("sid", nargs="?")
    c = sub.add_parser("check")
    g = c.add_mutually_exclusive_group()
    g.add_argument("--fast", action="store_true")
    g.add_argument("--full", action="store_true")
    c.add_argument("--list", action="store_true", help="list the steps, run nothing")
    c.add_argument("--only", help="run only steps whose name contains this text")
    lg = sub.add_parser("ledger")
    g2 = lg.add_mutually_exclusive_group()
    g2.add_argument("--portfolio", action="store_true")
    g2.add_argument("--stack", action="store_true")
    g2.add_argument("--lab", action="store_true")
    n = sub.add_parser("new")
    n.add_argument("sid")
    n.add_argument("spec")
    e = sub.add_parser("evidence")
    e.add_argument("sid")
    mp = sub.add_parser("map")
    g3 = mp.add_mutually_exclusive_group()
    g3.add_argument("--gaps", action="store_true")
    g3.add_argument("--researcher", metavar="COMPONENT")
    scan = sub.add_parser("scan", help="read-only normalized Compose JSON collector")
    scan.add_argument("compose")
    scan.add_argument("--runtime", required=True)
    scan.add_argument("--sha256", required=True, help="expected Compose file hash")
    scan.add_argument("--output", required=True)
    verify = sub.add_parser("verify", help="emit a scoped obligation bundle")
    verify.add_argument("ir")
    verify.add_argument("--output", required=True)
    verify.add_argument("--boundary-evidence", help="check raw archived native reference sink evidence; does not attest Compose")
    verify.add_argument("--lean", action="store_true", help="kernel-check the exact IR projection and contracts")
    report = sub.add_parser("report", help="render an obligation bundle")
    report.add_argument("bundle")
    report.add_argument("--output", required=True)
    a, extra = ap.parse_known_args(argv)
    if extra and a.cmd not in ("ledger", "new", "map"):
        ap.error(f"unrecognized arguments: {' '.join(extra)}")
    try:
        if a.cmd in ("scan", "verify", "report"):
            _import("security_ir")
            from extractors.compose import collect
            from security_ir.verifier import verify, report
            try:
                if a.cmd == "scan":
                    result = collect(a.compose, a.runtime, a.sha256)
                elif a.cmd == "verify":
                    ir = json.loads(Path(a.ir).read_text())
                    result = verify(ir)
                    if a.lean:
                        from tools.check_deployment_lean import check
                        checked = check(ir)
                        result["lean"] = checked
                        result["scope"] = "Kernel-checked finite model candidate; CONDITIONAL retains runtime faithfulness; no deployment-assured result"
                        for o in result["obligations"]:
                            if o["premise"] == "Lean-contract-instances":
                                o.update(status="PROVEN_IN_MODEL" if checked["accepted"] else "REFUTED",
                                         detail=checked["axioms"])
                        if not checked["accepted"]:
                            result["verdict"] = "UNASSURED"
                    if a.boundary_evidence:
                        from tools.check_deployment_evidence import check as check_boundary
                        check_boundary(a.boundary_evidence)
                        result["obligations"].append({"premise":"native-reference-boundary","status":"TESTED_BOUNDARY",
                            "detail":"Independent raw sink evidence at " + a.boundary_evidence + "; confined two-agent budget/replay, HALT during publication, writable-sink and UID-collision negatives. Native Linux guest test of pinned sources; does not attest this Compose inventory."})
                else:
                    result = report(json.loads(Path(a.bundle).read_text()))
                Path(a.output).write_text(result if isinstance(result,str) else json.dumps(result,sort_keys=True,indent=2)+"\n")
                return 1 if a.cmd == "verify" and result["verdict"] == "UNASSURED" else 0
            except (ValueError, OSError, TypeError, KeyError, AssertionError) as err:
                raise UsageError(str(err)) from err
        if a.cmd == "status":
            print(status_scenario(a.sid) if a.sid else status_portfolio())
            return 0
        if a.cmd == "check":
            if a.list:
                for name, argv_, _ in check_steps(a.full):
                    shown = ["python3" if x == sys.executable else x for x in argv_]
                    print(f"{name:36} {' '.join(shown)}")
                return 0
            return run_check(full=a.full, only=a.only)
        if a.cmd == "ledger":
            if a.stack:
                return dispatch(["tools/cert_ledger.py"] + extra, runner)
            if a.lab:
                return dispatch(["tools/cert_ledger.py", "--import", "ControlStack.Scenarios.LabStack",
                                 "--ledger", "ControlStack.LabStack.labLedger"] + extra, runner)
            if extra:  # portfolio_ledger without --check/--json rewrites ASSURANCE-LEDGER.md: never via cstack
                if not {"--json", "--check"} & set(extra):
                    raise UsageError("ledger --portfolio passes only --json/--check/--no-lean to portfolio_ledger.py "
                                     "(regenerate the ledger file with the tool itself)")
                return dispatch(["tools/portfolio_ledger.py"] + extra, runner)
            print(portfolio_table())
            return 0
        if a.cmd == "new":
            if not SID_RE.fullmatch(a.sid):
                raise UsageError(f"not a scenario id: {a.sid!r} (expected SC-NN)")
            if a.sid in manifests():
                raise UsageError(f"{a.sid} already exists")
            return dispatch(["tools/new_scenario.py", a.sid, a.spec] + extra, runner)
        if a.cmd == "evidence":
            return evidence(a.sid)
        if a.cmd == "map":
            mode = ["--gaps"] if a.gaps else (["--researcher", a.researcher] if a.researcher else [])
            return dispatch(["tools/stackmap.py"] + mode + extra, runner)
    except UsageError as err:
        print(f"cstack: {err}", file=sys.stderr)
        return 2
    return 2


if __name__ == "__main__":
    sys.exit(main())
