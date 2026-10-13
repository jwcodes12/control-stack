#!/usr/bin/env python3
"""Run (or verify) one strictly blind one-to-one batch from docs/lean-english/one-to-one/BLIND-PLAN.json.

  run    --tag g0n1 [--work DIR]   phase A (isolated dir) -> transcript audit -> phase B (clean checkout) with Sol (`codex exec`)
  verify --tag g0n1 [--work DIR]   re-run the batch's regate.py independently, check the freeze-before-open ordering in the event logs,
                                   and write VERIFY.json
Needs codex on PATH, the pinned Lean toolchain (~/.elan/bin) and a prebuilt ControlStack .lake/build, given by --build-dir.
It never edits the main checkout; results stay under --work until the caller imports them.
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PLAN = ROOT / "docs/lean-english/one-to-one/BLIND-PLAN.json"
MODEL = ["-m", "gpt-6.1-sol", "-c", "model_reasoning_effort=high"]


def sh(argv, **kw):
    return subprocess.run([str(a) for a in argv], text=True, capture_output=True, **kw)


def codex(prompt_file, cwd, events, last, timeout):
    prompt = Path(prompt_file).read_text()
    with open(events, "w") as ev, open(str(events) + ".err", "w") as err:
        p = subprocess.run(["codex", "exec", *MODEL, "-C", str(cwd), "--skip-git-repo-check", "--sandbox", "workspace-write", "--json",
                            "-o", str(last), prompt], stdin=subprocess.DEVNULL, stdout=ev, stderr=err, timeout=timeout)
    return p.returncode


def commands(events):
    out = []
    for line in Path(events).read_text().splitlines():
        try:
            e = json.loads(line)
        except ValueError:
            continue
        it = e.get("item", {})
        if it.get("type") == "command_execution" and e.get("type") == "item.started":
            out.append(it["command"])
    return out


def batch(tag):
    for b in json.loads(PLAN.read_text()):
        if b["tag"] == tag:
            return b["claims"]
    sys.exit("unknown tag " + tag)


def run(a):
    claims = batch(a.tag)
    work = Path(a.work).expanduser() / a.tag
    if work.exists():
        sys.exit(f"{work} exists")
    pa, pb = work / "a", work / "b"
    work.mkdir(parents=True)
    sh([sys.executable, ROOT / "tools/blind_one_to_one.py", "phase-a", "--claims", *claims, "--out", pa], check=True)
    sh([sys.executable, ROOT / "tools/blind_one_to_one.py", "prompts", "--out", pa, "--tag", a.tag], check=True)
    rc = codex(pa / "PROMPT-A.md", pa, work / "A-events.jsonl", work / "A-last.txt", 3 * 3600)
    names = [c.split(".")[-1] for c in claims]
    audit = sh([sys.executable, ROOT / "tools/audit_blind_phase.py", work / "A-events.jsonl", "--names", *names])
    (work / "A-AUDIT.txt").write_text(audit.stdout)
    hashes = pa / "back/BACK-HASHES.json"
    ok = rc == 0 and audit.returncode == 0 and hashes.exists()
    if ok:
        h = json.loads(hashes.read_text())["files"]
        ok = len(h) == len(claims) and all(hashlib.sha256((pa / "back" / f.split("/", 1)[1]).read_bytes()).hexdigest() == d for f, d in h.items())
    if not ok:
        sys.exit(f"phase A failed or not clean (rc={rc}, audit={audit.returncode}); see {work}")
    # Phase B checkout: a clean clone of the current branch, prebuilt objects linked, old results and other docs removed.
    branch = sh(["git", "-C", ROOT, "rev-parse", "--abbrev-ref", "HEAD"]).stdout.strip()
    sh(["git", "clone", "-q", "--branch", branch, ROOT, pb], check=True)
    (pb / ".lake").mkdir(exist_ok=True)
    os.symlink(Path(a.packages).expanduser(), pb / ".lake/packages")
    os.symlink(Path(a.build_dir).expanduser(), pb / ".lake/build")
    le = pb / "docs/lean-english"
    keep = {"one-to-one"}
    for f in le.iterdir():
        if f.name not in keep:
            shutil.rmtree(f) if f.is_dir() else f.unlink()
    oo = le / "one-to-one"
    for f in oo.iterdir():
        if f.name not in {"run_gate.py", "leangate_imports.py", "leangate-imports.patch"}:
            shutil.rmtree(f) if f.is_dir() else f.unlink()
    (pb / "docs/LEAN-CLAIMS-IN-PLAIN-ENGLISH.md").unlink(missing_ok=True)
    (le / "sol-input").mkdir()
    shutil.copy(pa / "input/batch.md", le / f"sol-input/batch-{a.tag}.md")
    bd = oo / f"blind-{a.tag}"
    shutil.copytree(pa / "back", bd / "back")
    shutil.copy(pa / "CLAIMS.txt", bd / "CLAIMS.txt")
    rc = codex(pa / "PROMPT-B.md", pb, work / "B-events.jsonl", work / "B-last.txt", 5 * 3600)
    (work / "DONE.json").write_text(json.dumps({"tag": a.tag, "claims": len(claims), "phase_b_rc": rc}) + "\n")
    print(f"{a.tag}: phase B exit {rc}; results in {bd}")


def verify(a):
    work = Path(a.work).expanduser() / a.tag
    bd = work / "b/docs/lean-english/one-to-one" / f"blind-{a.tag}"
    cmds = commands(work / "B-events.jsonl")
    freeze = next((i for i, c in enumerate(cmds) if "typed/HASHES.json" in c and re.search(r"write|dump|sha256|>", c)), None)
    opened = next((i for i, c in enumerate(cmds) if re.search(r"\b(cat|sed|nl|head|tail|rg|grep|less)\b", c) and re.search(r"(?<!!)ControlStack/[A-Za-z0-9_/]+\.lean", c)
                   and "lake env" not in c and not re.search(r"'!ControlStack", c)), None)
    env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
    before = {f.name: f.read_text() for f in bd.glob("*.receipt.json")}
    p = subprocess.run([sys.executable, str(bd / "regate.py")], cwd=work / "b", env=env, text=True, capture_output=True, timeout=7200)
    rows = []
    for f in sorted(bd.glob("*.receipt.json")):
        new = json.loads(f.read_text())
        old = json.loads(before.get(f.name, "{}") or "{}")
        w = f.name.replace(".receipt.json", ".witness-receipt.json")
        wr = json.loads((bd / w).read_text()) if (bd / w).exists() else {}
        rows.append({"id": f.name.split(".")[0], "claim_passed": new.get("passed"), "witness_passed": wr.get("passed"),
                     "same_hashes_as_sol": all(new.get(k) == old.get(k) for k in ("statement_sha256", "proof_sha256"))})
    result = {"tag": a.tag, "regate_exit": p.returncode, "freeze_command": freeze, "first_original_read": opened,
              "frozen_before_open": freeze is not None and opened is not None and freeze < opened, "gates": rows,
              "all_pass": p.returncode == 0 and bool(rows) and all(r["claim_passed"] and r["witness_passed"] for r in rows)}
    (work / "VERIFY.json").write_text(json.dumps(result, indent=1) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "gates"}), f"{len(rows)} gate receipts")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["run", "verify"])
    ap.add_argument("--tag", required=True)
    ap.add_argument("--work", default="~/projects/blind-work")
    ap.add_argument("--build-dir", default="/tmp/claude-1000/-home-opc/4ef840ee-1970-5e30-a456-ae46bb2676cb/scratchpad/wt-eventlog/.lake/build")
    ap.add_argument("--packages", default="~/research/control-stack/.lake/packages")
    a = ap.parse_args()
    run(a) if a.cmd == "run" else verify(a)


if __name__ == "__main__":
    main()
