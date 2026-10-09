#!/usr/bin/env python3
"""Strict SC-08 launcher/sentinel reconciliation (supplementary, not frozen evidence).

The original run-1 evidence and its checker remain immutable. This checker
closes completeness gaps in the original *reconciliation*: a missing digest in
an executed launcher entry was not rejected, and the launcher/sentinel digests
were not compared as multisets. It does NOT establish complete syscall
mediation, signal authenticity or that sentinel self-reading equals executed
bytes. Treat it as a fail-closed defensive check on trusted log inputs.
"""
from collections import Counter
import json
from pathlib import Path
import re

DIGEST = re.compile(r"^[0-9a-f]{64}$")


def _hex(x):
    return isinstance(x, str) and DIGEST.fullmatch(x) is not None


def reconcile_v2(allow, launcher, sentinel, *, pin_dir=None):
    """Return a detailed result without asserting anything about live kernel events."""
    findings = []
    if not isinstance(allow, dict) or not isinstance(launcher, list) or not isinstance(sentinel, list):
        return {"ok": False, "findings": ["invalid record container"], "executions": 0, "sentinel_records": 0}
    if not isinstance(pin_dir, str) or not Path(pin_dir).is_absolute():
        findings.append("trusted absolute pin directory was not supplied")
    progs = allow.get("interpreters")
    scripts = allow.get("scripts")
    if not isinstance(progs, list) or not isinstance(scripts, list) or not all(map(_hex, progs + scripts)):
        findings.append("allowlist contains missing or invalid SHA-256 digests")
        progs, scripts = [], []
    all_seq = []
    successful = []
    for i, entry in enumerate(launcher):
        if not isinstance(entry, dict):
            findings.append(f"launcher[{i}]: not an object")
            continue
        seq = entry.get("seq")
        if not isinstance(seq, int) or isinstance(seq, bool) or seq < 0:
            findings.append(f"launcher[{i}]: missing/invalid sequence")
        else:
            all_seq.append(seq)
        if entry.get("decision") != "executed":
            continue
        pd, sd = entry.get("program_digest"), entry.get("script_digest")
        if not _hex(pd) or pd not in progs:
            findings.append(f"launcher[{i}]: executed program digest missing or not allowlisted")
        if entry.get("script") is None or not _hex(sd) or sd not in scripts:
            findings.append(f"launcher[{i}]: executed script digest missing or not allowlisted")
        pin = entry.get("executed_path")
        if (not isinstance(pin, str) or not Path(pin).is_absolute() or not _hex(sd)
                or not isinstance(pin_dir, str) or not Path(pin_dir).is_absolute()
                or Path(pin).resolve(strict=False) != (Path(pin_dir) / (sd + ".py")).resolve(strict=False)):
            findings.append(f"launcher[{i}]: executed script path does not match its trusted pin directory and digest")
        rc = entry.get("rc")
        if rc != 0 or isinstance(rc, bool):
            findings.append(f"launcher[{i}]: execution did not exit successfully")
        else:
            if _hex(sd):
                successful.append(sd)
    if all_seq != sorted(set(all_seq)):
        findings.append("launcher sequences are duplicated or out of order")
    received = []
    for i, entry in enumerate(sentinel):
        if not isinstance(entry, dict):
            findings.append(f"sentinel[{i}]: not an object")
            continue
        d = entry.get("self_sha256")
        if not _hex(d) or d not in scripts:
            findings.append(f"sentinel[{i}]: executed code digest missing or not allowlisted")
        if _hex(d):
            received.append(d)
    if Counter(successful) != Counter(received):
        findings.append("successful launcher script digests do not match sentinel self-hashes as a multiset")
    return {"ok": not findings, "findings": findings,
            "executions": sum(isinstance(x, dict) and x.get("decision") == "executed" for x in launcher),
            "sentinel_records": len(sentinel)}


def main():
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument("allowlist")
    p.add_argument("launcher_jsonl")
    p.add_argument("sentinel_jsonl")
    p.add_argument("--pin-dir", required=True, help="trusted launcher-owned directory used for digest-named scripts")
    a = p.parse_args()
    allow = json.loads(Path(a.allowlist).read_text())
    def records(path):
        return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]
    verdict = reconcile_v2(allow, records(a.launcher_jsonl), records(a.sentinel_jsonl), pin_dir=a.pin_dir)
    print(json.dumps(verdict, sort_keys=True, indent=2))
    return 0 if verdict["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
