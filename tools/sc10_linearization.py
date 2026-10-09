#!/usr/bin/env python3
"""Read-only SC-10 timestamp audit; not a runtime correspondence proof.

The policy store returns a version at t_answer; PEP produces a decision
at t_decide. The Lean abstract step is atomic. The original reconcile.py
evaluates freshness at t_answer only. This checker additionally tests
freshness at t_decide without rewriting frozen evidence.

Even when it passes, authentic/comprehensive trace capture, real UID
separation, policy effect mediation and storage/clock trust remain unproved.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def is_nat(x):
    return type(x) is int and x >= 0


def digest(policy):
    return hashlib.sha256(
        json.dumps(policy, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def audit(versions, decisions):
    """Return read-time and effect-time defects separately (fail closed)."""
    bad = []
    ordered = sorted(versions, key=lambda x: x.get("version", -1))
    for i, v in enumerate(ordered):
        if not (is_nat(v.get("version")) and v["version"] == i
                and is_nat(v.get("t_commit")) and v.get("writer") == "admin"
                and isinstance(v.get("policy"), dict)
                and v.get("digest") == digest(v["policy"])):
            bad.append({"kind": "invalid_store_version", "index": i})
    timestamps = [v.get("t_commit") for v in ordered]
    if (any(not is_nat(t) for t in timestamps) or
            timestamps != sorted(timestamps) or
            len(set(timestamps)) != len(timestamps)):
        bad.append({"kind": "invalid_commit_order"})
    read_bad = effect_bad = 0
    for i, d in enumerate(decisions):
        t_read, t_effect = d.get("t_answer"), d.get("t_decide")
        if not is_nat(t_read) or not is_nat(t_effect) or t_effect < t_read:
            bad.append({"kind": "invalid_timestamps", "decision": i})
            continue
        read = [v for v in ordered if is_nat(v.get("t_commit")) and v["t_commit"] <= t_read]
        effect = [v for v in ordered if is_nat(v.get("t_commit")) and v["t_commit"] <= t_effect]
        at_read, at_effect = (read[-1] if read else None), (effect[-1] if effect else None)
        if at_read is None or d.get("version") != at_read["version"]:
            read_bad += 1
            bad.append({"kind": "not_latest_at_read", "decision": i})
        if at_effect is None or d.get("version") != at_effect["version"]:
            effect_bad += 1
            bad.append({"kind": "not_latest_at_effect", "decision": i})
        if at_read is not None:
            expected = "allow" if d.get("host") in at_read["policy"].get("allow", []) else "deny"
            if (d.get("digest") != at_read["digest"] or
                    d.get("length") != at_read["version"] + 1 or
                    d.get("decision") != expected):
                bad.append({"kind": "reply_policy_mismatch", "decision": i})
        if d.get("config") != {"cache_ttl": None, "alt_file": False}:
            bad.append({"kind": "not_deployed_configuration", "decision": i})
    return {
        "versions": len(versions), "decisions": len(decisions),
        "read_mismatches": read_bad, "effect_mismatches": effect_bad,
        "defects": bad, "ok": not bad,
    }


def read_store(path):
    versions, commits = [], {}
    for line in Path(path).read_text().splitlines():
        if not line.strip():
            continue
        record = json.loads(line)
        if "commit" in record:
            n = record["commit"]
            if n in commits:
                raise ValueError("duplicate commit marker")
            commits[n] = record["t"]
        else:
            versions.append(record)
    for v in versions:
        v["t_commit"] = commits.pop(v["version"], None)
    if commits:
        raise ValueError("unpaired commit markers")
    return versions


def read_decisions(path):
    return [json.loads(x) for x in Path(path).read_text().splitlines() if x.strip()]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--store", type=Path, required=True)
    p.add_argument("--decisions", type=Path, required=True)
    args = p.parse_args()
    report = audit(read_store(args.store), read_decisions(args.decisions))
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
