#!/usr/bin/env python3
"""Read-only SC-10 clock reconciliation with explicit read/use race classification.

This checks recorded store/PEP event logs, not all enforcement paths. It does
not change frozen evidence or prove real firewall or Lean correspondence.
"""
import argparse
import hashlib
import json
from pathlib import Path


def _int_timestamp(v):
    return type(v) is int and v >= 0


def _digest(policy):
    return hashlib.sha256(json.dumps(policy, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def _jsonl(path):
    with open(path, encoding='utf-8') as f:
        return [json.loads(line) for line in f if line.strip()]


def check_trace(store_rows, decision_rows):
    """Audit an observed read/use interval; a crossing commit is ambiguous.

    The store's t_commit is taken after policy fsync. PEP's t_answer is
    store-read time and t_decide is logged AFTER computing the result. A
    commit inside the interval is NOT a proven violation: the actual decision
    computation time is not measured.
    """
    issues, ambiguous = [], []
    versions, stamps = {}, {}
    if not isinstance(store_rows, list) or not isinstance(decision_rows, list):
        return {'ok': False, 'issues': ['non-list evidence'], 'ambiguous': [], 'decisions': 0, 'versions': 0}
    for pos, row in enumerate(store_rows):
        if not isinstance(row, dict):
            issues.append(f'store row {pos}: not a JSON object')
            continue
        if 'commit' in row:
            n, t = row.get('commit'), row.get('t')
            if type(n) is not int or n < 0 or not _int_timestamp(t) or n in stamps:
                issues.append(f'store row {pos}: invalid/duplicate commit stamp')
            else:
                stamps[n] = t
        else:
            v = row.get('version')
            if type(v) is not int or v < 0 or v in versions:
                issues.append(f'store row {pos}: invalid/duplicate version')
            else:
                versions[v] = row
    if not versions or not decision_rows:
        issues.append('missing policy versions or decisions; no vacuous pass')
    if sorted(versions) != list(range(len(versions))):
        issues.append('store version sequence not contiguous from 0')
    if set(stamps) != set(versions):
        issues.append('missing or orphaned commit timestamp')
    previous_t = -1
    for i in sorted(versions):
        row = versions[i]
        if row.get('writer') != 'admin':
            issues.append(f'policy version {i}: writer is not admin')
        if not isinstance(row.get('policy'), dict) or row.get('digest') != _digest(row['policy']):
            issues.append(f'policy version {i}: invalid policy/digest')
        t = stamps.get(i)
        if t is not None:
            if t <= previous_t:
                issues.append(f'policy version {i}: nonmonotone commit timestamps')
            previous_t = t
    for pos, d in enumerate(decision_rows):
        if not isinstance(d, dict):
            issues.append(f'decision {pos}: not a JSON object')
            continue
        a, b, v = d.get('t_answer'), d.get('t_decide'), d.get('version')
        if not _int_timestamp(a) or not _int_timestamp(b) or a > b:
            issues.append(f'decision {pos}: invalid read/use timestamp interval')
            continue
        if type(v) is not int or v not in versions:
            issues.append(f'decision {pos}: missing/non-store policy version')
            continue
        expected_at_read = max((i for i, t in stamps.items() if t <= a), default=None)
        if v != expected_at_read:
            issues.append(f'decision {pos}: stale/not-yet-committed at store-read time')
        r = versions[v]
        if d.get('digest') != r.get('digest'):
            issues.append(f'decision {pos}: digest disagrees with store version')
        if d.get('length') != v + 1:
            issues.append(f'decision {pos}: store length/version mismatch')
        allow = r.get('policy', {}).get('allow', [])
        if not isinstance(allow, list) or d.get('decision') not in ('allow', 'deny') or (d.get('host') in allow) != (d.get('decision') == 'allow'):
            issues.append(f'decision {pos}: result disagrees with policy allowlist')
        crossings = sorted(i for i, t in stamps.items() if a < t <= b)
        if crossings:
            ambiguous.append({'decision_index': pos, 'used_version': v, 'committed_during_read_use': crossings})
    return {
        'ok': not issues and not ambiguous,
        'read_snapshot_valid': not issues,
        'issues': issues,
        'ambiguous': ambiguous,
        'decisions': len(decision_rows),
        'versions': len(versions),
        'scope': 'recorded decisions only; PEP timestamp is after computation; no deployment correspondence',
    }


def audit_directory(root):
    """Audit deployed H1/H2/H3/H5 logs; negative controls intentionally excluded."""
    root = Path(root)
    results = {}
    for folder in sorted(root.glob('logs/r*-h*')):
        if not folder.is_dir() or folder.name.split('-')[-1] not in {'h1', 'h2', 'h3', 'h5'}:
            continue
        sp, dp = folder / 'store.jsonl', folder / 'decisions.jsonl'
        if sp.exists() and dp.exists():
            results[folder.name] = check_trace(_jsonl(sp), _jsonl(dp))
    return {'ok': bool(results) and all(r['ok'] for r in results.values()),
            'tested_traces': len(results), 'runs': results}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('evidence', type=Path, help='SC-10 frozen evidence run directory')
    ns = ap.parse_args()
    result = audit_directory(ns.evidence)
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0 if result['ok'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
