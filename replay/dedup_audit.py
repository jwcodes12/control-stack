"""R2-2: audit global action-sequence dedup. For each action_key with >1 records, compare label tuples."""
import collections, glob, json
from pathlib import Path
HERE = Path(__file__).resolve().parent
groups = collections.defaultdict(list)
for f in sorted(glob.glob(str(HERE / "full/*.compact.jsonl"))):
    for line in open(f):
        r = json.loads(line)
        groups[r["action_key"]].append(r)
LABELS = ("env", "main_task", "side_task", "side_task_success", "main_task_success", "agent_model")
out = collections.Counter(); examples = collections.defaultdict(list)
for k, rs in groups.items():
    if len(rs) == 1:
        out["singleton"] += 1; continue
    out["multi_groups"] += 1; out["multi_records"] += len(rs)
    distinct = {lab: len({json.dumps(r.get(lab)) for r in rs}) for lab in LABELS}
    runs = len({r["run_id"] for r in rs}); traj = len({r["trajectory_id"] for r in rs})
    differs = [lab for lab, n in distinct.items() if n > 1]
    if not differs:
        out["exact_label_clones"] += 1
    else:
        for lab in differs:
            out[f"differs_{lab}"] += 1
        if len(examples[tuple(differs)]) < 3:
            examples[tuple(differs)].append({"n": len(rs), "runs": [r["run"] for r in rs][:4],
                                             **{lab: sorted({str(r.get(lab)) for r in rs})[:4] for lab in differs},
                                             "n_actions": len(rs[0]["actions"])})
    out["same_trajectory_id_all"] += traj == 1
    out["distinct_run_ids_gt1"] += runs > 1
res = {"records": sum(len(v) for v in groups.values()), "unique_keys": len(groups), **dict(out),
       "examples": {"|".join(k): v for k, v in examples.items()}}
(HERE / "dedup_audit.json").write_text(json.dumps(res, indent=1) + "\n")
print(json.dumps({k: v for k, v in res.items() if k != "examples"}, indent=1))
for k, v in res["examples"].items():
    print("EXAMPLE", k, json.dumps(v[0])[:300])
