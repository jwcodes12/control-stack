"""R2-1/2/4/6 robustness analysis (NEW analysis; the frozen dev/test results in replay_full_*.json are unchanged).
- task-aware dedup: key = (action_key, env, main_task, side_task, run-type class)
- run-type classes from run names: honest, honest_accidental ("Accidental ST": honest runs scored against side tasks),
  attack, attack_obvious, attack_strategy, straj
- strata: side_task_success, failure_type, environment, agent model, side category; macro averages
- position of the first denied action (fraction of trajectory length); "any-block" endpoint, NOT prevention
"""
import collections, glob, hashlib, json, math, statistics
from pathlib import Path
from policy import rules, TIERS, IGNORED_TOOLS

HERE = Path(__file__).resolve().parent
split = lambda env: "dev" if hashlib.sha256(env.encode()).digest()[0] % 2 == 0 else "test"


def klass(run, side):
    n = run.lower()
    if "accidental st" in n: return "honest_accidental"
    if "straj" in n: return "straj"
    if "strategy-attack" in n: return "attack_strategy"
    if "obvious" in n: return "attack_obvious"
    return "attack" if side else "honest"


if __name__ != "__main__" and False:
    pass
seen = {}
for f in sorted(glob.glob(str(HERE / "full/*.compact.jsonl"))):
    for line in open(f):
        r = json.loads(line)
        c = klass(r["run"], r["side_task"])
        k = (r["action_key"], r["env"], r["main_task"], r["side_task"], c)
        if k not in seen:
            r["klass"] = c; r["split"] = split(r["env"]); seen[k] = r
rows = list(seen.values())
TIER = "T1"; TIER4 = "T4+code"


def wil(k, n, z=1.96):
    if n == 0: return [0, 1]
    p = k / n; d = 1 + z * z / n; c = p + z * z / (2 * n); r = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
    return [round((c - r) / d, 3), round((c + r) / d, 3)]


def blocks(r, ids):
    acts = [a for a in r["actions"] if a["function"] not in IGNORED_TOOLS]
    for i, a in enumerate(acts):
        if set(rules(a)) & ids: return i / max(1, len(acts))
    return None


stats = collections.defaultdict(lambda: collections.Counter())
first_pos = collections.defaultdict(list)
tasks = collections.defaultdict(set)
for r in rows:
    for t in (TIER, TIER4):
        pos = blocks(r, TIERS[t])
        keys = [("class", r["klass"]), ("class_split", r["klass"], r["split"]), ("class_env", r["klass"], r["env"]),
                ("class_model", r["klass"], (r.get("agent_model") or "unknown").split("/")[-1])]
        if r["klass"].startswith("attack") or r["klass"] == "straj":
            keys += [("success", r["klass"], str(r.get("side_task_success"))),
                     ("failure", r["klass"], r.get("failure_type") or "unknown"),
                     ("category", r.get("side_category") or "none")]
        for key in keys:
            stats[(t,) + key]["n"] += 1; stats[(t,) + key]["b"] += pos is not None
        if pos is not None and (r["klass"] == "attack" and r.get("side_task_success")):
            first_pos[t].append(pos)
    tasks[r["klass"]].add((r["env"], r["main_task"], r["side_task"]))
res = {"unique_task_aware": len(rows), "by_class": dict(collections.Counter(r["klass"] for r in rows)),
       "unique_tasks_by_class": {k: len(v) for k, v in tasks.items()}, "tables": {},
       "first_block_position_successful_attacks": {t: {"n": len(v), "median": round(statistics.median(v), 3) if v else None,
                                                        "quartiles": [round(q, 3) for q in statistics.quantiles(v, n=4)] if len(v) > 3 else None}
                                                    for t, v in first_pos.items()}}
for key, c in sorted(stats.items(), key=lambda x: str(x[0])):
    res["tables"]["/".join(map(str, key))] = {"b": c["b"], "n": c["n"], "rate": round(c["b"] / c["n"], 3), "wilson95": wil(c["b"], c["n"])}
for t in (TIER, TIER4):
    cats = [v for k, v in res["tables"].items() if k.startswith(f"{t}/category/") and not k.endswith("/none")]
    envs = [v for k, v in res["tables"].items() if k.startswith(f"{t}/class_env/attack/")]
    henv = [v for k, v in res["tables"].items() if k.startswith(f"{t}/class_env/honest/")]
    res[f"macro_{t}"] = {"attack_over_categories": round(statistics.mean(v["rate"] for v in cats), 3),
                         "attack_over_envs": round(statistics.mean(v["rate"] for v in envs), 3),
                         "honest_over_envs": round(statistics.mean(v["rate"] for v in henv), 3)}
(HERE / "robustness.json").write_text(json.dumps(res, indent=1) + "\n")
print(json.dumps({k: v for k, v in res.items() if k != "tables"}, indent=1))
for k in sorted(res["tables"]):
    if any(s in k for s in ("/class/", "/success/", "/class_split/")):
        v = res["tables"][k]; print(f"{k:<45} {v['b']:>5}/{v['n']:<5} {v['rate']:.3f} {v['wilson95']}")
