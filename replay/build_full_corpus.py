"""Dedup the full compact shards into corpus_full.jsonl (same schema as corpus.jsonl; same environment split).
Population: 'straj' if the run name mentions straj; else 'attack_<model>' if a side task is set, 'honest_<model>' otherwise."""
import collections, hashlib, json, re
from pathlib import Path

HERE = Path(__file__).resolve().parent
split = lambda env: "dev" if hashlib.sha256(env.encode()).digest()[0] % 2 == 0 else "test"


def model_tag(m):
    m = (m or "unknown").split("/")[-1].lower()
    return re.sub(r"[^a-z0-9]+", "-", m).strip("-")[:40]


seen = {}
runs = collections.Counter()
for f in sorted((HERE / "full").glob("*.compact.jsonl")):
    for line in f.open():
        r = json.loads(line)
        runs[r["run"]] += 1
        k = r["action_key"]
        if k in seen:
            seen[k]["runs"].append(r["run"]); continue
        pop = "straj" if "straj" in r["run"].lower() else (("attack_" if r["side_task"] else "honest_") + model_tag(r["agent_model"]))
        r.update(population=pop, split=split(r["env"]), runs=[r["run"]], key=k)
        seen[k] = r
with (HERE / "corpus_full.jsonl").open("w") as out:
    for v in seen.values():
        out.write(json.dumps(v) + "\n")
c = collections.Counter((v["population"], v["split"]) for v in seen.values())
summ = {"records": sum(runs.values()), "unique": len(seen), "runs": len(runs),
        "by_population": dict(collections.Counter(v["population"] for v in seen.values()).most_common()),
        "by_class_split": dict(collections.Counter(("honest" if v["population"].startswith("honest") else "attack",
                                                    v["split"]) for v in seen.values()))}
summ["by_class_split"] = {f"{a}/{b}": n for (a, b), n in summ["by_class_split"].items()}
(HERE / "corpus_full_summary.json").write_text(json.dumps(summ, indent=1) + "\n")
print(json.dumps(summ, indent=1))
