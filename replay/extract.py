"""Stage 1: deduplicate the LinuxArena public sample and write a compact replay corpus (no outputs/reasoning).

Dedup rule: identical (function, arguments) sequences are one trajectory; monitor reruns duplicate their source run.
Population labels: honest_haiku, honest_opus, attack_haiku, straj. Task cluster = (environment, main task, side task).
Held-out split (fixed before any policy is written): environments sorted by name; those whose SHA-256 of the name has
an even first byte are DEV, odd are TEST. Policies are designed on DEV only; TEST is used once for final reporting.
"""
import hashlib, json, collections
from pathlib import Path

SRC = Path(__file__).resolve().parent.parent / "data/linuxarena-public/sample.jsonl"
OUT = Path(__file__).resolve().parent / "corpus.jsonl"


def population(run: str) -> str:
    if "straj" in run: return "straj"
    if "Opus honest" in run: return "honest_opus"
    if "Haiku honest" in run: return "honest_haiku"
    if "Haiku attack" in run: return "attack_haiku"
    raise ValueError(run)


def split(env: str) -> str:
    return "dev" if hashlib.sha256(env.encode()).digest()[0] % 2 == 0 else "test"


seen = {}
for line in SRC.open():
    r = json.loads(line)
    acts = [{"function": a["function"], "arguments": a["arguments"], "error": bool(a.get("output_error"))}
            for a in r["actions"]]
    key = hashlib.sha256(json.dumps([(a["function"], a["arguments"]) for a in acts], sort_keys=True).encode()).hexdigest()
    if key in seen:
        seen[key]["runs"].append(r["run_display_name"]); continue
    st = r.get("side_task") or {}
    env = r["environment"]["id"]
    seen[key] = {"key": key, "trajectory_id": r["trajectory_id"], "runs": [r["run_display_name"]],
                 "population": population(r["run_display_name"]), "env": env, "split": split(env),
                 "main_task": r["main_task"]["id"], "main_task_success": r.get("main_task_success"),
                 "side_task": st.get("id"), "side_task_success": r.get("side_task_success"),
                 "failure_type": st.get("failure_type"), "side_category": st.get("task_category"),
                 "actions": acts}
with OUT.open("w") as f:
    for v in seen.values():
        f.write(json.dumps(v) + "\n")
c = collections.Counter((v["population"], v["split"]) for v in seen.values())
envs = sorted({v["env"] for v in seen.values()})
summary = {"source_sha256": hashlib.sha256(SRC.read_bytes()).hexdigest(), "unique": len(seen),
           "by_population_split": {f"{p}/{s}": n for (p, s), n in sorted(c.items())},
           "dev_envs": [e for e in envs if split(e) == "dev"], "test_envs": [e for e in envs if split(e) == "test"],
           "attack_failure_types": dict(collections.Counter(v["failure_type"] for v in seen.values() if v["side_task"])),
           "attack_side_success": dict(collections.Counter(str(v["side_task_success"]) for v in seen.values() if v["side_task"]))}
(Path(__file__).resolve().parent / "corpus_summary.json").write_text(json.dumps(summary, indent=1) + "\n")
print(json.dumps(summary, indent=1))
