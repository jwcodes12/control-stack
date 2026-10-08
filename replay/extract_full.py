"""Stream the full LinuxArena public shards one at a time: download, reduce to compact records (no outputs or
reasoning), verify the record count against manifest.json, delete the shard. Peak disk ≈ one shard (≤ 2.1 GB)."""
import hashlib, json, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MAN = json.loads((HERE.parent / "data/linuxarena-public/manifest.json").read_text())
OUT = HERE / "full"
OUT.mkdir(exist_ok=True)
URL = "https://huggingface.co/datasets/anonymouslinuxarena/linuxarena-public/resolve/main/data/{}.jsonl"
for env, n_expected in MAN["per_env_counts"].items():
    dst = OUT / f"{env}.compact.jsonl"
    if dst.exists():
        print("skip", env); continue
    raw = OUT / f"{env}.raw.jsonl"
    subprocess.run(["curl", "-sL", "--fail", "--retry", "4", "-o", str(raw), URL.format(env)], check=True)
    h, n = hashlib.sha256(), 0
    with raw.open("rb") as fin, (OUT / f"{env}.tmp").open("w") as fout:
        for line in fin:
            h.update(line)
            r = json.loads(line)
            st = r.get("side_task") or {}
            acts = [{"function": a["function"], "arguments": a["arguments"], "error": bool(a.get("output_error"))}
                    for a in r["actions"]]
            fout.write(json.dumps({
                "trajectory_id": r["trajectory_id"], "run_id": r["run_id"], "run": r["run_display_name"],
                "agent_model": r.get("agent_model"), "env": r["environment"]["id"],
                "main_task": r["main_task"]["id"], "main_task_success": r.get("main_task_success"),
                "side_task": st.get("id"), "side_task_success": r.get("side_task_success"),
                "failure_type": st.get("failure_type"), "side_category": st.get("task_category"),
                "action_key": hashlib.sha256(json.dumps([(a["function"], a["arguments"]) for a in acts],
                                                        sort_keys=True).encode()).hexdigest(),
                "actions": acts}) + "\n")
            n += 1
    raw.unlink()
    if n != n_expected:
        sys.exit(f"{env}: {n} records != manifest {n_expected}")
    (OUT / f"{env}.tmp").rename(dst)
    (OUT / f"{env}.sha256").write_text(h.hexdigest() + "\n")
    print(env, n, "records ok", flush=True)
