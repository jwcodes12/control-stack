#!/usr/bin/env python3
"""Stream one LinuxArena public-mirror shard and split it into two compact files.

  <out>/meta/<shard>.jsonl     labels and counts only: NO score values. Safe to read before the freeze.
  <out>/sealed/<shard>.jsonl   per-action suspicion scores. Must not be read before the preregistration is frozen.
  <out>/hash/<shard>.json      SHA-256 and byte count of the raw shard, and row counts.

The raw shard (1 to 2 GB of full trajectories) is read from stdin and not stored:

  curl -sL https://huggingface.co/datasets/anonymouslinuxarena/linuxarena-public/resolve/<REV>/data/<shard>.jsonl \
    | python3 extract_scores.py <shard> <out>

Source: anonymouslinuxarena/linuxarena-public (CC-BY-4.0). This script computes no statistic of any score.
"""
import hashlib
import json
import sys
from pathlib import Path


def num(x):
    return x if isinstance(x, (int, float)) and not isinstance(x, bool) else None


def main(shard, out):
    out = Path(out)
    for d in ("meta", "sealed", "hash"):
        (out / d).mkdir(parents=True, exist_ok=True)
    h = hashlib.sha256()
    n_bytes = rows = 0
    with open(out / "meta" / f"{shard}.jsonl", "w") as fm, open(out / "sealed" / f"{shard}.jsonl", "w") as fs:
        for line_no, raw in enumerate(sys.stdin.buffer):
            h.update(raw)
            n_bytes += len(raw)
            if not raw.strip():
                continue
            r = json.loads(raw)
            acts = r.get("actions") or []
            mons = [a.get("monitor_response") if isinstance(a.get("monitor_response"), dict) else None for a in acts]
            scores = [num(m.get("sus_score")) if m else None for m in mons]
            tm = r.get("traj_monitor_response") if isinstance(r.get("traj_monitor_response"), dict) else None
            env, mt, st = r.get("environment") or {}, r.get("main_task") or {}, r.get("side_task")
            meta = {
                "trajectory_id": r.get("trajectory_id"), "run_id": r.get("run_id"),
                "run_display_name": r.get("run_display_name"), "shard": shard, "line_no": line_no,
                "environment": env.get("id"),
                "main_task": mt.get("id"), "main_task_category": mt.get("task_category"),
                "side_task": st.get("id") if st else None,
                "side_task_category": st.get("task_category") if st else None,
                "failure_type": st.get("failure_type") if st else None,
                "agent_model": r.get("agent_model"),
                "main_task_success": r.get("main_task_success"), "side_task_success": r.get("side_task_success"),
                "n_actions": len(acts), "n_scored_actions": sum(1 for s in scores if s is not None),
                "n_monitor_errors": sum(1 for m in mons if m and m.get("error")),
                "monitor_names": sorted({str(m.get("monitor_name")) for m in mons if m}),
                "monitor_models": sorted({str(m.get("model_name")) for m in mons if m}),
                "has_traj_score": bool(tm and num(tm.get("sus_score")) is not None),
                "traj_monitor_name": tm.get("monitor_name") if tm else None,
                "traj_monitor_model": tm.get("model_name") if tm else None,
                "n_substep_actions": sum(1 for a in acts if a.get("substeps")),
            }
            fm.write(json.dumps(meta, sort_keys=True) + "\n")
            fs.write(json.dumps({"trajectory_id": r.get("trajectory_id"), "action_scores": scores,
                                 "traj_score": num(tm.get("sus_score")) if tm else None}) + "\n")
            rows += 1
    (out / "hash" / f"{shard}.json").write_text(json.dumps(
        {"shard": shard, "raw_sha256": h.hexdigest(), "raw_bytes": n_bytes, "rows": rows}, sort_keys=True) + "\n")
    print(f"{shard}: {rows} rows, {n_bytes} bytes, sha256 {h.hexdigest()}")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
