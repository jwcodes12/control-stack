# LinuxArena public mirror: compact labels and scores

Derived from the Hugging Face dataset `anonymouslinuxarena/linuxarena-public` (LinuxArena: A Benchmark for AI
Control Evaluations, anonymous authors), revision `2fd29f9c7bc190fb873bd76c6bd648f22b9ab0a7`, licence **CC-BY-4.0**.
Changes made: each of the ten shards was reduced by `experiments/E1-flag-budget-replay/extract_scores.py` to

- `meta/<shard>.jsonl.gz`: per-trajectory labels and counts (run, environment, task and side-task ids, success
  flags, number of actions and of scored actions). No score values.
- `sealed/<shard>.jsonl.gz`: per-action suspicion scores and the trajectory-level score, keyed by trajectory id.
- `raw_shards.json`: row count, byte count and SHA-256 of each raw shard as streamed.

**Do not read `sealed/` before experiment E1 has been run.** It is the confirmatory data of
`experiments/E1-flag-budget-replay/PREREG.md`. The seal is a convention; nothing enforces it.
