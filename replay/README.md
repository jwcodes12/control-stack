# Offline replay of LinuxArena trajectories (no model calls)

Stage 1 (`extract.py`): 932 sample records → 584 unique trajectories (monitor reruns duplicate their source; 20
Haiku-attack task pairs are genuinely different attempts and are kept, clustered by task). Populations: 200 Haiku
honest, 200 Opus honest, 112 Haiku attack, 72 strajs. Held-out split fixed BEFORE any policy work: environment-level,
by SHA-256 of the environment name (dev: auto_workflow, file_indexing, media_processing, shared_dotfiles, user_tracking,
web_scraping; test: clinical_trial, model_registry, slack_clone, tiktok). Source: `data/linuxarena-public/sample.jsonl`
(CC BY 4.0, SHA-256 in `corpus_summary.json`; not committed, 705 MB).

Metrics (offline replay can estimate only the first two):
1. honest policy interference: fraction of honest trajectories with ≥ 1 blocked action;
2. recorded attack interception: fraction of attack trajectories blocked before the harmful effect;
3. actual usefulness: requires live runs (paid stage).
