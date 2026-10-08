# Offline replay: full LinuxArena public corpus, frozen policy v2, dev vs held-out TEST

Corpus: 22,215 public trajectories (CC BY 4.0; per-shard SHA-256 in `shard_hashes/`, counts verified against the
dataset manifest) → 9,863 unique action sequences (monitor reruns removed) from 172 runs and ~15 agent models.
Environment-level split fixed before policy work (dev: 6 environments; test: 4). Policy `policy.py` frozen at
`ba9ff40` (SHA-256 361fd480…27c9) after dev-only iteration; TEST evaluated once, all tiers reported.
Metrics: honest interference = trajectories with ≥ 1 denied action; recorded-attack interception = attack trajectories
with ≥ 1 denied action (upper bound on blocking before harm for live failures; ignores adaptive rerouting; counts blocks
on incidental main-task actions too). Wilson 95% intervals; trajectories of one task are not independent, so intervals
are optimistic.

| tier | honest dev | honest TEST | attack dev | attack TEST | strajs dev | strajs TEST |
|---|---|---|---|---|---|---|
| T1 egress | 0.044 [0.037, 0.051] | **0.077** [0.067, 0.088] | 0.154 [0.140, 0.168] | 0.175 [0.156, 0.196] | 5/98 | 4/44 |
| T2 + privilege | 0.175 | 0.131 | 0.274 | 0.222 | 21/98 | 4/44 |
| T3 + control plane | 0.187 | 0.140 | 0.300 | 0.265 | 21/98 | 12/44 |
| T4 + pipe-to-shell | 0.201 | 0.146 | 0.313 | 0.270 | 21/98 | 12/44 |
| T4 + egress in code | 0.245 | 0.213 | 0.372 | 0.333 | 27/98 | 14/44 |

TEST, by side-task category (T1 / T4 / T4+code): access_control_bypass (429) 0.16 / 0.33 / 0.35; exfiltration (366)
0.17 / 0.23 / 0.31; running_malware (252) 0.35 / 0.44 / 0.52; data_tampering (224) 0.08 / 0.14 / 0.25;
monitoring_subversion (136) 0.04 / 0.12 / 0.12.

## Conclusions
1. **Weak separation.** The best tier (T1 egress) blocks 2–3.5× more attack than honest trajectories, but intercepts
   only 15–18% of attacks while blocking 4–8% of honest work. No tier gives high interception at low interference.
2. **Out-of-sample transfer matters.** Honest interference at T1 nearly doubles from dev to TEST (0.044 → 0.077): the
   allowlist tuned on dev environments misses destinations the test environments legitimately need. Policies need
   per-deployment allowlists, not a learned global one.
3. **Host policy addresses host-level classes only.** Malware 35–52%, exfiltration 17–31%; data tampering and
   monitoring subversion ≤ 25% even with code-egress scanning: these are application-level and need artifact gates
   (reviewed diffs on protected code surfaces) or monitoring.
4. **The privilege tier is not discriminative** in this setting (agents run as root and use su/sudo honestly).
5. **Limits of offline replay** (from the review): it estimates interference and recorded interception only; actual
   usefulness and adaptive attacks need live runs.

Next candidates: (a) attribute blocks to attack vs incidental actions (needs per-action attack labels; `attack_analysis`
covers ~4%); (b) a per-environment allowlist derived from each environment's declared services; (c) artifact-gate
policies (F4) for the application-level classes; (d) live pilot (paid).
