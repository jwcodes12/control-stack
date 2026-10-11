# Exploratory joint co-miss evidence on LaStraj monitors

tools/monitor_pair_replay.py examines the **real per-trajectory monitor
scores** already checksum-pinned under data/redwood-leaderboard/monitors.json.

For each of the 19 observed monitor variants, it considers every one of
the 171 possible two-monitor ensembles, at a fixed demonstrative
suspicion threshold of 8. A pair alarms if **either** monitor's maximum
action suspicion score during the same trajectory crosses the threshold.

A pair misses an attack only when **both** monitors miss that same attack
trajectory. Benign false alarms occur when **either** monitor alarms
on a benign trajectory. Both metrics directly preserve shared blind spots,
rather than multiplying individual miss probabilities.

All 171 candidate pairs remain in the confidence-correction family,
including pairs with missing or unaligned scored episodes. Only pairs
with **exactly aligned trajectory identity sets** in both classes are
evaluable. Each reported per-pair one-sided exact Clopper-Pearson bound
uses alpha / (2 * 171); false alarms and missed attacks are separate
risk families. Each trajectory is one sampling unit; its many actions
are *not* independent samples.

Reproduce into a new, non-overwritten scratch receipt:

    python3 tools/monitor_pair_replay.py --threshold 8        --output /tmp/lastraj-pairs-new.json

No score threshold, ensemble choice or sampling rule was independently
predeclared before the data became public. The entire analysis is
**EXPLORATORY_POSTHOC_NO_ADAPTIVE_CERTIFICATE**, regardless of
point estimates or apparent ensemble improvement. In particular,
correlations from a small fixed benchmark do not certify adversarial
conditional recall under unseen feedback histories. Collect fresh,
predeclared adaptive-episode evidence using the separate anytime-valid
acceptance pipeline before an operational F6 claim.
