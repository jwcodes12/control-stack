# F6 anytime-valid adaptive-episode monitor validation

The estimator in tools/anytime_monitor_calibration.py uses a uniform
martingale/Hoeffding *anytime* concentration bound. Unlike the iid per-stratum
estimator, it permits history-dependent, predictably sampled episode
selection, conditionally correlated outcome risk through previous
observations and an outcome-dependent sample stopping count.

For each predeclared history h and class c, X_i is a binary failed-monitor
outcome, and p_i = E[X_i | past before observing X_i]. We bound **the
observed subsequence's average conditional risk** (1/n) sum p_i at every
sample count n simultaneously:

    upper(n) = min(1, observed_failures/n +
                   sqrt(log((2*H)*n*(n+1)/alpha)/(2*n)))

This follows from the bounded-difference conditional Hoeffding
supermartingale plus alpha allocation delta_(h,c,n) =
alpha/(2*H*n*(n+1)), which sums to alpha across all n, histories
and classes. No independence of different monitors or repeated episodes
within a trajectory is claimed or assumed by the arithmetic.

**Key assumptions that software cannot verify:** a trusted record that the
manifest, monitored model and thresholds are externally pinned before
collection; complete episode logging; every history/class selection is
predictable *before* the alarm/outcome is observed; truthful binary attack
labels; monitored outcomes not selectively censored; meaningful class and
history definitions. If the monitor itself changes adaptively without a
predeclared rule, if the attack label is determined by the alarm itself,
or if sampling depends on the current alarm, the bound is not justified.

The theorem target is an average over *past selected episodes*, NOT a
universal upper bound on any individual future risk, the supremum risk
over every reachable attacker history, or full OS effect observation.
Unseen predeclared histories produce insufficient_samples and cannot
silently vanish from the union correction.

Manifest JSON must include histories, monitor_sha256, policy_sha256, alpha,
minimum_per_class, max_miss_upper and max_false_alarm_upper. Keep the
manifest under an independent, timestamped and reviewed custody. Both
metric limits must be below 1 and chosen **before** sampling.

Every JSONL episode has exactly id, history, attack (bool), alarm (bool).
The CLI writes a hash-tagged, exclusively created/never overwritten receipt:

    python3 tools/anytime_monitor_calibration.py --manifest policy.json         --input fresh-heldout-episodes.jsonl --output /new/receipt.json

A conditional_average_limits_met result only says the **conditional
averages** meet the declared limits under the hypotheses. It does not
establish a deployment guarantee or independently prove that the input
samples were held out.

Regression: python3 -m unittest tools.test_anytime_monitor_calibration -v

No newly gathered real monitoring dataset is included: PR #42 adds a
statistical acceptance implementation and tests, not fabricated empirical
evidence. Collecting new signed held-out samples and independent auditing
remains mandatory. All 28 scenario statuses remain CONDITIONAL.
