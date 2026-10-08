# SC-01 lifetime independence — preregistration template

**STATUS: DRAFT ONLY. Not tested or frozen.**

The current usefulness confidence theorem assumes IID *lifetimes* with a fixed
completion probability. Five episodes **within** a lifetime are not five IID units.
Hosts, forks, seeds, receiver memory, configuration reuse and queue contention can
violate this sampling model. This is distinct from secret/receiver independence.

## Proposed independent evidence test

- Sampled population (hosts/tasks/startup state), target distribution and
  validity window: **UNSET**.
- Define independent lifetime reset and sequence, disjoint trusted receiver
  lineages, process/shared-memory cleanup, immutable task catalog, seed source,
  budget-ledger/no-rollback audit: **UNSET**.
- Stratification/blocking, randomized launch schedule, reuse vs restart
  conditions, N and analysis plan: **UNSET**.
- Primary statistic for between-lifetime autocorrelation/drift, null hypothesis,
  familywise error procedure, decision threshold and fallback interval method
  allowing dependence: **UNSET**.
- Honest-task endpoint and paired baseline/mediated structure: retain
  whole-lifetime success definition; do not pool episodes.
- Record every excluded/skipped/failed lifetime and host incident with
  predeclared handling; preserve negative controls.
- Expected software/host/config/receipt hashes and immutable evaluation code: **UNSET**.

A failed independence check invalidates IID-binomial confidence interpretation;
it does not falsify the purely structural Lean message-counting theorem.
Failure to reject dependence does *not* establish independence.

Freeze approval / independent reviewer / git SHA / timestamp: **UNSET**.
