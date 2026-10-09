# SC-10 decision linearization gap (source-only review, 2026-10-09)

**Scope:** independently re-examine frozen SC-10 store and PEP logs; do **not**
modify historical evidence, preregistration, policy runtime, Lean theorems,
scenario manifest, or assurance classification.

## The mismatch

The Lean `ControlStack.SC10.sc10_safe` describes a single atomic decision
using the current latest admin policy. In the reference Python harness,
`store.py` serves the latest policy and stamps `t_answer`. In a *later*
step, `pep.py` computes and records the enforcement decision and stamps
`t_decide`. The existing `reconcile.py` checks freshness at `t_answer`,
not `t_decide`. An admin version could commit between them. Even if the
read was fresh, a subsequent decision can use a version that is no longer
current. Distinguish snapshot-at-read linearizability from *latest-at-effect*
freshness rather than silently identifying these semantics.

`tools/sc10_linearization.py` independently checks both clock cuts for
every observed decision, along with reported digest, version length, policy
result, writer and negative-control configuration. The synthetic test injects
an admin commit between store answer and decision; it passes the read-time
test and fails the effect-time test.

### Reproduce (read-only)

```sh
python3 -m unittest tools.test_sc10_linearization -v
python3 tools/sc10_linearization.py \
  --store scenarios/SC-10/evidence/run-1/logs/r1-h1/store.jsonl \
  --decisions scenarios/SC-10/evidence/run-1/logs/r1-h1/decisions.jsonl
```

This is a **post-hoc checker** and does not create new experimental
assurance. It is not a complete concrete-to-abstract Lean refinement.
A pass does not establish that all policy decisions and every harmful effect
were logged, that SO_PEERCRED identified the correct trust principal across
all processes, or that a store read/decision is atomic with policy updates.
The shared monotonic clock, time/commit log truth, process isolation, digest
identity, unique policy evaluator and exclusive action path remain open.

To bridge this gap in a new separately preregistered system, either (1)
explicitly weaken the desired property to a snapshot linearized at the store
read and prove that the effect is atomic with that snapshot, or (2) enforce a
version-validating transaction/serialization through the effect and prove
that no admin update may commit in the intervening interval. A log-based
checker cannot itself close the runtime TOCTOU gap.

**No status change:** SC-10 remains CONDITIONAL; independent statement-fidelity
review and runtime correspondence are open.