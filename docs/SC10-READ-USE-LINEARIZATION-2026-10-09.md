# SC-10 read/use linearization audit (2026-10-09)

## Finding: freshness is currently scoped to the store read, not the effect

The frozen SC-10 harness `store.py` answers a policy read with a version, digest,
length and `t_answer` (time of the store response). The enforcement point
`pep.py` then computes its allow/deny response and records `t_decide`
*after* that computation. The existing `reconcile.py` compares policy
versions at `t_answer`, not at the actual decision computation.

A validly newer admin policy can commit after the PEP's store read and before
its decision is used. `SC10.sc10_safe` rules out stale version use in the
abstract full-check machine, but this host implementation has no atomic
read/evaluate/store linearization point covering the interval. The frozen
single-host run cannot be upgraded to a proof of such atomicity.

## New, read-only checker

`tools/sc10_temporal_audit.py` validates the recorded H1/H2/H3/H5 traces:
contiguous store versions, unique monotonic commit timestamps, SHA-256 policy
digests, admin writers, decision policy digests, applied allowlist values,
store length, version freshness at `t_answer`, and the ordering of
`t_answer <= t_decide`. It separately reports any store commits in the
interval `(t_answer, t_decide]` as **AMBIGUOUS**.

A crossing is **not** a proven stale-use defect, because `t_decide` was
recorded after the allow/deny calculation. Conversely, finding no crossings
in a finite run is **not** proof that another run cannot experience one.
Missing evidence or ambiguous intervals must not silently pass.

The eight synthetic mutation tests exercise policy/source defects,
staleness, timestamp reversal, partial receipts, duplicate commit records,
a concurrent-commit witness and a passing trace.

Run without changing any historical receipts:

```sh
python3 -m unittest discover -s tools -p 'test_sc10_temporal_audit.py' -v
python3 tools/sc10_temporal_audit.py scenarios/SC-10/evidence/run-1
```

The test is limited to the observed reference PEP decisions; it does not
establish process credential separation, enforce a real firewall, cover bypass
decision paths, or replace an operational event-machine → Lean simulation.

## Real remediation still required (new preregistration)

To make actual *enforcement-time* freshness a defensible property, use a
trusted single transaction/linearization point that both selects a policy
version and makes the policy decision, while policy writes cannot interleave
between selection and authorization. Couple this to the effect mediator so
there is no post-decision unmediated path. Record and test concurrent
tightening at that boundary, use an independent recorder or checker, and
explicitly model crashes, retries, aborts, authorization, and real effect
atomicity. A PEP read timestamp alone cannot establish this.

This document does **not** claim SC-10 or SC-11 has an implemented Lean
refinement, nor that any scenario is deployment assured. Do not amend the
frozen preregistration or evidence to support a stronger claim.
