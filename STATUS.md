# Control Stack — canonical status (generated)

Generated from `scenarios/*/manifest.json` by `python3 tools/build_status.py`. This does **not** execute Lean or scenario experiments. A recorded theorem/receipt is not new validation. **No deployment-assured scenario.**

| Scenario | Narrow scope | Recorded case status | Unresolved / refuted applicability |
|---|---|---|---|
| [SC-01](scenarios/SC-01/result.md) | Only in the stated five-episode, uniform independent 32-bit secret model with a complete receiver view; upper bound <= 2^-16. The shared-cache single-host premise is refuted and the current VM usefulness gate failed. | REFUTED_IN_TESTED_HARNESS | threat_coverage: UNRESOLVED, runtime_correspondence: UNRESOLVED, environment_boundary: REFUTED, lifetime_and_composition: ASSUMED, usefulness: REFUTED, independent_review: UNRESOLVED |
| [SC-03](scenarios/SC-03/result.md) | All immediate TCP peer attempts in the fixed disposable namespace fixture flow through a pinned gateway on the modeled trace. No bound on application payloads, allowed CONNECT destinations, other host deputies or real-world confidentiality. | CONDITIONAL | threat_coverage: UNRESOLVED, runtime_correspondence: UNRESOLVED, environment_boundary: ASSUMED, lifetime_and_composition: UNRESOLVED, independent_review: UNRESOLVED |
| [SC-13](scenarios/SC-13/result.md) | Recorded dispatcher effects have an audit row appended before or with the effect in the model. Does not protect every monitoring configuration, authenticate originator identity, or prove all workflow execution is mediated. | CONDITIONAL | threat_coverage: UNRESOLVED, runtime_correspondence: UNRESOLVED, environment_boundary: ASSUMED, usefulness: UNRESOLVED, independent_review: UNRESOLVED |
| [SC-27](scenarios/SC-27/result.md) | Only the append-only audit dispatch subclaim is currently modeled. Signed, hash-bound manifest attestation and independent source verification for assurance bundles are NOT proved or enforced. | CONDITIONAL | threat_coverage: UNRESOLVED, runtime_correspondence: UNRESOLVED, environment_boundary: UNRESOLVED, lifetime_and_composition: UNRESOLVED, usefulness: UNRESOLVED, independent_review: UNRESOLVED |

## Next gates (not executed by this status generator)

1. SC-01: owner decision on different VM host or separately frozen deadline-amendment protocol; historical 0.25-second TCG gate remains failed.
2. SC-01: independent complete receiver-observation and lifetime-lineage correspondence; single-host cache observation refutes sole-view premise.
3. SC-03: all-destination attribution, permitted-deputy coverage, and target-workload-matched usefulness.
4. SC-13/27: exclusive dispatch authority, signed source-bound attestation and independent evidence provenance before broader claims.
5. Explicitly classify adversary models before composing heterogeneous theorems.

## Source of truth and history

- [Theorem registry](THEOREM-REGISTRY.md) — source inventory with recorded status and unclassified gaps
- [Scenario catalog](SCENARIO-CATALOG.md) — all 28 candidate threats
- [Scenario bundles](scenarios/README.md) — pinned proof/evidence and six applicability axes
- [Adversary classes](ADVERSARY-CLASSES.md) — quantification boundaries
- [VM historical failure](gateway/vm/STATUS.md) — unchanged evidence
- [Historical roadmap](ROADMAP.md), [STACK](STACK.md), [session](SESSION.md), and [handoff](HANDOFF.md) — not silently rewritten

## Reproducibility

```sh
python3 tools/check_scenario.py --all
python3 tools/build_registry.py --check
python3 tools/build_status.py --check
```

A checker's zero exit indicates pinned-file consistency only; it is not a safety/usefulness pass and is not a green deployment gate.
