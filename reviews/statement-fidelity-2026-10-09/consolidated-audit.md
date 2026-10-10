# Adversarial theorem-statement fidelity audit — SC-06/08/25/26, F6/F8

**Status:** source-derived technical self-audit, **not independent human review**; no change to any historical evidence, manifest assurance status, or the frozen EgressGate. The findings distinguish valid formal claims from runtime claims. Pinned Lean cross-checks are in `Counterexamples.lean` and must pass Actions at the exact head to count as kernel observations.

| Claim / theorem | What the statement actually establishes | Adversarial issue and disposition |
|---|---|---|
| `SC06OneUse.scoped_safe` | All *recorded* abstract foreign-sensitive effects in `run R init es` match a context entry and user-role confirmation, and confirmation IDs in the effect list are distinct | `EffectOk` is defined using final-state membership, not a direct observation of runtime provenance or external effect causality. In `step`, `.ingest` and `.confirm` are events with caller/data authored by the trace, not cryptographically authenticated. `step` now checks entry existence on confirmation, defeating the earlier pre-ingestion counterexample, but real issuer provenance, handle integrity and full mediation remain assumptions. Do not call it a human consent theorem. |
| `SC08.sc08_safe` | `Good E` over the `St.ran` list of the abstract machine, with `full` checks | `Env.h : ℕ → ℕ` represents a trusted digest and `Env.interp` represents interpreter classification. These values do not establish collision resistance, load-time image identity, Python/module/JIT loaders, shell escapes, or that all native exec paths pass the broker. A pinned script test only checks a slice of runtime behavior. |
| `SC25.sc25_safe` | Every **abstract executed** item has an audit/approval satisfying `ExecOk` with log lengths at the execution moment and unique execution ID | `cls` and `h` are arbitrary trusted functions; correct irreversibility classification, digest collision resistance, external executor exclusivity and source-binding are premises. Further, `halt_freezes` proves only `executed` unchanged, not full state: `.crash` after HALT still clears volatile `checked`. Retain narrowly stated effect freeze; don't market it as an absorbing full-state halt. |
| `SC26.sc26_safe` | For traces whose every operation satisfies `legal R`, each model bank entry is exact-approved/reserved, receiver-deduplicated and sum amount ≤ cap | `legal` restricts only direct `.bankCall` with the gate identity; **any `.approve c ...` operation is formally legal**, including one carrying a role-member approver identifier. The adversary cannot actually forge a trusted principal only as a separate environment/credential separation premise. `halt_freezes` explicitly allows already-in-flight messages to complete. Reusing same business intent with a distinct request ID gives additional payments. |
| `EnsembleKernel.ensK_adaptive` (F6) | Bound for an adaptive attacker under a specified per-history mixture law, blind-spot cap, and conditional per-monitor q bound | `Params`, unobserved blind-spot mixture and every-history catch-rate assumptions carry the probabilistic burden; observationally correlated misses do not satisfy an independent product law by default. New source-only finite countermodel confirms a fully correlated case violates the product assumption. False-positive and monitoring policy usefulness are separate obligations. |
| `GateComposition.shared_invariants` / new review `shared_family_invariants` (F8) | Invariants preserved after all interleavings if **every shared transition preserves all relevant invariants** | Joint preservation is the central unproved premise for actual runtime effects. The theorem is a sound induction schema, not a proof that SC-06/08/25/26 runtime operations satisfy `hJoint`, or that any security-critical side channel is in the joint action alphabet. |

## Severity-ranked consequence and proposed discharge

**High — credential separation (19 scenarios).** Existing `SO_PEERCRED` tests and typed approver roles test one broker interface. They do not prevent direct process, filesystem, container escape, or a trusted deputy bypass. Implement real privilege boundary on a deployment host, then negative-test role impersonation, FD passing, same-UID bypass and restart. Record trusted UID configuration and signer custody.

**High — honest usefulness (18 scenarios).** The original frozen SC-01 0.25-second VM trial fails 0/64 baseline and 0/64 mediated on TCG (see `gateway/vm/receipts/usefulness-20261008-linkfix.json`); do not reinterpret this as a monitor regression, new success or runtime security bound. Obtain authorized hardware-accelerated guests or separately preregister new workload/protocol, then replay.

**High — exclusive effect path (11 scenarios), implementation correspondence.** The newly implemented `trusted_stack.effect_release` appends exact reviewed bytes to SQLite in one atomic transaction, but cannot mediate arbitrary Linux/network/bank effects. New bounded Python/Lean differentials test **models**, not the actual runtime transition relation. Need a pre-effect OS/effect adapter with an exact forward simulation, independent receiver idempotence and audited bypass attempts.

**High — complete observation, measured miss rates.** Model observation channel and worst-case monitor kernels are not proven complete. Holdout tests with independent equipment and an explicit receiver observation inventory are needed. No amount of successful `#eval` or source-parity testing closes this premise.

**Medium — independent human review.** Self-audits and CI are not independent third-party acceptance. Assign separate reviewer to inspect elaborated `#print` output, quantifiers, hidden definition assumptions, and test-to-theorem mapping. Sign review packet and publish exact source hashes; not done.

## Reproduce the bounded controls

```bash
lake exe cache get
lake build ControlStack.Scenarios.SC06OneUse ControlStack.Scenarios.SC08Exec ControlStack.Scenarios.SC25Audit ControlStack.Scenarios.SC26Transaction
lake env lean reviews/statement-fidelity-2026-10-09/Counterexamples.lean
python3 tools/bounded_model_diff.py
python3 scenarios/SC-26/harness/lean_difftest.py -n 200
python3 -m unittest discover -s trusted_stack -p 'test_*.py' -v
```

All conclusions are conditional, and these are not necessarily fully elaborated theorem normal forms. Check `#print` and `#print axioms` for each theorem in the pinned toolchain, inspect environment roles and primitive specifications, and require no `sorryAx`. No independent audit endorsement is claimed.
