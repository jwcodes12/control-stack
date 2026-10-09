# Outstanding concrete-to-model refinements (2026-10-09)

This list is a **backlog**, not new proof or runtime evidence. Main already has the
SC-07, 16, 18, 25, 26, 27 and 28 refinements. These eleven runtime-tested
scenarios still need their *own* operational event-machine → Lean abstract
machine refinement. Independent review remains open for all 28 scenarios.

| Scenario | Existing abstract theorem(s) | Essential runtime-to-model obligations |
|---|---|---|
| SC-04 | `ChannelInstances.log_channel/canonical_seq` | Enumerate every emitted log, diagnostic/error response and observable timestamp; prove the runtime canonicaliser's typed output corresponds to the finite template/field view. Prove bypass channels absent or keep `timing_in_view` open. |
| SC-06 | `SC06.sc06_safe` | Formalise writes, reads, derivations, recipient principal and sensitive effects; require canonicalisation on *every* cross-agent read, not just the happy path; test unlabeled/shared-file bypasses. |
| SC-08 | `SC08.sc08_safe/safe_of_sound` | Model execve/execveat, executable-fd pinning, interpreter and script argv, memfd/JIT as explicit exclusions or controlled capabilities; connect loaded bytes to checked digest and policy decision. |
| SC-09 | `SC09.sc09_safe/spawn_attenuates` | Model real UID/GID/capability sets, setuid/deputy transitions, namespaces and privilege broker; keep kernel enforcement and admin-key separation explicit environment premises. |
| SC-10 | `SC10.sc10_safe/policy_admin_only` | Extract policy writes, reads, alternate evaluators and builds from the reference harness; model immutable pinned policy path and atomic decision sequence; prove the evaluator cannot bypass the store. |
| SC-14 | `SC14.sc14_safe` | Model cgroup hierarchical consumption, descendant propagation, tick/expiration/halt and each resource vector separately; link observed meters, monotonic anchor and in-flight consumption to budget accounting. |
| SC-15 | `SC15.sc15_safe/sc15_safe_authenticated` | Model push/amend/review/CI/merge with digest-bound approvals and trusted actor identity; do not identify procedural merge approval with semantic detection of backdoors. |
| SC-17 | `SC17.sc17_safe/SC17Drift.drift_bounded` | Model desired vs live state, reconcile interval and out-of-band writes; prove bounded drift only with measured timing and complete observer; handle between-reconcile exposure. |
| SC-19 | `SC19.sc19_safe` | Model snapshot/version check, restore verification, 2-phase prepare/approval/commit, concurrent writes and irreversible effects; preserve trusted-verifier and versioned-write premises. |
| SC-20 | `SC20.sc20_safe/sc20_safe_authenticated` | Model digest pinning from ingest through quarantine, promotion, freeze and training read; separate provenance-chain integrity from semantic dataset cleanliness. |
| SC-23 | `SC23IsolationV2.sc23v2_safe_authenticated` | Model taint-labelled tool results, derivation/argument flows, exact display and authenticated confirmation before effect; prove no unlabelled planner/deputy path. |

## Acceptance contract for each remaining refinement

1. Freeze the precise runtime version and event semantics. Do not alter old preregistered evidence to fit the model.
2. State an explicit concrete machine, abstraction map and per-event simulation theorem; transfer the scenario's *existing* safety property through the simulation.
3. Add a counterexample in which disabling the relevant check changes the bad-event outcome.
4. Make every runtime assumption explicit, especially credential provenance, instrumentation completeness, kernel behavior, concurrency, timing, byte/digest identity and exception paths.
5. Add the refinement theorem to that scenario's `manifest.json`, `claim.lean`, `ControlStack/Core/TrustRoot.lean` and the generated review/ledger pages. Preserve `implementation_conformance` as a residual root until runtime traces are independently checked.
6. Require a kernel build with standard axioms only, fast/full checks, frozen evidence-pin verification, CI green, and independent human statement-fidelity review before any deployment-assurance label.

An idealized event machine is **not** proof that the Python harness, Linux host,
cloud APIs or physical side-channels implement that machine.
