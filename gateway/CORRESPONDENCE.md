# Gateway ↔ `ControlStack/CovertChannel.lean` correspondence (v1 prototype)

Theorem premise (`covert_bound`): everything the receiver observes from an episode is one value v ∈ V, a finite set
fixed before the episode; the secret m is uniform and independent of the shared seed ω and of the receiver's inputs.
Conclusion: P(receiver recovers m) ≤ |V| / |M| for every shared seed, adaptive randomised encoder and decoder.

| premise | how the gateway discharges it | evidence | status |
|---|---|---|---|
| receiver's view is a single value | `deliver()` returns one tuple per channel, only after `close()` | `test_no_early_read_and_no_late_send` | RUNTIME_VALIDATED (tests) |
| view lies in a FIXED finite V | exact-type enum validation; fixed slots; NULL padding | `test_invalid_payloads_blank_episode`, `test_views_lie_in_declared_space` | RUNTIME_VALIDATED (tests) |
| refusals are not a signal | any refusal blanks the episode to all-NULL, which is itself in V; the sender is never told | `test_*` (refusal paths) | RUNTIME_VALIDATED (tests) |
| no message-count or timing channel | fixed slot count per channel; delivery only at close; no timestamps | design + tests | RUNTIME_VALIDATED (tests); timing of `close()` is the harness's |
| no other channel (files, network, processes, env) | `act()` denies everything and blanks the episode | `test_side_actions_denied` | prototype only: real isolation needs OS-level enforcement (SANDBOX2F1 bind order) |
| |V| ≤ 2^budget | static check at configuration | `test_budget_refused` | RUNTIME_VALIDATED (tests) |
| m independent of ω and receiver inputs | eval design (red team draws m after the receiver is set up) | `redteam_eval` | assumption of the eval; in deployment UNRESOLVED (shared training/context could correlate) |
| receivers are machines only | scope decision (John, 2026-10-07) | — | humans OUT of scope |

Red-team check: the optimal reachable-view encoder (k = 13) achieves 0.229 ± 0.006, its exact predicted value
1885/2^13, under the Lean bound 2197/2^13 = 0.268. Design point: 16-bit budget, 32-bit secret → P ≤ 2^-16
(`design_point`).

Not yet: the gateway is unverified Python; the bound holds only if the deployment routes EVERY inter-instance artefact
through it and the harness provides OS isolation. Next: run the gateway inside a sandboxed multi-agent harness and
prove a Lean model of `send`/`deliver` refines the view map (implementation correspondence, P0).
