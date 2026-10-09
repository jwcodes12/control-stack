# SC-01 priorities — independent second-pass audit (2026-10-08)

This is a **source/claim adversarial audit** of the existing Lean proof statements,
NOT an independent third-party certification or an exhaustive kernel/statement
fidelity proof. All theorem kernels below have been built on the pinned Lean toolchain,
but the quantified assumptions must be matched to a real deployment separately.

| Theorem or group | Precise statement scope checked | What it does **not** establish | Disposition |
|---|---|---|---|
| `SafetyCaseSC01.sc01_case` | Conjunction of a side-kernel exact-recovery inequality, binomial false-pass lemma, fixed observed confidence endpoint, (9^5) carrier cardinality and restore-free ledger bound | No runtime side-kernel dominance, no actual statistical independence of VM lifetimes, no complete receiver-observation inventory, no useful VM at 0.25 seconds | MODEL_ONLY / APPLICATION_BLOCKED |
| `GatewayCore.core_bound` | Quantifies over **finite** seed/secret/action types, a **fixed-length** raw event array, normalized seed/encoder/decoder laws; decoder consumes **only** `finalView` | No elapsed time, process exit status, stderr, management logs, cache, variable schedule or extra receiver observations in theorem carrier | MODEL_ONLY / VIEW_BOUNDARY_OPEN |
| `GatewayCore.refusal_blanks`, `close_freezes` | Reference transition system; refusal already occurred before close and sets `blanked`; frozen snapshot remains constant | Not a proof all operating-system output routes are intercepted; post-close alert count or return time may change | MODEL_ONLY / PYTHON_DIFFERENTIAL_TEST |
| `SafetyCaseSC01.ledger_five` | **No restore** events; each admitted charge exactly 9; initial ledger value one; cap (2^{16}) | No trusted lineage uniqueness across crashes/forks/restore, no rollback resistant external anchor | MODEL_ONLY / ROLLBACK_OPEN |
| `Leakage.covert_seq_seed` | Uniform secret independent of a potentially shared seed; per-seed dominated kernels and decoder distributions | Correlated secret/seed, unconstrained side observations, secret-dependent lifetime horizon | MODEL_ONLY / RANDOMNESS_OPEN |
| `Leakage.audit_leak_bound` | Uniform hidden audit schedule, explicit kernel soundness/catch constraints and certificate domination only over schedule support | Unchecked catch flag correspondence, observable audit schedule, false-positive budget or unbounded causal feedback | MODEL_ONLY / AUDIT_RUNTIME_OPEN |
| `Gate.withHalt` and `HaltLiveness.liveness_if_delivered` | Reference gate effects stop changing after **trusted HALT is delivered**; bounded delivery is a premise | Real scheduler fairness, OS kill success, async harms already issued or all real side effects | MODEL_ONLY / DELIVERY_OPEN |
| `GateClients.Approval.approval_safe` | Exact payload, nonce, expiry and distinguished trusted approval capabilities in model | Real signing key custody or whether approved content is harmless | MODEL_ONLY / KEY_CUSTODY_OPEN |
| `Lease.lease_safe`, `revoke_absorbing` | Modeled atomic shared lease counters and trusted revocation | Real distributed race/rollback prevention, forged identities, external work already started | MODEL_ONLY / LEASE_RUNTIME_OPEN |
| `GateComposition.shared_invariants` | Each shared-state action preserves BOTH initial invariants | Compositional safety if authority crosses gates or a confused deputy bypasses the joint transition relation | MODEL_ONLY / SHARED_STATE_OPEN |

## Concrete new checks

`tools/test_gateway_correspondence.py` is a pure-Python *independently
implemented* reference transition machine (not an import of production gate
state). It enumerates all traces of length 0–5 over seven representative
single-channel actions and 0–3 over ten multi-channel actions, including invalid
payloads, overflowing slots, unrelated actions, unknown channels, early closure
and post-close operations. It checks delivery equivalence against the production
`Gateway`. It also constructs all 21 reachable states for a two-channel example,
checks the actual SC-01 (9^5\le2^{16}<9^6) lifetime ledger, and reconfirms
the saved VM failure without modifying it.

These traces are **bounded and selected**; passing them is not a mechanized
refinement theorem for arbitrary traces. The independent reference transition
model was authored in the same project, so it is not an independent external
review of the formal specification.

## SC-01 usefulness: frozen empirical diagnosis

The saved VM receipt has **0/64 completed lifetimes** under both baseline and
mediated conditions with the frozen **0.25-second per-agent deadline**.
All **320 baseline sender + 320 mediated sender** invocations timed out,
as did all 640 corresponding receiver invocations. Baseline episode wall
median ~2.294 seconds; mediated ~1.931 seconds. These wall times contain
transport, VM scheduling and process costs; they cannot be substituted for
per-agent execution-time distributions or justify a particular new deadline.

**Do not rerun the same gate on this TCG host and treat repeated failure as
progress.** Run `tools/sc01_host_feasibility.py` read-only on prospective
platforms to check host architecture and KVM API. A KVM-capable, aarch64-capable
host would still need a separately configured/provisioned VM pair, verified
guest/host isolation and a genuinely passing **unchanged** 0.25-second task
before declaring usefulness recovered. Any new deadline requires an explicit
separate preregistration and owner decision; historical receipts never change.

Even a future successful usefulness experiment will not prove the theorem's
complete-observation premise. A full confidentiality claim needs evidence
about guest/host cache, clocks, serial/management interfaces, termination
and all colluding receiver-visible channels, or a justified uniform side-kernel
certificate within the stated mass budget.

## Missing independent attestations and owner-dependent gates

- An *independent* reviewer of theorem statements and adversary semantics,
  with a recorded opinion and source/commit binding.
- A trusted runtime mediation implementation/refinement proof, not just
  bounded Python transition agreement. Include all side effects, clocks and
  termination behavior, durable cross-restart and no-rollback assumptions.
- An owner-authorized host with usable native KVM/hardware isolation and
  access to create/provision guests, or an explicitly preregistered protocol
  amendment. No credentials, ACLs, VMs or evidence receipts are changed here.
- A successful 64-lifetime usefulness gate under the chosen frozen or formally
  amended protocol, followed by independent receiver-observation/channel review.

**Disposition: SC-01 stays CONDITIONAL and cannot be marked deployment assured.**
