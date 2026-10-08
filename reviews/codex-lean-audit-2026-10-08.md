# Statement-fidelity audit: ScenarioARepair, EgressGate, GatewayModel (2026-10-08)

Read-only review at HEAD `964993c`. Method: 5-bin test (binders, carriers, definition bodies, consumption, axioms).

## Axioms and compilation (all three files)

- `lake env lean` compiles all three files with no errors. GatewayModel has only lint warnings: deprecated `if_true` at line 79, and unused simp arguments at lines 108, 150 and 183.
- `#print axioms`:
  - ScenarioARepair (3 theorems): `[propext, Classical.choice, Quot.sound]`.
  - EgressGate (6 theorems): a subset of `[propext, Quot.sound]`.
  - GatewayModel (3 printed theorems): a subset of the standard three. The unprinted helpers (`blank_absorbing`, `push_dist`, `buf_le`, `deliver_eq_embed`) are dependencies of the printed theorems, so they are covered.
- A grep of the three files plus `CovertChannel.lean` for `sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque` finds nothing.
- File hashes match their pins:
  - CovertChannel and GatewayModel match `assurance/covert-channel-gateway-v2.json`.
  - EgressGate (`b491ec0a…`) matches `assurance/egress-boundary-v1.json`.
  - ScenarioARepair (`df5bf078…`) matches `gateway/scenario/results/local-full.json`.
  - `egress/results/lean-axioms.txt` matches its pinned hash and the current output.
- `egress/check_lean.sh` is sound for its purpose:
  - Each theorem needs exactly one axiom report, and its axioms must be in the allowlist. A `sorryAx` or `ofReduceBool` would therefore fail it.
  - `set -e` aborts the script if `lean` fails.
  - Nits:
    - It calls bare `lean` rather than `lake env lean`. This is fine only because the file imports `Std` alone.
    - The textual grep covers only `sorry|admit`; the allowlist check covers the rest.
    - The `.` in `'ControlStack.EgressGate\.'` is unescaped. This is harmless.

## 1. ControlStack/ScenarioARepair.lean

| Theorem | Verdict | Reason |
|---|---|---|
| `transcript_card` (l.11) | OK | `Fin 5 → Option (Fin 8)` has 9^5 = 59049 elements. This matches `contract.json`: 8 enum values plus blank gives 9 views per episode, 5 episodes, lifetime cardinality 59049. |
| `repair_recovery` (l.14) | OK | `M = Fin (2^32)` matches the 32-bit secret. ρ, enc and dec are universally quantified, and their only hypotheses are `IsDist`, which are satisfiable. Uniformity of m and m's independence from ω are built into `successProb`. The encoder is any joint law on whole 5-episode transcripts, so it covers adaptivity. The decoder sees the whole lifetime transcript, which conservatively treats the lineage as one receiver. |
| `repair_target` (l.23) | OK | Arithmetic is correct: 59049/2^32 ≈ 1.375e-5 ≤ 2^-16 ≈ 1.526e-5. |

Carrier and modelling notes (ISSUE-minor):

- **Not derived from the gateway model.** `View := Option (Fin 8)` (l.8) is posited directly. It is not obtained from `GatewayModel.deliver` with `slots = 1` and `|S| = 8`, although the two have the same cardinality: Σ_{j≤1} 8^j = (8+1)^1 = 9. Nothing in Lean ties the 9-view carrier to the gateway semantics or to the raw sender actions across five episodes.
- **The fixed five-episode count is load-bearing.** `Transcript = Fin 5 → View` encodes "exactly five episodes, each delivering a view".
  - If the number of delivered episodes could vary and the receiver could observe it, the right carrier is Σ_{e≤5} 9^e = 66,430.
  - 66,430 > 2^16, so the 2^-16 target would fail: 66430/2^32 ≈ 1.547e-5.
  - `run.py` currently loops a fixed `episodes_per_lineage`, and PREREG line 28 states "always executes five episodes". However, neither the README nor the manifest lists this as a premise.
- **Finite shared seed.** Ω must be finite. This is standard and only a nit.

Consumption:

- `gateway/scenario/README.md` lines 5–7 and PREREG lines 18–20 correctly make the bound conditional on complete observation, lineage, independence and correspondence. README line 25 explicitly certifies no runtime 2^-16 guarantee.
- ScenarioARepair is not listed in `assurance/covert-channel-gateway-v2.json` (neither the file hash nor the theorem ids). CI (`ci/covert/check.sh` line 22) and `gateway/scenario/check.sh` do check it.

## 2. ControlStack/EgressGate.lean

| Theorem | Verdict | Reason |
|---|---|---|
| `lookup_pinned` (l.26) | OK | Correct, but weak. It proves only that the returned peer is *some* peer in the table, not the peer bound to `key`. The docs (FIDELITY line 6) claim only "chooses peers from the fixed table", so they are accurate. |
| `direct_no_effect` (l.94) | ISSUE-minor | True by the `step` guard `s.active && !safe s.topology` (l.84) together with Invariant.1. No network semantics are involved. `Topology` is five uninterpreted Bools (l.38–44). The sandbox-origin branch is unreachable from any state that satisfies the Invariant. |
| `step_safe` (l.100) | ISSUE-major (definition body / consumption) | The proof is correct. However, the actions that could break the invariant are neutralised by definition rather than analysed. `.tamperPolicy => s` is the identity (l.87). `.startGateway supplied` sets `gatewayUp := decide (supplied = p)` (l.76): a gateway given a different policy simply never serves. The Python `load_policy` (`egress/proxy.py` lines 14–26) checks only shape and serves any well-formed policy, so this equality check has no implementation counterpart. FIDELITY lines 4–6 say the model "exposes … policy tampering, gateway startup", which reads as if tampering were analysed. It is assumed. |
| `trace_safe` (l.126) | ISSUE-major (inherits) | The action list is correctly universally quantified, and the policy `p` is fixed before the adversary acts. The content is the same as `step_safe`. No initial-state lemma is given; the premise is satisfiable (for example `active := false, attempts := []`) but not exhibited. |
| `failed_launch` (l.132) | OK | Definitional (`active := safe t`), and stated honestly. |
| `crash_closed` (l.135) | OK | One step only: crash followed by one request. Restart via `startGateway p` is allowed, and FIDELITY does not claim more. |

Definition-level gaps (modelling, versus the documented Python), all minor:

- **Peer type.** `Peer` has `address : String` and `protocol : String` (l.8–11). The Python peer is `[ip, port]`. Nothing models "numeric loopback" (README line 6).
- **Lookup semantics.** Lean uses first-match list lookup; Python uses exact dict lookup. Because only membership is proved, the difference does not matter.
- **Effect granularity.** Effects are connection attempts only. Bytes, CONNECT tunnels and downstream hops are absent. This is documented in the docstring at l.72–73 and in README lines 18–23.
- **Derived instances.** Both `BEq` and `DecidableEq` are derived for `Peer` and `Rule`. They are unused, but having both risks `==`/`=` divergence later.

Consumption:

- The manifest assumption `model_trace_invariant` (THEOREM_VERIFIED, not ledger-gated) is accurate.
- The CI fields disagree. `egress-boundary-v1.json` line 70 says "No remote GitHub CI run claimed", but `egress/README.md` lines 49–52 claim a passing remote CI run at `b30177e`.

## 3. ControlStack/GatewayModel.lean

`gateway/CORRESPONDENCE.md` exists.

| Theorem | Verdict | Reason |
|---|---|---|
| `blank_absorbing` (l.47) | OK | Blank status is absorbing under every action. |
| `other_blanks` (l.61) | OK | Any `other` action anywhere in the trace yields the all-NULL view. Invalid sends and overflow also blank by `step` (l.31–37), but no theorem states that. |
| `push_dist` (l.74) | OK | Standard pushforward lemma. |
| `gateway_bound` (l.84) | OK, with minor notes | Quantifier order is right: the gateway (`valid`, `slots`, `L`) is fixed first, then every ρ, enc and dec. The encoder is a law on raw traces, the decoder sees only `deliver ∘ run`, and the RHS is (|S|+1)^slots/|M|. Minor notes: (a) the trace is exactly length L (`Fin L → Act R`), but the header comment (l.5) says "bounded length L"; (b) `Fintype R` restricts the encoder to finitely supported payloads. See below. |
| `buf_le` (l.111) | OK | |
| `deliver_eq_embed` (l.138) | OK | Every delivered view is a j-prefix followed by NULLs, with j ≤ slots. |
| `gateway_bound_reachable` (l.153) | OK | The RHS Σ_{j≤slots} |S|^j matches `Channel.alphabet()` in `gateway/gateway.py`. |

On note (a) under `gateway_bound`: no action pads a trace without blanking it, because `other` and invalid sends both blank. Shorter traces are therefore not embedded in the length-L statement; they are covered only by instantiating smaller values of L separately. Mixed-length encoders are not literally covered.

Modelling gaps versus `gateway/gateway.py`, all minor and noted as UNRESOLVED `python_refines_model`:

1. **One channel versus many.**
   - Lean models a single channel. Python allows several channels, with episode-wide blanking and `view_space_size` taken as the product over channels.
   - There is no Lean theorem for the multi-channel joint view.
   - The joint view does lie in the product of per-channel reachable sets, so the product accounting is sound, but that is not proved.
   - `difftest.py` exercises only one channel: S = Fin 4, 3 slots.
2. **No close / UNKNOWN_CHANNEL handling.** Lean has no `close()`, `AFTER_CLOSE` or `UNKNOWN_CHANNEL`.
   - The Lean trace must be read as the pre-close actions.
   - `UNKNOWN_CHANNEL` maps to `other`.
   - Post-close actions in Python do not blank, which is consistent with that reading.
3. **Check order.** Python checks overflow before validation; Lean validates first. Both orders blank, so the outcomes agree.

Consumption:

- `assurance/covert-channel-gateway-v2.json` lists `GatewayModel.gateway_bound` but not `gateway_bound_reachable`. The runtime ledger charge (`Channel.alphabet`, `gateway.py` around line 98) relies on the reachable bound.
- `CORRESPONDENCE.md` line 12 marks "no message-count or timing channel" as RUNTIME_VALIDATED. That is inconsistent with the cache-timing finding (line 35, and scenario README lines 21–25).
- The manifest `claim` string (line 3) states the 2^-16 bound without a "model-only / conditional" qualifier. The verdict is correctly CONDITIONAL with six blockers.

## Recommended fixes

1. **EgressGate, policy integrity.** Make policy integrity an explicit hypothesis rather than a definition. Either:
   - parameterise `State` with a `loaded : Policy` set by `startGateway`, have `request` use it, and add the hypothesis `loaded = p` (trusted host) to `trace_safe`; or
   - keep the model and change the docstring at l.3 and FIDELITY lines 4–6 to say that `tamperPolicy` and wrong-policy startup are *assumed* to have no effect (the trusted-host premise), not modelled.
2. **EgressGate, direct attempts and initial state.**
   - State in FIDELITY that `direct_no_effect` is definitional, given the `safe` flags, and that all isolation content lives in the runtime validator.
   - Add `init_invariant : Invariant p ⟨false, t, false, []⟩`.
3. **EgressGate, authority binding (optional).** Strengthen `lookup_pinned` to `∃ r ∈ p, r.authority = key ∧ r.peer = peer`.
4. **ScenarioARepair, derive the carrier.** Derive the 9-view carrier from GatewayModel by proving `Fintype.card (Fin 1 → Option (Fin 8)) = 9`, or better, prove a five-episode raw-trace version: an encoder over `Fin 5 → (Fin L → Act R)`, with the view taken as the pointwise `deliver 1 ∘ run valid 1`.
5. **ScenarioARepair, fixed episode count.** Add "fixed, receiver-unobservable episode count (exactly five episodes always delivered; absent or failed episodes delivered as the blank view)" as an explicit premise in the README and manifest. Note that the variable-count carrier, 66,430, exceeds 2^16.
6. **Manifest coverage.** Add `ScenarioARepair.lean` (hash and three theorem ids) and `GatewayModel.gateway_bound_reachable` to `assurance/covert-channel-gateway-v2.json`.
7. **GatewayModel, trace length.** Generalise `gateway_bound` / `gateway_bound_reachable` to an arbitrary `Fintype T` with a map `T → List (Act R)`, which covers variable length. Otherwise, change "bounded length L" at l.5 to "length exactly L".
8. **GatewayModel, multi-channel.** Add a multi-channel theorem (episode-wide blank, joint view in the product of per-channel reachable sets), or state single-channel scope in CORRESPONDENCE and gateway.py.
9. **Docs.**
   - Reconcile the egress manifest `ci` field with README lines 49–52.
   - Downgrade the CORRESPONDENCE line 12 timing status.
   - Qualify the covert manifest `claim` as model-conditional.
10. **Lint cleanup in GatewayModel.** Replace `if_true` with `ite_true`, and drop the unused simp arguments at l.108, l.150 and l.183.
