# Claude, round 1: response to `reviews/covert-channel-gateway-review-2026-10-07.md`

Reviewed baseline: `cd0d996`. Changes since: `4d2c494` (Lean gateway model, differential test, sandboxed harness;
written before this review was read) and the commit containing this file (fixes below). All claims below refer to
this commit's tree. Local checks: `lake build` (whole VCVio project) passes; every theorem cited reports only
`[propext, Classical.choice, Quot.sound]`; `gateway/test_gateway.py` 10/10; `gateway/difftest.py` 300 traces, 0
mismatches; `gateway/test_harness.py` 2/2.

## Scope clarification: AGREE
Adopted. `CATASTROPHE-SPEC.md` now opens with "Scope of the claim": the certified property is **bounded exact-message
recovery** of a uniform independent k-bit secret over its lifetime; it explicitly states that a 16-bit channel carries a
1-bit command with certainty and that low-bandwidth coordination is out of scope (P2, needs application invariants).
The manifest's `claim` field carries the same wording.

## P0-1 cumulative budget: AGREE (critical; fixed in the gateway, scoped in the spec)
Correct: v1 charged 16 bits per episode, so a receiver with memory could reconstruct 32 bits over two episodes.
- Lean: `ControlStack/CovertChannel.lean::covert_bound_lifetime`: if the receiver's whole observation is the tuple of E
  episode views, success ≤ ∏_e |V_e| / |M|.
- Gateway: `LifetimeLedger` (`gateway/gateway.py`) charges each episode's exact view-space size against a cumulative
  cap 2^budget per **lineage** (all receivers that can share memory over the secret's lifetime); an episode that would
  exceed it is refused before it starts. Refusal depends only on configuration counts, not on sender behaviour.
- Your adversarial test: `test_lifetime_budget_blocks_two_episode_split`: two 2^16-view episodes for the same lineage;
  the second is refused; another lineage is unaffected.
- Remaining assumption (manifest `lifetime_scope`, UNRESOLVED): the deployment must define lineages correctly. A
  shared store that the gateway does not see would merge lineages; that is the same "only channel" obligation as P0-2.
- Consequence worth stating: a 16-bit LIFETIME budget is severe for usefulness; that trade-off is now explicit.

## P0-2 receiver-visible refusal / diagnostic / timing paths: PARTIALLY AGREE
- Alerts: AGREE, fixed. Alerts are now fixed codes from `ALERT_CODES`; attacker-controlled channel names, action kinds
  and payloads are never stored (`test_alerts_are_fixed_codes`). Alerts go only to the overseer.
- Refusal as a signal: already closed in v1 and kept: any refusal blanks the episode to all-NULL, which is itself in V,
  and the sender is never told (send() never raises to the caller).
- Timing, exit status, stderr, files, network: the two-process harness (`gateway/harness.py`, `4d2c494`) runs sender
  and receiver in separate bubblewrap sandboxes (all namespaces unshared, cleared env, private tmpfs, read-only /usr),
  discards stderr and exit code, caps output, and starts the receiver at sender-start + deadline regardless of the
  sender (fixed schedule). `test_side_channels_closed`: a sender trying /tmp, /dev/shm, code and system dirs, network,
  stderr, duration and exit code transmits nothing (receiver guess empty, view all-NULL).
- PARTIAL because: (a) shared kernel state across sequential sandboxes (page-cache timing, other microarchitectural
  state) is NOT closed; it needs VM-level isolation or cache flushing (CORRESPONDENCE.md, manifest `only_channel`);
  (b) "complete runtime observation alphabet" is argued, not proved: the receiver's inputs are its stdin (the frozen
  view as JSON), its own code, read-only /usr, and the host clock (neutralised only by the fixed schedule).

## P0-3 mutable configuration/state: AGREE (fixed for configuration; the real boundary is the process)
`Schema`, `Channel` are frozen dataclasses deep-validated at construction (primitive enum values int/str/bool only,
non-empty, unique names and values, positive int slots; bool ≠ int); `Gateway` copies channels into a private table at
construction. Python attribute privacy is not a security boundary: in the harness the gateway runs in the parent
process and agents run in sandboxes with no access to its memory (manifest `gateway_isolation`, UNRESOLVED until the
gateway is a separate minimal service). Tests: `test_config_validation_and_exact_budget`.

## P0-4 one-shot snapshot: AGREE (fixed)
`close()` atomically freezes the transcript; later sends/actions raise an AFTER_CLOSE / DENIED_ACTION alert but cannot
change it; repeated `deliver()` returns the identical frozen snapshot. Test: `test_no_early_read_and_frozen_snapshot`
(close, deliver, send, act, close, deliver: identical).

## P0-5 exact arithmetic and configuration types: AGREE (fixed)
Budget is an int; cardinality is the exact integer ∏(|S_c|+1)^slots_c compared with 2^b. NaN/float budgets, empty or
duplicate enums, duplicate names, non-primitive values, zero/negative/bool slots are rejected; boundary 2^b accepted and
2^b + 1 rejected (`test_config_validation_and_exact_budget`). IPC grammar in the harness: JSON lines with exactly
{op, channel, payload} or {op: act}; anything else is a refusal.

## P1-1 Lean theorem is not runtime correspondence: AGREE; partly addressed
- Lean model: `ControlStack/GatewayModel.lean` models step/run/deliver over an arbitrary finite raw-action alphabet;
  `blank_absorbing`, `other_blanks`; `gateway_bound`: every shared seed, randomised adaptive encoder of raw traces
  (any length L) and decoder gives success ≤ (|S|+1)^slots / |M|.
- Correspondence: `gateway/difftest.py` evaluates the Lean model with `#eval` and the Python gateway on 300 random
  adversarial traces: 0 mismatches. This is translation validation by testing, not a refinement proof
  (manifest `python_refines_model`, UNRESOLVED). The model does not yet include close/lifetime ledger; next round.

## P1-2 general attainment: AGREE (fixed)
`attain_embedding`: for any injection e : V → M, the encoder sending e⁻¹(m) on the image and a fixed view otherwise,
with decoder e, succeeds with probability exactly |V|/|M|. So the bound is tight for every |V| ≤ |M|.

## P1-3 reachable views: AGREE (not yet done)
Correct and a genuine gain: sequential fill makes only Σ_{j≤slots} |S|^j views reachable (1885 vs 2197 in the test
schema; the optimal encoder hits 1885/2^13). Planned: prove card(reachable deliver outputs) = Σ_j |S|^j in
GatewayModel and charge the ledger with it.

## P1-4 CI scope: AGREE (fixed, pending first run)
New mandatory job `lean-covert` (`.github/workflows/fast.yml`): a narrow Lake project `ci/covert/` pinned to the same
Lean (v4.34.0) and Mathlib rev as the main project, fetches Mathlib's prebuilt cache, builds CovertChannel and
GatewayModel, and fails if any of the 7 public theorems lacks an axiom report or depends on `sorryAx`. The full VCVio
build stays manual. If the first run fails I will report it in round 3 rather than claim green.

## P1-5 covert manifest: AGREE (fixed)
`assurance/covert-channel-gateway-v2.json`: theorem file hashes and ids, implementation hashes, configuration, tests,
and 8 assumptions: 2 THEOREM_VERIFIED, 6 UNRESOLVED (python_refines_model, only_channel, lifetime_scope,
secret_independence, machine_receivers_only, gateway_isolation). Verdict CONDITIONAL. The checker refuses
THEOREM_VERIFIED before the Lean check passes and has no path to DEPLOYMENT-GRADE while anything is UNRESOLVED.

## Answers to the round-1 questions
- Cross-episode split: feasible in v1; refused in v2 by the lineage ledger; the remaining obligation is defining
  lineages correctly (no unmediated shared memory between receivers).
- Runtime observation alphabet: stdin view (frozen JSON), own code, read-only /usr, host clock (fixed schedule);
  not: alerts, logs, exit codes, stderr, sender files, network. Residual: shared kernel/microarchitectural state.
- Shared interpreter / config mutation / close timing: no in the harness (separate sandboxed processes; harness owns
  close; fixed schedule). The gateway still runs in the harness's Python; a minimal separate service is future work.
- Lean trace property: `gateway_bound` (every raw trace maps into Fin slots → Option S); next: add close/ledger and
  the reachable-set cardinality; connection to the binary is by differential testing for now.
- Narrow claim vs harmful coordination: narrowed to exact uniform-secret recovery now; harmful low-bandwidth
  coordination needs a second, application-specific theorem (P2).
- Narrow Lean CI: yes, `lean-covert`.

## Where I disagree or want a challenge
- I do not think the counting bound needs min(1, ·) in the statement: |V|/|M| ≥ 1 makes it vacuous but true.
- "16-bit lifetime budget" may make the primitive useless for most real coordination tasks between instances;
  challenge welcome on whether a per-lineage budget is the right unit, or whether channels should instead be shaped
  so that they carry no secret-dependent information (deterministic-function-of-public-state channels, ℓ = 0).

DIALOGUE_STATUS: CONTINUE
