# Hostile review: Leakage, Necessity, Gate, GateClients, Lease (current copy at /var/tmp/cs-review-opus)

Legend: **[checked]** = I read it in the source or traced it by hand against the Lean definitions. **[inferred]** = my reasoning, not machine-checked. Per the rules, I built nothing and ran nothing.

## Verdict

1. I found no unsound proof. The defects are in the models, the event and witness definitions, and the prose.
2. Lease is the weakest model. The agent declares its own cost, so zero-cost work is unlimited, and an unauthenticated `fork` revives a worker whose lease was revoked.
3. Two Necessity witnesses do not show what NECESSITY.md says: `fp_exhaustion_breaks_audit` (a policy comparison) and `seed_secret_breaks_covert` (non-strict, empty at |M| = 1).
4. The leak-pricing results (`audit_leak_bound`, `sc01_adaptive_target`, `covert_side_bound`) have no Lean instance with a nontrivial leak. They are non-vacuous only for near-zero leaks.
5. The mathematics is classical (maximal-leakage chain rule, absorbing feedback, reference-monitor invariants). What is new is the packaging.

## Defects (ranked)

**D1. `Lease: lease_safe`. The agent chooses the cost, so a lease does not bound how much work runs.** [checked]
`Op.work (w cost)` is labelled "agent", but the header says "Costs are declared by the gate". The guard is `spent + c ≤ budget ∧ total + c ≤ cap`.
- Counterexample: `[issue ⟨0,0,100⟩ 1] ++ replicate n (work 1 0)` with cap 0 admits n work effects, and `lease_safe` still holds.
- An agent can also split one job into many small declared costs.
- Fix: a gate-side `cost : Kind → ℕ⁺` (or `1 ≤ c`), plus a bound on the count of work units.

**D2. `Lease: revoke_absorbing` / `fork`. Revocation stops a lease id, not a worker.** [checked, hand trace]
`fork w w'` has no check on who issues it or whether `w'` already exists, and the newest holder entry wins.
- Trace: `[issue ⟨0,5,100⟩ 1, issue ⟨1,5,100⟩ 2, revoke 0, fork 2 1, work 1 3]`.
- Result: worker 1's lease is revoked, yet `work 1 3` is admitted, under lease 1.
- Any worker can re-point any other worker onto its own lease. Nothing models which principal may draw on which lease.
- `restart` being a no-op is the durability premise holding by definition, the same pattern as `tamperPolicy`. `LifetimeLedger.restore_breaks` shows that this premise matters.
- Fix: forks only to fresh children, issued by the parent; revocation per lineage.

**D3. `Necessity: fp_exhaustion_breaks_audit` is mislabelled.** [checked]
No theorem has the premise "honest rounds do not consume audits". Under the random schedule, most audits do land on honest rounds.
- The witness compares two different mechanisms:
  - first-come flag-triggered auditing, against an attacker that always attacks the last round;
  - the uniform schedule.
- The comparison flips with the false-positive rate: at FPR = 0 the same policy gives survival 0 < 3/4.
- The premise actually at stake is that the audit allocation is independent of the attacker's timing.
- `exhausted_no_audit` is a one-line unfolding.
- Fix: relabel the row, or state a theorem with that premise and drop it.

**D4. `Necessity: seed_secret_breaks_covert` is vacuous at |M| = 1 and uses the wrong functional.** [checked]
- The conclusion is `… = 1 ∧ card Unit / card M = (card M)⁻¹`. It has no strict inequality and no `Nontrivial M`, so at `M = Unit` it witnesses nothing.
- It uses `jointSuccess`, and no lemma ties `jointSuccess (ρ ⊗ uniform)` to `successProb`. So it is not `covert_bound` with a premise dropped.
- A secret equal to the seed is a degenerate case.
- Fix: add `[Nontrivial M]` and `1 > |M|⁻¹`, add the bridging lemma, and add a family where the secret equals the seed with probability α.

**D5. `Leakage: audit_leak_bound` / `audit_leak_prod` have no witness with a leak.** [checked; instance inferred]
The only instance is `audit_adaptive_hidden` (`Z = Unit`, mass exactly 1), so the leak pricing is untested in Lean.
- A satisfiable instance in which the bound is attained:
  - N = 2, B = 1, k = 1.
  - Round 0 leaks [0 ∈ S] through a binary symmetric channel with crossover ε.
  - The attacker attacks round 0 if the leak says "not audited", otherwise round 1.
  - `hcons` holds. The least certificate has round masses 2(1−ε) and 1.
  - The bound is ½·2(1−ε) = 1−ε, and the true survival is also 1−ε.
- Freeze it as the `Witness`.

**D6. `Leakage: survInd` is the wrong event.** [checked]
- `Disjoint S (attackSet t) ∧ k ≤ #attackSet t` requires ALL attacks to go unaudited. The prose says "completes k attack steps unaudited", so attacking again after k successes and being caught counts as failure.
- This is harmless for `audit_adaptive_hidden`, because truncation stays inside the σ class.
- For `audit_leak_bound`, the truncated kernel needs its own certificate, and no lemma covers it.
- Fix: define success as "the first k attacks are unaudited", or prove a truncation lemma.

**D7. `Leakage: audit_leak_bound` `hdom` ranges over every `S`, not only `#S = B`.** [checked; looseness inferred]
- Example: the leak `z = decide (Even #S)` carries zero information on the support. With a natural kernel it still forces `cl ≥ 1` on both values of z, which doubles the bound every round.
- The only escape is the unobvious trick `K S := 0` off the support.
- The same pattern appears in `covert_seq`: `c` cannot depend on ω, although the decoder knows ω.
- Fix: restrict to the support, and let the certificate depend on ω.

**D8. `sc01_adaptive_target` / `covert_side_bound` are non-vacuous only near "no side channel".** [arithmetic inferred]
- The condition `∏λ ≤ 65536/59049` allows about 0.15 bits of maximal leakage over five episodes. For a binary symmetric side channel that means crossover ≥ 0.4895 (consistent with `bsc_lifetime_ok`/`_fails`).
- Domination is worst-case over the hidden history. So a cache written in episode 1 and read out over episodes 2–5 pays full capacity every round, and the bound is then vacuous.
- `Z` must be finite (timing would need quantising, which is not modelled), and the episode count is fixed.
- No Lean instance has a nontrivial `Z`.

**D9. `GateClients: Approval.approval_safe`, `Artifact` do not separate actors.** [checked]
- `approve` and `review` sit in the same op alphabet as the agent's ops, and the theorems range over all traces.
- So "the model gives the agent no operation that adds an approval" is false. What is proved is "executions ⊆ approvals, whoever approved".
- There is no restart op, so the durability of `used` and a monotone clock are assumed by omission.
- Fix: an agent predicate, a proof that agent-only traces never extend `approvals` or `reviewed`, and a restart-loses-`used` witness.

**D10. `Gate: Spec`, `withHalt`, `halt_absorbing`; `GateClients: egressHaltSpec`.** [checked]
- **`Spec` carries no content.** `ok := fun _ _ => True` with `Inv := True` satisfies it for any append-only log.
- **`Spec` has no `init` field.** The dispatch, audit-gate and egress clients get no proof that their initial state satisfies `Inv`.
- **The halt is absorbing by construction.** `if sh.2 then sh` is a sticky bit.
- **No deployed component has it.** EgressGate's own `crashGateway` is not absorbing: `startGateway p` restarts it.
- **"Halting freezes all socket attempts" leaves out live traffic.** CONNECT tunnel bytes are excluded from `Effect` by design, so established tunnels keep moving data.
- **Nothing addresses whether the halt is ever processed (liveness).**

**D11. `Artifact.deployed_is_reviewed`: `hinj` is about the final state.** [checked]
- Trace: `[review true, put true, deploy (), put false]` with a constant hash. The deploy was correct, but the hypothesis fails.
- Fix: state injectivity at deploy time.
- Reviews never expire and are not bound to any context. Deploys can be replayed without limit.

**D12. The `audit_adaptive_hidden` docstring drops premises.** [checked]
"≤ ((N−B)/N)^k" omits `0 < N, k ≤ N`. At N = B = 0, k ≥ 1 the expressions give 1 ≤ 0, because x/0 = 0.

**D13. Minor witness gaps.** [checked]
- `marginal_certs_dont_compose`: "least mass 1", "mass 2 given the first output" and "blind value 1/2" are prose only.
- `comono` is never shown to be a distribution.
- `shared_score_product_unsound` is `if s = false ∧ s = false`, i.e. P(A∩A) = P(A). Remove it from the witness table.

**Fine** [checked]:
- `transfer`, `seq_transfer`, `val_le_cval`, `mass_le_prod`, `cval_live`, `blind_audit`, `episode_dom` and `covert_seq` are correct as stated.
  - ℕ subtraction is harmless: for k > N, survival is 0.
  - `B > N` gives 0 ≤ 0.
- `audit_adaptive_hidden` is correct. σ is behavioural, randomised and fully adaptive, which is complete for finite horizons.
- The AuditDispatch and AuditGate client invariants are reused correctly. EgressGate keeps its known definitional policy integrity.

## Overclaims in prose

- **(a)** Side channels "with feedback and state carried across episodes" are covered only under worst-case domination given the visible history, at under 0.15 bits in total for SC-01 (D8).
- **(b)** "Catch feedback is free" holds only because a catch is perfect and absorbing. With imperfect audits, or audits of honest rounds that the attacker can see, it fails.
- **(c)** "Adaptive attackers gain nothing" is correct, but it is AuditBudget's own modelling remark, and `survInd` is not the prose event (D6).
- **The "full visibility (mass ≥ C(N,B))" endpoint is not proved.**
- **(d)** The "absorbing shutdown obligation (A11; SC-13, SC-25)" is a sticky bit on a wrapper with no deployed counterpart (D10).
- **(e)** "Only collisions an adversary actually produced matter" overstates it: collisions produced after the deploy also void the theorem (D11).
- **(f)** "No replay" relies on a durable nonce store that is not modelled, and on approvals that the agent could equally issue in the model (D9).
- **(g)** Lease:
  - "Forks cannot multiply a lease" holds per lease.
  - "Revocation is absorbing" holds per lease id only (D2).
  - The quota does not bound the work count (D1).
- **(h)** NECESSITY rows:
  - `fp_exhaustion` is mislabelled (D3).
  - `seed_secret` is non-strict (D4).
  - `audit_leak_bound` "not tight" is unshown; the D5 instance is tight.
- **Novelty.**
  - `transfer` is the guessing form of maximal leakage (Issa–Wagner–Kamath), i.e. the min-capacity bound.
  - `seq_transfer` is its adaptive composition / chain rule: compare the composition results in the maximal-leakage literature (arXiv 1903.01777; Issa–Wagner's adaptive-composition result) and channels with memory and feedback (Alvim–Andrés–Palamidessi, JCS 2012).
  - `cval_live` is the standard fact that feedback is constant on surviving paths.
  - Gate, Lease and Approval are reference-monitor guards (Anderson 1972) and textbook nonce checks.
  - The witnesses are a one-time pad, a comonotone coupling and P(A∩A).
  - Nothing here is a new theorem.

## Harness question

The harness would add real value, but not by re-proving anything: every statement compiles. Its value is that the red team and the Witness obligation target exactly the failure mode here, which is vacuity and fidelity in the definitions. D1–D4, D6 and D9 are what a foreign-family vacuity and fidelity pass is designed to catch.

These statements most need the Witness obligation:

1. `audit_leak_bound` / `audit_leak_prod`: the D5 instance.
2. `sc01_adaptive_target` / `covert_side_bound`: an instance with a nontrivial `Z`, for example a binary symmetric side channel with crossover 0.49 per episode.
3. `seed_secret_breaks_covert`: strictness under `Nontrivial M`.
4. `lease_safe`: a bound on the work count. It would fail today, which is the point.
5. `approval_safe` / `Artifact`: a statement that separates actors.
6. Every `Gate.Spec` client: check its `ok` against an independently written intended property, because `ok := True` type-checks.

It is ceremony for `transfer`, the `cval`/`mass` lemmas, `trace_safe`, `halt_absorbing`, `replay_without_nonce`, `collision_breaks` and `shared_score`. Those are inductions or `decide`; the risk sits in the definitions.

## Missing results

1. **Leaks combined with imperfect audits or false positives.** A positive theorem for paced or randomised-reservation auditing, and a version with probabilistic catches, where free feedback no longer holds.
2. **A leak bound that does not compound with N.** Per-round masses of 1+ε give e^{Nε}, but the joint least certificate is at most C(N,B). Prove `min(mass, C(N,B))` or a bound in terms of total leakage.
3. **Halt liveness.** A bounded delay from trigger to halt, agent ops cannot be ordered ahead of it indefinitely, and in-flight tunnels terminate.
4. **Confused deputy across gates.** An agent op that adds no effect but steers a trusted effect (`put`→`deploy`, `request`→`dispatch`).
5. **Lease, done properly.** Authenticated forks, revocation per lineage, gate-assigned positive costs, and a crash/rollback model.
6. **Refinement.** A link from any of these models to the Python, SQL or egress code.
7. **Partial secret–seed correlation** (D4).
