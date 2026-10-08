# Adversarial review disposition (2026-10-08)

Reviewers. Both reviewed the Lean source, which the prompt (`prompt.md`) inlined.
- **Gemini 3.1 Pro** (`gemini-3.1-pro-high`), run via agy without falling back to the API. It reviewed the version at
  `28be36e`. Output: `gemini-review.md`.
- **Opus 5.5**, run as a Claude Code subagent (model "opus") in a read-only copy. It reviewed the version that already
  had the Gemini fixes. Output: `opus-review.md`. Opus 5.5 is the SAME family as the author, so it is not a foreign
  red team.
- A first agy attempt at Opus is in `opus-agy-failed.log`. agy no longer offers Opus 4.8, and its Opus 5.5 hit the
  account quota. Owner rule: Opus runs only through Claude Code.

Neither reviewer found an unsound proof. The defects are in models, events, witness definitions and prose.

| id | finding | disposition |
|---|---|---|
| G1 | `Artifact.deployed_is_reviewed` assumed GLOBAL hash injectivity (impossible for a real hash, so vacuous) | FIXED: injectivity only on contents in the run (`Set.InjOn`) |
| G2 | `Lease.leaseOf` first-match + append: reissue and fork onto an existing worker took no effect | FIXED: newest assignment wins; `reissue_takes_effect` |
| G3 / O-D13 | `shared_score_product_unsound` is P(A∩A)=P(A), not a witness | FIXED: relabelled ILLUSTRATION |
| O-D1 | Lease: the agent chooses its cost, so zero-cost work is unbounded | FIXED: `1 ≤ c` required; `work_count_le` (units per lease ≤ budget, total ≤ cap); `zero_cost_refused` |
| O-D2 | Lease: an unauthenticated fork re-points a revoked worker | FIXED: forks only create fresh workers; `revoked_worker_stays_stopped`. Revocation is per lease, and this is stated |
| O-D3 | `fp_exhaustion_breaks_audit` compares mechanisms; it is not a premise witness | FIXED: relabelled "policy comparison" in Lean and NECESSITY.md; notes that FPR 0 reverses the comparison |
| O-D4 | `seed_secret_breaks_covert` is not strict (vacuous at \|M\|=1) and its `jointSuccess` was unbridged | FIXED: `2 ≤ \|M\|` with a strict inequality; `jointSuccess_indep` bridges it to `successProb`. Partial correlation is still open |
| O-D5 | `audit_leak_bound` had no instance with a real leak | FIXED (bound): `LeakWitness.leak_bound` has all hypotheses discharged for a BSC(ε) leak and gives survival ≤ 1−ε. Attainment (= 1−ε) is a hand calculation only |
| O-D6 | `survInd` requires EVERY attack unaudited; the prose said "k steps" | FIXED (prose); a truncation lemma for leaky kernels is open |
| O-D7 | audit domination ranged over all S; the covert certificate could not depend on the seed | FIXED: `audit_leak_bound` (support form, with `audit_leak_bound_all` kept); `covert_seq_seed` |
| O-D8 | SC-01 side bounds are informative only near "no side channel" (about 0.15 bits over five episodes) | DOCUMENTED in the Leakage header |
| O-D9 | Approval/Artifact did not separate actors; nonce durability was assumed by omission | FIXED: `agent_cannot_approve`, `agent_cannot_review`, `Lease.agent_cannot_issue`; `replay_if_nonces_lost` (durability is a premise) |
| O-D10 | Gate `Spec` has no content by itself and no init field; the halt is absorbing by construction; CONNECT tunnels; liveness | DOCUMENTED in Gate.lean and GateClients.lean |
| O-D11 | Artifact injectivity is checked on the final state | DOCUMENTED (conservative but narrower than necessary) |
| O-D12 | `audit_adaptive_hidden` docstring dropped side conditions | FIXED |

Missing results both reviewers named (open):
- damage or harm bounds beyond the survival event;
- policy-tampering resistance (EgressGate);
- an end-to-end mediation proof (no bypass of `step`);
- leaks combined with imperfect audits or false positives;
- a leak bound that does not compound with the number of rounds;
- halt liveness;
- confused-deputy attacks across gates;
- a link from these models to the actual code.

Harness question (both reviewers agree): proofledger adds value for statements, not proofs. The mandatory `Witness`
and the foreign-family statement red team target exactly the defect classes found here: vacuity (G1, O-D4, O-D5) and
model or event mistakes (G2, O-D1, O-D2, O-D6, O-D9). Re-proving would be ceremony.
