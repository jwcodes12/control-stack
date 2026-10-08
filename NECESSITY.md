# Necessity catalogue: what each witness shows, and what it does not

A witness is a Lean result showing that dropping a premise outright breaks a bound. It does NOT show that the premise
is necessary in every weaker form. This table follows the narrow labels from the circle consultation
(`reviews/circle-consult-2026-10-08/`). Every entry compiles with standard axioms only and has been proved, but not
ledger red-teamed.

## Witnesses

| premise | witness (Lean) | what it establishes | what it does NOT establish |
|---|---|---|---|
| encoder unrestricted on the carrier (bound tightness) | `CovertChannel.attain_embedding` | \|V\|/\|M\| is attained by an injective code; the counting bound cannot be improved | necessity of any modelling assumption |
| secret independent of the shared seed | `Necessity.seed_secret_breaks_covert` (+ `jointSuccess_indep`) | for \|M\| ≥ 2, a secret equal to the seed is recovered w.p. 1 from a constant view, strictly above the independent-secret bound 1/\|M\| < 1 | how much partial correlation costs; a deployment "secret" correlated with shared context is not covered either way |
| complete observation: no side channel | `ScenarioASide.repair_one_bit_attained` | one noiseless side bit (mass 2) attains 2·59049/2^32 > 2^-16 | that every kernel of mass > 1.11 breaks the target (the 1.11 condition is sufficient only) |
| side certificate dominates the JOINT side output | `Necessity.marginal_certs_dont_compose` | outputs R and R⊕m are each independent of m, yet jointly reveal it (success 2× blind) | anything about specific physical channels |
| fixed, unobservable episode count | `ScenarioACore.varObs_breaks_target` | a visible count CONTROLLED BY THE ENCODER gives 66430 views > 2^16 | that a count independent of the secret breaks the target (it need not) |
| no ledger rollback | `LifetimeLedger.restore_breaks` | one restore of an older snapshot breaks the per-lineage cap | that restoration with external accounting is unsafe |
| independent lifetimes (usefulness gate) | `Necessity.correlated_lifetimes_break_gate` | comonotone lifetimes with marginal 9/10 pass w.p. 9/10, not ≤ 1/80 | how much weak dependence costs |
| conditional (not marginal) per-step catch rate | `MultiStep.correlated_nogo` | a seeded monitor with marginal rate c gives survival 1−c for every k, not (1−c)^k | that independence is needed (suitable conditional hazards suffice) |
| hidden audit schedule | `AuditBudget.observable_schedule_nogo` | full advance knowledge of the schedule gives survival 1 when N−B ≥ k | partial observability, which `Leakage.audit_leak_bound` now prices (sound, not tight) |
| audit allocation independent of attacker timing (POLICY COMPARISON, not a premise of any stack theorem; review D3) | `Necessity.exhausted_no_audit`, `fp_exhaustion_breaks_audit` | under first-come flag-triggered auditing, B earlier flags (false positives) leave every later attack unaudited; instance N=4, B=1, FPR 1/2, perfect monitor: survival 7/8 vs 3/4 for the hidden random schedule | the best budget-allocation policy under false positives (pacing, randomised reservation) |
| independent layers (shared score); ILLUSTRATION only, P(A∩A) = P(A), no stack theorem instantiated | `Necessity.shared_score_product_unsound` | two layers fired by one score: joint miss 1/10, not 1/100 | anything about layers with fresh randomness (`ComposeGame` covers those) |
| per-submission (not population) trusted miss | `ComposeBlindSpot` | population miss 1/1000, adaptive content reaches catastrophe w.p. 1 | that the coverage (K, ε) condition is uniquely necessary |
| coverage constants K, ε | `ComposeCoverage.tight_K`, `tight_eps` | each coefficient is separately sharp | simultaneous attainment for the whole composed protocol |
| exact-recovery harm vs coordination | `CovertNoGo.one_bit_coordinates` | one distinguishable bit coordinates a binary action with certainty | anything about the probability of coordination attempts |

`ScenarioASide.bsc_lifetime_fails` is NOT a witness. It shows that a certificate EXPRESSION exceeds the threshold, not
that an attack attains failure.

## Premises with no witness yet

- `trusted_lineage`: the supervisor groups every memory-sharing receiver into one lineage. A witness would be two
  lineages sharing memory that each stay within budget yet jointly exceed it. This is easy; it has not been written.
- `ledger_correspondence` (SQLite atomicity and durability) and `python_refines_core`: these are
  implementation-correspondence premises. A witness here would be a concrete implementation bug, not a theorem.
- The fresh-coins premise of `ComposeGame`: a latent-bit counterexample exists in prose in `COMPOSITION-N1-UMPROT.md`,
  but not yet in Lean.
- "An audit catches with certainty" (imperfect auditors) is open. The false-positive premise now has a witness
  (above). A positive theorem for a paced or randomised-reservation policy under false positives is still open.
- Fixed trace length in `GatewayModel.gateway_bound`: superseded by `GatewayCore.core_bound`, so no witness is needed.

## Adversarial review 2026-10-08

Reviews by Gemini 3.1 Pro and Opus 5.5 are in `reviews/adversarial-2026-10-08/`; the disposition is in
`disposition.md` there. The labels above incorporate them. Main corrections:
- `shared_score_product_unsound` is an illustration only.
- `fp_exhaustion_breaks_audit` is a policy comparison.
- `seed_secret_breaks_covert` is strict for \|M\| ≥ 2 and bridged to `successProb`.
