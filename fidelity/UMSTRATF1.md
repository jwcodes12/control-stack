# Fidelity audit (orchestrator): UMSTRATF1, stratified honeypots with class-aware shutdown

Statement: `ledger/UMSTRAT.lean` with Reviewer A's strengthened Witness (frozen d2b4b11507cc; the Claim text is unchanged
from my v1 draft apart from formatting). Depends on UMPROTF1. Proof: 218 lines, isolated prover agent; gated, standard axioms.
Red team: Reviewer A pass and Reviewer C pass, both on the frozen text after the stale-verdict reset.

| element | classification | note |
|---|---|---|
| content-only mediator: the view law of x is `K (c x)`, with `IsKernel K` | SOURCE (strong design requirement) | honeypots and attacks of one class have *identical* mediated laws |
| stratified test: m honeypots per class e ∈ Es with mediated law `K e`; class-aware hard slack s_c; survival = ∏_e surv(K e, φ, hardKill s_c, m, 0) | SOURCE / MODELLING | the product encodes independent per-class tests with separate counters (A1, A3) |
| `∀ x, Bad x → c x ∈ Es` | SOURCE: coverage of every bad class (A9) | costs \|Es\|·m honeypots; UMNOGOF1 is the price of failing it |
| ρ, φ, π, r ∈ [0,1], any b, N | SOURCE (same strategy class as UMPROTF1) | |
| (b) attainment needs decodable K and N ≥ 1, b ≥ 1 | SOURCE | the value binCDF(m, s_c, t)·(1 − r + r t) is the per-class analogue of UMPROTF1's T3* |

**Reading.** Every colluding pair has risk ≤ (1 − r) + r(s_c+1)/(m+1), with no factor for the number of classes. The
realistic-budget table (DESIGN v1 §5) shows the gain when the honest monitor misses honeypots: n_h = 100, α₀ = 5%,
k = 8 gives 0.163 vs 0.415 for the global iid counter.

**Witness.** Bool classes, 12 honeypots per class, slack 1: catastrophe probability ≈ 0.064 > 0, below 2/13.
Non-degenerate.

**Novelty.** Per-stratum application of the counting bound: elementary. As a design recommendation for honeypot
protocols (class-aware slack), it appears not to be stated in the untrusted-monitoring literature. Calibrated:
modest, pending the final novelty gate.
