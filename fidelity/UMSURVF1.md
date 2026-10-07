# Fidelity audit (orchestrator): UMSURVF1, honeypot-test survival

Statement: `ledger/UMSURV.lean`, frozen as UMSURVF1. Informal source: DESIGN.md v1 §3 (T3b, T3c, T3c').

| conjunct | informal claim | binders and hypotheses | classification | verdict |
|---|---|---|---|---|
| 1 | survival depends on the rule only through h = Σ q φ | `Z` finite, `q φ : Z → ℝ`, `κ`, `n j`, `Σ q = 1` | `Σ q = 1` is SOURCE (q is the mediated honeypot law). No nonnegativity is needed: the identity is algebraic, so it is stronger than the source | faithful |
| 2 | hard slack gives the binomial CDF | `h : ℝ` (any real), `n ns` | TYPING. Holds for all real h as a polynomial identity, which is stronger than h ∈ [0,1] | faithful |
| 3 | a constant schedule gives (1−kh)^n | `h k : ℝ`, `n` | TYPING; polynomial identity | faithful |
| 4 | h·P(Bin(n,h) ≤ s) ≤ (s+1)/(n+1) | `0 ≤ h ≤ 1` | SOURCE (h is a probability). Covers s ≥ n | faithful |
| 5 | h(1−kh)^n ≤ 1/(k(n+1)) | `0 ≤ h ≤ 1`, `0 < k ≤ 1` | SOURCE (k = 1/n_s with n_s ≥ 1) | faithful |
| 6 | survival ∈ [0,1] | `h ∈ [0,1]`, `κ i ∈ [0,1]` | SOURCE | faithful |

**Strategy class.** The monitor enters only through the honeypot pass rate h. That is the stateless-monitor assumption
(A1) fixed per shared seed ω. Reviewer A's red team notes that shared-seed applications must condition on ω first. UMPROTF1
does this: `protocolCat` sums over ω with `surv (push M PH) (φ ω) …`.

**Witness.** The hard-slack instance (27/64) is non-degenerate. The soft witness only evaluates the closed form 5/101,
which Reviewer A calls a weak certificate, but a non-degenerate soft instance exists, e.g. conjunct 3 at h = 1/4, k = 1/5.
Acceptable for infrastructure.

**Novelty.** Classical (truncated binomial first moment; exchangeability bound (s+1)/(n+1)). Infrastructure lemma for
the control stack.
