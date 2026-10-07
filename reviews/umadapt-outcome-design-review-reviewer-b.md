# Hostile review: UMADAPT (adaptive-tester converse) and `Outcome.lean` (outcome-valued VCVio game)

Reviewer: Reviewer B, 2026-10-07. Scratch: `<scratch>/` (all numbers below are exact `Fraction` computations that mirror
the Lean text literally: `n.choose j = 0` for `j > n`, `ℕ` subtraction truncates, `0^0 = 1`, `h ++ [e]` histories, `Bool true = PASS`).
No Lean/lake was run. Scripts: `lean_sem.py` (literal adSurv / adProtocolCat / cat / binCDF), `dp.py` (exact optimal adaptive tester by
DP over class-symmetric states), `check_a.py`, `a_random.py`, `ctr.py`, `sticky.py`, `poly.py`, `minimax.py`/`scan_minimax.py`/`ratio.py`
(single tester vs best-responding colluder), `outcome_check.py`, `game_check.py`, `honest_edges.py`, `witness_check.py`, `pareto_check.py`,
`benign_rec.py`, `misc_check.py`.

## Verdicts

| Part | Verdict | One line |
|---|---|---|
| 1. UMADAPT | **minor** (accept after reframing (c) and adding one risk-valued corollary conjunct) | (a), (b), Witness are TRUE; (c) is true but does not show what the docstring and the brief say it shows: it is a pointwise-in-t counterexample and is NOT a counterexample at the colluder's best t |
| 2. Outcome | **minor on the game and four recursions, major on two conjuncts** | `deployO`/`gameO`/`caughtG`/`haltP`/`complG`, Marginal, DeployLaw, Partition, GameLaw, HonestClaim, Witness numbers are all TRUE; the PL_UMUSEF1 link is not "textual identity" (needs a lemma/conjunct), and `TwoMarginalsClaim` is a conjunction of two independent facts |

No FATAL issue in either part. Two MAJORs (U1, O1/O2 below; O1 and O2 are the same fix family).

---

# PART 1: UMADAPT

## 1.0 What I verified (independent of `numerics/umadapt_check.py`)

* **Truth of (a), by proof.** Fix the exact decoder `g`. For seed `ω ∈ S` and `x` queried, `Σ_z M x z · classRule c g t ω z = t·[c x = c ω]`
  (on the support `g z = c x`), and `1 − φ_ω z = 1 − t·[c x = c ω]` on the support. Let `F_ω^n(h)` be the all-FLAG-continuation mass
  (`F^0(h) = keep h`, `F^{n+1}(h) = Σ_x T h x Σ_z M x z (1 − φ_ω z) F^n(h ++ [(x,z,false)])`). Then `adSurv ≥ F` (all other branches are `≥ 0`;
  needs `T, M, φ, keep ≥ 0`), `0 ≤ F ≤ 1` (needs `keep ≤ 1`, `T`, `M` distributions, `φ ∈ [0,1]`), and `F^0(h) = 1` for all-FLAG `h` (the contract).
  **Lean-friendly induction without Bernoulli:** for every all-FLAG `h`, `G^n(h) := Σ_{ω∈S} F_ω^n(h) ≥ k − t·n`.
  Step: `G^{n+1}(h) = Σ_x T Σ_z M Σ_ω (1 − t[c x = c ω]) F_ω^n(h') ≥ Σ_x T Σ_z M (G^n(h') − t Σ_ω [c x = c ω])`, using `F ≤ 1` and
  `Σ_ω [c x = c ω] ≤ 1` (InjOn). Then `risk = (1/k) Σ_ω adSurv_ω · cat_ω ≥ t · (1/k) G^n([]) ≥ t(1 − tn/k)`, where `cat_ω ≥ t` for `N ≥ 1`
  (first round: seed is `Bad`, PASS w.p. exactly `t` on the support; the FLAG branch is `≥ 0` because `r ≤ 1`).
  Every hypothesis of the Claim is used; none is vacuous.
* **Brute force, all of it exact.**
  * DP-optimal adaptive tester (both contracts: keep = [misses ≤ n_s] and keep = [misses = 0]) on **3240 cells**
    (k ∈ 1..5, n ∈ 0..8, n_s ∈ 0..3, t ∈ {0, 1/8, 1/4, 1/3, 1/2, 2/3, 3/4, 7/8, 1}): **0 violations of (a)**. Edge cells included:
    n = 0, k = 1, t ∈ {0, 1}. Equality (risk = t(1 − tn/k)) holds for n = 0, for n = 1 with n_s = 0 (every k, t; e.g. (2,1,0,1/2) = 3/8, (3,1,0,1/2) = 5/12), and at (2,2,0,1/2) = 1/4; it is strict elsewhere in the grid.
  * **600 random literal-semantics instances** (random decodable mediators with 1–2 views per class, items outside S, benign items sharing a class
    with a seed, random history/view-dependent randomised `T`, random `keep` with the contract, `keep ≡ 0` off all-FLAG, r ∈ {0,1/2,1}, b ∈ 0..2, N ∈ 1..2,
    n ≤ 3, t ∈ {0,1/4,1/2,2/3,3/4,1}): **0 violations**. This covers items (1) of the brief (n = 0, k = 1, t ∈ {0,1}, r ∈ {0,1}, b = 0, N = 1,
    queries outside S, benign queries, keep depending on views).
  * **Witness**: `adProtocolCat = 3/8` confirmed; the arithmetic `1/2·(1 − 1/2·1/2) = 3/8` confirmed.
  * **(c)**: `adProtocolCat … 3 1 1 1 … (classRule id id (3/4)) = 141/512` confirmed (it is also the DP optimum at that cell, so the tester is optimal at t = 3/4);
    `141/512 < 21/64 = 168/512` confirmed. `ctrQuery` pattern semantics match the prose (first-miss re-query; otherwise `true`).
  * **(b)** arithmetic: 0 failures on k ∈ 1..39, n ∈ 1..59; equality iff `k ≤ 2n`. At n = 0, `k/(2n) = 0` in Lean so `min 1 0 = 0`; (b) correctly requires `1 ≤ n`.

## 1.1 Issues

### U1. MAJOR (overclaim): (c) is a pointwise counterexample only; it is not a counterexample at the colluder's best t

Where: the claim line "(c) The multiplier cannot be kept", the docstring sentence "(b) ... the (n_s+1) multiplier of PL_UMLOWERF1 is lost",
and the brief's "by 1.3–1.7× at the colluder's best t".

What is true and what is not.

* PL_UMLOWERF1 states `∀ design, ∀ t, risk ≥ t(1 − tn/(k(n_s+1)))`. (c) refutes exactly this universal statement for adaptive `T`: there are `T, t` with
  `risk(T,t) < curve(t)`. That is correct and is all (c) proves.
* The **optimised** corollary of PL_UMLOWERF1 (`max_t curve(t) = min(1/2, k(n_s+1)/(4n))`) is NOT refuted by (c) in the best-response sense.
  Exact risk of the (c) tester as a function of t (n = 3, k = 2, n_s = 1; r = b = N = 1):
  `risk(1/2) = 11/32 = 0.3438`, `risk(5/8) = 0.3351`, `risk(2/3) = 26/81 = 0.3210`, `risk(3/4) = 141/512 = 0.2754`, `risk(7/8) = 0.1632`, `risk(1) = 0`.
  Its maximum over t is **0.3463 at t ≈ 0.54**, which is **above 1/3 = max_t curve(t)**. So a colluder who picks t after seeing this tester
  (t is not part of the tester's information) gets more than the optimised PL_UMLOWERF1 value. t = 3/4 is not the colluder's best t against it, as the brief suspects.
* This is not an accident of the chosen tester. **At k = 2 no single t-oblivious adaptive tester beats the curve maximum** (exact minimax over testers by double-oracle DP,
  t-grid of 20): `min_T max_t risk` = 0.5440 (n=2), 0.3462 (n=3), 0.2699 (n=4), 0.2183 (n=5), 0.1850 (n=6), 0.1604 (n=7) at n_s = 1, versus curve maxima 0.5, 0.3333, 0.25, 0.2, 0.1667, 0.1429.
  The k = 2 example cannot be upgraded.
* **Correction of my own final-review-2 numbers.** The "adaptive best-t risk" table in `final-review2-reviewer-b.md` §3.1 was `max_t` of the per-t DP optimum,
  i.e. each t was faced by a tester tuned to that t. That is a valid refutation of the optimised corollary *evaluated at the corollary's own fixed t\**
  (the tester may know t\* = k(n_s+1)/(2n), a public function of the parameters), and it is a lower bound on `min_T max_t`, not an upper bound. I did not claim and cannot claim from those numbers
  that a single tester beats the best-responding colluder. I have now computed that directly (next bullet).
* **The strong (best-response) version is true for k ≥ 3, and the smallest cell is (k, n, n_s) = (3, 3, 1).** Exact minimax over a single tester:

  | (k, n_s, n) | min_T max_t risk (grid) | max_t PL_UMLOWERF1 curve | ratio |
  |---|---|---|---|
  | (3,1,3) | 0.4362 | 0.5000 | 0.87 |
  | (3,1,4) | 0.3229 | 0.3750 | 0.86 |
  | (3,1,6) | 0.2288 | 0.2500 | 0.92 |
  | (3,1,12) | 0.1209 | 0.1250 | 0.97 |
  | (4,1,5) | 0.3086 | 0.4000 | 0.77 |
  | (4,3,8) | 0.3560 | 0.5000 | 0.71 |
  | (5,2,8) | 0.3023 | 0.4688 | 0.64 |
  | (6,2,10) | 0.2699 | 0.4500 | 0.60 |
  | (6,3,12) | 0.2794 | 0.5000 | 0.56 |

  A simple explicit tester ("sticky": query fresh classes 0,1,2 in order; after a miss keep re-querying the missed one) is within 1e-4 of the minimax at (3,3,1).
  Its exact risk, checked in the literal Lean semantics (X = Z = Fin 3, identity mediator, r = b = N = 1, uniform seed), is the polynomial
  **`risk(t) = t − t³ + t⁴/3`** (verified at t = 1/3, 1/2, 2/3, 7/10, 3/4, 1 and by degree-7 interpolation), with maximum 0.43707 at t ≈ 0.6943.
  The curve's maximum is 1/2 (at t = 1, because k(n_s+1) = 6 = 2n). So `∀ t ∈ [0,1], risk(t) < 1/2 = max_t curve`. This is the clean best-response counterexample.

**Fix (Lean).** Keep the existing (c) but relabel it as the pointwise failure, add the optimised-t form for the same tester (it is also a counterexample to the
PL_UMLOWERF1 corollary at the corollary's own t\* = 2/3), and add the best-response counterexample as (c2). The (c2) tester:

```lean
/-- sticky tester on three classes: next fresh class until a miss, then re-query the (first) missed class -/
def stQuery (h : Hist (Fin 3) (Fin 3)) : Fin 3 :=
  match h.find? (fun e => e.2.2) with
  | some e => e.1
  | none => if h.length = 0 then 0 else if h.length = 1 then 1 else 2
def stT (h : Hist (Fin 3) (Fin 3)) (x : Fin 3) : ℝ := if x = stQuery h then 1 else 0
def stKeep (h : Hist (Fin 3) (Fin 3)) : ℝ := if misses h ≤ 1 then 1 else 0   -- hard slack n_s = 1
def idM3 (x z : Fin 3) : ℝ := if z = x then 1 else 0

-- (c1) pointwise at the optimised t* of PL_UMLOWERF1's docstring corollary (k = 2, n = 3, n_s = 1: t* = 2/3, min(1/2, 4/12) = 1/3)
(adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool))
    (classRule id id (2/3)) (seedPolicy (Z := Bool)) = 26/81 ∧ (26/81 : ℝ) < 1/3) ∧
-- (c2) best response: every colluder of the family loses to one t-oblivious tester (k = 3, n = 3, n_s = 1)
(Setup (fun _ : Fin 3 => True) idM3 id (univ : Finset (Fin 3)) ∧ AdTester stT stKeep ∧
  (∀ h, misses h ≤ 1 → stKeep h = 1) ∧
  ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3)))
        (classRule id id t) (seedPolicy (Z := Fin 3)) = t - t^3 + t^4/3 ∧
    t - t^3 + t^4/3 < 1/2 ∧
    (1/2 : ℝ) = 1 * (1 - 1 * (3 : ℝ) / ((3 : ℝ) * ((1 : ℝ) + 1))))
```

The inequality `t − t³ + t⁴/3 < 1/2` on [0,1] is a degree-4 `nlinarith` (slack ≥ 0.063). If the 3-class expansion is too heavy, ship (c1) and say in the
docstring "(c) is a pointwise statement: t known to the tester; the best-response version is numerical only (k ≥ 3: table above)".
Do not write "cannot be kept" without that qualification.

### U2. MINOR (must fix before freeze): (b) is detached arithmetic, not the stated consequence

(b) as written never mentions risk. The docstring claim "(b) At t = min(1, k/(2n)) this is ≥ min(1/2, k/(4n))" is a statement about `adProtocolCat`.
A consumption audit will flag it. Add the risk-valued conjunct inside the `∃ g` block of (a):

```lean
  ∀ (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ), 1 ≤ n → AdTester T keep →
    ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N →
      min (1/2) ((S.card : ℝ) / (4 * n)) ≤
        adProtocolCat Bad M T keep n r b N (seedLaw S)
          (classRule c g (min 1 ((S.card : ℝ) / (2 * n)))) (seedPolicy (Z := Z))
```

(derived from (a) at `t := min 1 (k/(2n))` and the arithmetic of (b); (b) may stay as a standalone lemma). Also add the n = 0 case to the docstring: risk ≥ t, so risk = 1 at t = 1.
Remark: for `n < k/2` the optimised value is `1 − n/k > 1/2`, so `min(1/2, ·)` is weaker than what (a) gives; `max(1/2·[..], …)` is not needed but the docstring could say so.

### U3. MINOR: scope of "the (n_s+1) multiplier is lost" and tightness of (a)

* The gap between the adaptive converse and the nonadaptive curve is regime dependent. Exact single-tester minimax / curve max: at k = 3, n_s = 1 the ratio is 0.87 at n = 3 and tends to 1 as n grows
  (0.97 at n = 12); k = 4, n_s = 1, n = 24: per-t optimum 0.0761 vs curve max 0.0833; k = 3, n_s = 1, n = 24: 0.0616 vs 0.0625. The multiplier is genuinely lost for `n ≲ c·k(n_s+1)`
  (for example, ratios 0.56–0.77 at n ≈ 2k with n_s = 2..3, k = 4..6) and is nearly recovered for `n ≫ k(n_s+1)`.
  Say "for n of the order of k(n_s+1) or smaller" in the docstring. (a) is therefore not tight in n_s; it is tight only at n_s = 0 (and then only up to a constant:
  for n_s = 0 survival is `(1/k) Σ (1−t)^{N_ω}`, exponentially smaller than the Bernoulli bound `1 − tn/k`; the optimised truth is about `k/(e n)` against `k/(4n)`).
* "Attained at (2,1,0)" is correct (3/8; Witness). The brief's "36 cells" is a subset of what I ran; fine.
* The docstring's "a honeypot budget n must grow linearly in the number k of decodable bad classes for every adaptive tester" is true for the colluder family, any n_s, any contract-compliant tester:
  to certify risk ≤ ε < 1/2 one needs `n ≥ k/(4ε)` (when `k ≤ 2n`). Keep it, but note it is conditional on exact decodability of the k classes (mediation that merges classes makes k small).

### U4. MINOR: the contract (KeepsAllFlag)

* **Is it the right weakest contract?** It is "completeness": the test never shuts down the monitor on its own perfect transcript (flag every honeypot). That is the weakest *natural* hypothesis
  because the colluder's strategy is FLAG-except-seed-class, so its non-seed behaviour is exactly the perfect-catch transcript. It is satisfied by hard slack (any n_s ≥ 0), soft slack (`softKill`, randomised `keep`),
  class-aware slack (PL_UMSTRATF1), a fraction-of-honeypots slack, and "must flag ≥ n − n_s honeypots". It fails exactly for rules that punish an all-FLAG record: inverse honeypots (benign queries that must be PASSed), benign-flag guards.
  The statement "fails for inverse/benign-flag guards" is right **for this colluder** (it FLAGs every non-seed view, benign included, and is caught with probability ~1). It does not say that testers with benign items are safe: the colluder would
  have to be refined (PASS views decoded as benign). Add that sentence; as written a reader may infer the converse "tests with benign items escape the bound".
* The contract is stronger than needed in two harmless ways: it is imposed on all `h : Hist X Z` (only T,M-reachable all-FLAG records matter; off-path values of `keep` do not enter `adSurv`), and it is exact (`= 1`).
  A robust version costs nothing: `∀ h, all-FLAG h → 1 − δ ≤ keep h` gives `(1 − δ)·t(1 − tn/k) ≤ risk`. Optional extra conjunct.
* Necessity witness (cheap, shows the contract is load-bearing and ties to availability): `wKeepBad h = if misses h = 0 then 0 else 1` (shut down every perfect-catch monitor)
  on the Witness instance gives risk **1/8** (< 3/8; checked), and it is not an `AdTester`:
  `¬ AdTester wT wKeepBad ∧ adProtocolCat … wT wKeepBad 1 1 1 1 … = 1/8`. This is the formal version of "always-FLAG survives every test, so the contract is what UMUSE's completion obstruction is about".
* "keep applied only at the end" is lossless. Early shutdown after a PASS prefix is `keep = 0` on every continuation, which is consistent with the contract (a PASS-containing prefix is not all-FLAG); early *acceptance* is `keep = 1` on all continuations;
  variable-length tests of length ≤ n are covered. A shutdown on an all-FLAG prefix is forbidden by the contract, which is intended.

### U5. MINOR: model generality

* Randomised `T` and randomised `keep` as behavioural kernels on histories that contain the tester's own past queries lose nothing (Kuhn: perfect recall), including correlation of `keep` with earlier internal coins. Views and answers are in `Hist`. OK.
* What is not covered, and should be one sentence in Scope: (i) honeypots interleaved with deployment (online testing); (ii) a tester that sees deployment events or the generator's real attacks (replay); (iii) deterministic monitors (fresh coins per call are used; re-querying the same honeypot is only informative because the colluder is randomised);
  (iv) the tester knows `S`, `c`, `g`, `t`, only the seed is secret (this is the strongest reading for a lower bound).
* The proof uses only `cat ≥ t` (the seed's first PASS is a catastrophe) and independence of test and deployment coins given ω. The halting protocol is not otherwise used. The colluders-do-not-see-the-test assumption is part of the *colluder's* definition (pair is stateless and seed-only) and is the right place for it; seeing the test would only enlarge their options.
* `n` can be read as the length of the **all-FLAG path** (the honest-run cost). The lower bound ignores every path that contains a PASS, so the tester may append unboundedly many extra queries after a first miss and (a) still holds. This is a free strengthening worth one docstring line (sequential/SPRT-style testers with a small honest-run length are covered).

### U6. Quantifier order (item 4): OK, and stronger than needed

`∃ g` precedes `∀ n T keep t r b N`. Since `T` and `t` are both universally quantified, `∀T ∀t ≡ ∀t ∀T`: the statement holds for testers that know `t` (and `S, c, g`); the only secret is the seed. The colluder with `t = min(1, k/(2n))` depends on (n, k) only,
so it is one colluder against all testers of length n. The decoder is fixed before the tester and before `n`; only its values on supports matter (any two decoders agree there). No problem. The only thing that quantifier order does affect is the *counterexample* reading, which is U1.

### U7. INFO: novelty (item 6)

Classical. The technique is "probability that an adaptive procedure hits a uniformly hidden target within n probes is ≤ n/k when the answers are uninformative until the first hit" (Yao's principle, then identical-until-bad / difference lemma), plus the first-moment/union bound.
I did not find the specific "honeypot-budget converse for untrusted monitoring" in the group-testing, property-testing or acceptance-sampling literature; the closest relatives are adaptive group testing for a single defective, needle-in-a-haystack probing lower bounds, and curtailed/sequential acceptance sampling (Wald). None gives the exact statement. Report as infrastructure, modest novelty.
Citations, with what I verified: Shoup, "Sequences of games: a tool for taming complexity in security proofs", IACR ePrint **2004/332** (title/author/id verified by fetch; the difference lemma is its Lemma 1 from memory, body not fetchable); Bellare–Rogaway, "Code-Based Game-Playing Proofs and the Security of Triple Encryption", ePrint **2004/331** (verified; the "identical-until-bad" lemma);
Yao 1977 (FOCS, not fetched); Wald 1945, Ann. Math. Stat. 16(2) (SPRT; from memory); Dorfman 1943, Ann. Math. Stat. 14(4) (group testing; from memory); Du–Hwang, *Combinatorial Group Testing and Its Applications* (from memory);
Greenblatt–Shlegeris–Sachan–Roger, arXiv **2312.06942** (verified: "AI Control: Improving Safety Despite Intentional Subversion"); Gardner-Challis et al., arXiv **2602.20628** (verified: "When can we trust untrusted monitoring? A safety case sketch across collusion strategies").

## 1.2 Frozen conjunct list, Part 1 (proposed)

Inside the `∃ g` block of (a), for `Setup Bad M c S`:

1. (a) unchanged (adaptive converse, `AdTester` with the all-FLAG contract).
2. (a′) NEW: risk-valued optimised corollary at `t = min 1 (k/(2n))`, `1 ≤ n` (U2).
3. (b) arithmetic lemma (may be kept, now a lemma used by (a′)).
4. (c1) the ctr tester, pointwise: `141/512` at t = 3/4 (keep) and `26/81 < 1/3` at t = 2/3 (the corollary's own t\*).
5. (c2) NEW: sticky tester (k, n, n_s) = (3,3,1): `∀ t ∈ [0,1], risk = t − t³ + t⁴/3 < 1/2 = max_t curve` (best-response counterexample), or drop with an honest docstring.
6. Witness: unchanged (3/8, tight) plus NEW necessity witness `¬ AdTester wT wKeepBad ∧ risk = 1/8`.
7. Docstring: replace "cannot be kept" with "false pointwise in t, and false at the best t for k ≥ 3 and n ≲ k(n_s+1)"; add the scope lines of U3–U5.

---

# PART 2: `Outcome.lean`

## 2.0 What I verified (literal distribution semantics, exact Fractions)

I implemented `deployO`, `deploy`, `gameO`, `protocolGame`, `honeypotPasses` as finite-distribution monads with the **same bind order** as the Lean text (`x ← π h; z ← M x; pass ← D z`; `A h x z` after FLAG with `u < b`; `k ← honeypotPasses`),
with random finite kernels (X, Z ∈ {2,3}), history-dependent generators `π(h)`, history-and-view-dependent audit kernels `A(h,x,z)` with recall in {0, 1/5, ..., 1}, PASS probabilities in {0, 1/4, ..., 1}, random `Bad`, seeds `ρ` on up to 3 seeds with seed-dependent `D` and `π`.

* **MarginalClaim** (deploy and game): 300 + 250 instances, equality exact. Branch structure of `deployO` and `deploy` is identical (same do-block, `caught ↦ .caught`, miss ↦ `.catastrophe` corresponds to `!caught`, `.halted/.complete ↦ false`). TRUE.
* **DeployLawClaim**: `Pr[catastrophe] = catG`, `Pr[caught] = caughtG`, `Pr[halted] = haltP`, `Pr[complete] = complG`, `Pr[rejected] = 0`: 300/300 exact, for random n ≤ 4, u ≤ 2, b ≤ 3. The recursions are the right ones. `haltP` is a **character-for-character copy** of `ledger/UMUSE.lean` (`diff` is empty).
* **PartitionClaim**: TRUE **without** any [0,1] constraint. Per step the four terms contribute `φ·1 + (1−φ)·1` (bad PASS: cat 1; bad FLAG with audit: `(1−R) + R`; FLAG without audit: halt 1; benign: continuation), so the identity is polynomial in φ and R; base case `0+0+0+1`. I checked it with φ and R arbitrary rationals (negative, > 1) and kernels with negative entries but row sums 1: 200/200 exact. The two nonnegativity hypotheses in the Lean statement are unused by the proof (harmless). The docstring says "with values in [0,1]"; the Lean statement does not require that (O3).
* **GameLawClaim**: 250 instances, all four non-rejected outcomes and the `rejected` formula exact; also `Pr[catastrophe | gameO] = Pr[true | protocolGame]` (second half of MarginalClaim). The `o ≠ rejected` exclusion is needed and correct.
* **HonestClaim**: 600 random + 1728 edge instances (α₀ ∈ {0, 1/3, 1}, f₀ ∈ {0, 2/3, 1}; n_h ∈ {0,1,3,5}, n_s ∈ {0,1,3,4,6}, b ∈ {0,1,2,3,5,7}, N ∈ {0,1,2,3,4}; seed law on 3 seeds): **0 failures**. Specific edge cases:
  `b ≥ N` (then `binCDF N b f = 1`: terms with `j > N` have `choose = 0`, the truncated `N − j = 0` and `0^0 = 1` never matter); `N = 0` (`binCDF 0 b f = 1`, halted = 0, complete = `binCDF nh ns α₀`); `n_s ≥ n_h` (rejected = 0);
  `n_h = 0` (any α₀); `α₀ = 0` (`binCDF n s 0 = 1`), `α₀ = 1` (`binCDF n s 1 = [s ≥ n]`), `f₀ = 0/1`. All consistent with the Lean `binCDF` text. The benign-support hypothesis is necessary and sufficient for `catastrophe = caught = 0`.
  I also checked the real-recursion identities `haltP = 1 − binCDF N b (flagRate)`, `complG = binCDF N b (flagRate)`, `catG = caughtG = 0` for iid benign `μ`: 300/300.
* **Witness numbers** (literal semantics): `G`: (catastrophe, caught, rejected, halted, complete) = (27/256, 81/256, 37/64, 0, 0), sums to 1. `Gh`: complete 15/16, halted 1/16. `α₀ = 0`, `f₀ = 1/4`, `binCDF 2 1 (1/4) = 15/16`. All correct.

## 2.1 Issues

### O1. MAJOR (overclaim in docstring + missing bridge): the link to PL_UMUSEF1 (b) is not "textual identity of the rate definitions"

The docstring says HonestClaim is "linked by textual identity of `binCDF` and of the rate definitions". Only `binCDF` is textually shared (imported from the Bridge; and `haltP` is a copy). In `Outcome.lean` the rates are `α₀ := (Pr[= true | H >>= M >>= D₀]).toReal` and
`f₀ := (Pr[= false | μ >>= M >>= D₀]).toReal`, i.e. probabilities of ProbComps. The ledger's `missRate M PH φ₀ = Σ_z (push M PH) z · φ₀ z` and `flagRate M μ φ₀ = Σ_x μ x Σ_z M x z (1 − φ₀ z)` are finite sums over kernels.
They are equal only after the law-of-total-probability argument (small, true, but an argument), and `PL_UMUSEF1.honestCompletion = surv(...) · (1 − haltP …)` is related to `Pr[complete]` through `complG = 1 − haltP` on benign streams, which needs `PartitionClaim` plus `catG = caughtG = 0`.
The two Lean projects cannot import each other (v4.35 vs v4.34), so the only available link is copied text **plus** an explicit conjunct that closes the gap. As frozen, HonestClaim is a correct operational statement whose correspondence to the ledger is by reader's inspection.

**Fix (Lean).** Copy `push`, `missRate`, `flagRate` verbatim from PL_UMHSF1/PL_UMUSEF1 and add:

```lean
def push {X Z : Type} [Fintype X] (M : X → Z → ℝ) (P : X → ℝ) : Z → ℝ := fun z => ∑ x, P x * M x z
def missRate {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (φ₀ : Z → ℝ) : ℝ :=
  ∑ z, push M PH z * φ₀ z
def flagRate {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (μ : X → ℝ) (φ₀ : Z → ℝ) : ℝ :=
  ∑ x, μ x * ∑ z, M x z * (1 - φ₀ z)

/-- the operational rates are the ledger's rates (law of total probability) -/
def RateLinkClaim : Prop :=
  ∀ (X Z : Type) [Fintype X] [Fintype Z] (H μ : ProbComp X) (M : X → ProbComp Z) (D₀ : Z → ProbComp Bool),
    (Pr[= true | H >>= M >>= D₀]).toReal =
      missRate (fun x z => (Pr[= z | M x]).toReal) (fun x => (Pr[= x | H]).toReal)
        (fun z => (Pr[= true | D₀ z]).toReal) ∧
    (Pr[= false | μ >>= M >>= D₀]).toReal =
      flagRate (fun x z => (Pr[= z | M x]).toReal) (fun x => (Pr[= x | μ]).toReal)
        (fun z => (Pr[= true | D₀ z]).toReal)

/-- the deployment recursions on an iid benign stream are the ledger's (a)/(b) -/
def BenignRecursionClaim : Prop :=
  ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ₀ : Z → ℝ) (μ : X → ℝ) (b N : ℕ),
    (∀ x, (∀ z, 0 ≤ M x z) ∧ ∑ z, M x z = 1) → (∀ x, 0 ≤ μ x) → ∑ x, μ x = 1 → (∀ x, 0 < μ x → ¬ Bad x) →
    (∀ z, 0 ≤ φ₀ z ∧ φ₀ z ≤ 1) →
    haltP Bad M φ₀ (fun _ => μ) b N 0 [] = 1 - binCDF N b (flagRate M μ φ₀) ∧
    complG Bad M φ₀ (fun _ => μ) b N 0 [] = binCDF N b (flagRate M μ φ₀)
```

(`BenignRecursionClaim`'s two lines are PL_UMUSEF1 (a) in the same text; checked numerically.) Then reword the docstring: "linked to PL_UMUSEF1 by the textual copies `haltP`, `missRate`, `flagRate`, `binCDF` and the conjuncts RateLink and BenignRecursion".

### O2. MAJOR (meaningless coupling): `TwoMarginalsClaim` is a conjunction of two unrelated facts, not two marginals of one experiment

* Conjunct 1 is `EndToEndClaim` transported along `MarginalClaim`; it quantifies over *all* colluding `(ρ, D, π)`. Conjunct 2 is `HonestClaim` at `ρ = pure ()`, a *different* `(D₀, μ)`. The two share only the protocol constants `(H, M, A, n_h, n_s, b, N)`. Nothing relates the colluding monitor
  of conjunct 1 to the honest monitor of conjunct 2, so there is no single run in which a safety event and an availability event are both measured, and no inequality between them. The docstring line "safety and availability are then two marginals of ONE experiment" is false of this claim (it is true only of `DeployLawClaim`/`GameLawClaim`, which give the whole five-outcome law of any single pair).
  The conjunction is derivable from two already-frozen claims.
* Also, the Witness does not instantiate it: `G` and `Gh` use different `(D, π, b, N)`, so joint satisfiability of the hypotheses of TwoMarginals (L-domination of bad views and benign `μ` support, same protocol) is never exhibited.

**What does couple them operationally** is the exact identity of PL_UMUSEF1 (c')/(P) for the view-blind pair, here with a view-blind monitor built **without any new ProbComp**: `D_blind := fun _ => H >>= M >>= D₀` (ignores the view, fresh independent draw, so `Pr[PASS] = α₀` on every view). I verified, on 400 random instances (N ≥ 1, recall exactly r at the root history), both
`risk(blind pair) = binCDF nh ns α₀ · (α₀ + [0<b](1−r)(1−α₀))` and the exact identity
`binCDF N b f₀ · risk(blind pair) = (α₀ + [0<b](1−r)(1−α₀)) · Pr[complete | honest game]`, with 0 failures. Consequence: any risk certificate `Xc` that bounds every colluding pair satisfies `q · Pr[complete] ≤ binCDF N b f₀ · Xc`, a genuine Pareto constraint for the one protocol.

**Fix (Lean).** Replace `TwoMarginalsClaim` by:

```lean
/-- operational Pareto obstruction (operational form of PL_UMUSEF1 (c') and (P)): one protocol, the view-blind
colluder `D_blind` (its honeypot PASS rate equals the honest monitor's α₀), and the honest pair -/
def ParetoClaim : Prop :=
  ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (H μ : ProbComp X) (M : X → ProbComp Z) (D₀ : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) (r : ℝ) (x₀ : X),
    (∀ x, Pr[= x | μ] ≠ 0 → ¬ Bad x) → Bad x₀ → 1 ≤ N →
    (∀ z, (Pr[= true | A [] x₀ z]).toReal = r) →
    let α₀ := (Pr[= true | H >>= M >>= D₀]).toReal
    let f₀ := (Pr[= false | μ >>= M >>= D₀]).toReal
    let q := α₀ + (if 0 < b then (1 - r) * (1 - α₀) else 0)
    let Gb := gameO Bad (pure ()) H M (fun _ _ => H >>= M >>= D₀) (fun _ _ => pure x₀) A nh ns b N
    let Gh := gameO Bad (pure ()) H M (fun _ => D₀) (fun _ _ => μ) A nh ns b N
    (Pr[= Outcome.catastrophe | Gb]).toReal = binCDF nh ns α₀ * q ∧
    binCDF N b f₀ * (Pr[= Outcome.catastrophe | Gb]).toReal = q * (Pr[= Outcome.complete | Gh]).toReal ∧
    (∀ Xc : ℝ,
      (∀ (D : Unit → Z → ProbComp Bool) (π : Unit → Hist X Z → ProbComp X),
        (Pr[= Outcome.catastrophe | gameO Bad (pure ()) H M D π A nh ns b N]).toReal ≤ Xc) →
      q * (Pr[= Outcome.complete | Gh]).toReal ≤ binCDF N b f₀ * Xc)
```

(`N ≥ 1` is needed: at N = 0 the blind risk is 0 while `q·complete > 0`. `α₀ · complete ≤ Xc·binCDF …`-style corollary follows since `q ≥ α₀`.) Keep `EndToEndClaim` (via Marginal) and `HonestClaim` as separate frozen claims; add a joint witness: take the honest instance of the Witness (`Dh`, α₀ = 0 is degenerate; use the enriched one below) with `x₀ = true`, `H = pure true`, identity mediator, perfect audit (r = 1), and check the three conjuncts. If a single-experiment coupling beyond this is wanted, say so explicitly; the only natural one (a mixed stream of benign tasks and attacks under one `D`) has `Pr[complete] = 0` on any run containing an attack by construction, so it carries no information beyond the five-outcome law.

### O3. MINOR: PartitionClaim docstring vs Lean, and "partition" needs nonnegativity

The docstring requires φ, R ∈ [0,1]; the Lean statement has neither (and is true without them, see 2.0). The Lean statement is the stronger, fine. But "a probability partition" additionally needs each recursion ≥ 0, which is true under [0,1] hypotheses and is not stated.
Fix: reword the docstring to "sum to 1 for any real φ, R, π, M with unit row sums", and add `PartitionNonnegClaim`: under `∀ z, 0 ≤ φ z ∧ φ z ≤ 1`, `∀ h x z, 0 ≤ R h x z ∧ R h x z ≤ 1`, nonneg kernels, each of the four recursions is `≥ 0` (induction; sums of products of nonnegatives).

### O4. MINOR: Witness does not exercise the test factor; add edge instances

The honest instance has `α₀ = 0`, `n_s = 0`, so `binCDF(3,0,0) = 1` and `Pr[rejected] = 0`: the `binCDF nh ns α₀` factor and the `rejected` formula of HonestClaim are never non-trivially instantiated. Add an enriched honest instance (verified): same stream and honeypots, honest monitor PASSes the honeypot view `true` w.p. 1/4 and the benign view `false` w.p. 3/4, `n_h = 3, n_s = 1, b = 1, N = 2`:
`α₀ = 1/4`, `f₀ = 1/4`, `binCDF 3 1 (1/4) = 27/32`, **complete = 405/512, halted = 27/512, rejected = 5/32** (sum 1). Also one `b ≥ N` and one `N = 0` instance (complete = `binCDF nh ns α₀`, halted = 0). The existing numbers are correct.

### O5. MINOR: availability as full-run completion

Documented in the file; I only add that `halted` at round N−1 and at round 1 are the same outcome. If availability is to be linked to usefulness later, `halted (j : ℕ)` (round index) gives `E[completed rounds]` for free; not needed now.

### O6. INFO: assumptions inherited and not re-examined

Rational ProbComp probabilities, absorbing shutdown on a catch, no benign audit false positives, seed-independent audit, stateless monitor: as in `Refinement.lean`. `Pr[rejected | deployO] = 0` and the `o ≠ rejected` guard in GameLawClaim are correct. `GameLawClaim`'s rejected formula uses total mass 1 of `honeypotPasses` (true for ProbComp without failure). The `Fintype Outcome` instance (explicit `elems`, `complete` field by `cases x <;> simp`) is fine.

## 2.2 Frozen conjunct list, Part 2 (proposed)

Freeze unchanged: `Outcome` (+ `Fintype`), `deployO`, `gameO`, `caughtG`, `haltP` (verbatim copy of PL_UMUSEF1), `complG`, **MarginalClaim**, **DeployLawClaim**, **PartitionClaim** (docstring fixed), **GameLawClaim**, **HonestClaim**.
Add: `push`/`missRate`/`flagRate` copies and **RateLinkClaim**, **BenignRecursionClaim** (O1); **PartitionNonnegClaim** (O3); **ParetoClaim** replacing `TwoMarginalsClaim` (O2); Witness extended with the enriched honest instance, a `b ≥ N` and an `N = 0` instance, and a joint instance for ParetoClaim (O4, O2).
Docstring: replace "two marginals of ONE experiment" and "textual identity of … the rate definitions" with the accurate statements above.

---

# Fixes in priority order

1. **U1** reframe (c): pointwise (existing), optimised-t at t\* = 2/3 (`26/81 < 1/3`), and the best-response counterexample (3,3,1) `risk(t) = t − t³ + t⁴/3 < 1/2`; remove "cannot be kept" / "at the colluder's best t" wording that (c) does not support.
2. **O2** replace `TwoMarginalsClaim` by `ParetoClaim` (operational PL_UMUSEF1 (c')/(P)); fix docstring.
3. **O1** add `RateLinkClaim` + `BenignRecursionClaim` with verbatim copies; fix the "textual identity" sentence.
4. **U2** add the risk-valued optimised corollary (a′) so (b) is consumed.
5. **U4** add the necessity witness (`¬ AdTester wT wKeepBad`, risk 1/8) and the "fails for this colluder" wording; optional δ-robust version.
6. **O3, O4, U3, U5** docstring/Witness polish (partition wording, enriched honest witness, regime scope of "multiplier lost", scope lines).
