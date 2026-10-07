# TMCERT v1 + TMGAC v0 hostile design review (Reviewer B 5.5), 2026-10-07

Scope: `reviews/tmcert2-design-review-prompt.md`; drafts `ledger-drafts/TMCERT-v1.lean`, `ledger-drafts/TMGAC-v0.lean` (I diffed them
against the statements pasted in the brief: identical). I did NOT run Lean or lake. Everything marked "checked" is an exact
`fractions.Fraction` mirror of the Lean definitions, in `<temporary path> B-tmcert2/`:

| file | what it mirrors / checks |
|---|---|
| `mirror2.py` | literal mirror: `Game`, `risk` (nature selector `θ n h s a`), `RiskCertUpTo`, `Vstar`, `Vrob`, `honestER`, `checkRiskQ`/`checkLawfulQ` with `Fin.castSucc` = same value / `Fin.succ` = +1, `gameOfQ`/`valOfQ` (zero beyond horizon), `pushK` |
| `t1_q_checker.py`, `t1b_q_nontrivial.py` | 10 000 random tables (N,m,k,t from 0..3, incl. empty): `checkRiskQ = true` <=> `RiskCertUpTo` of the induced real tables, both directions; `checkLawfulQ` <=> `LawfulUpTo`; and `Lawful` for ALL horizons once the check passes |
| `t2_witnesses.py` | TMCERT Witness (checker, lawfulness, 3/4 attained by switching, FxGap 1/2,1/2,3/4, the `Covered` instance) |
| `t3_soundness_tight.py` | (S) with row-local `adm`, history-dependent randomised Red, adaptive nature: 8 623 (n,s) tests, 0 violations |
| `t4_tight_use_abs.py` | (T) attainment by a deterministic time-dependent Markov policy, `0 <= Vstar <= 1`; (TR) attainment by (Markov policy, Markov selector); (U): 0 failures in 400+400+3 585 tests |
| `t5_abs.py`, `t8_hull_abs.py` | (Abs) as stated (3 890 tests, 0 violations); the domination variant needs `V >= 0` (explicit counterexample); hull-dominated variant (4 394 tests, 0 violations) |
| `t6_tmgac.py`, `t7_lip_w_t5.py` | (Z) incl. non-monotone `f`, `f(qd) < f(qa)`, `β` outside `[0,1]`; (UZ) as written AND against GAC Prop. C.2; (Lip), (W) incl. `TA > 0` at `c = 0`; the whole (T5) table; `exV3`; the TMGAC Witness |

GAC source: the local copy `<temporary path>` is arXiv 2409.07985v2 (7 May 2026), read App. B, C.1, C.2 line by line. A WebFetch of
arxiv.org/html/2409.07985v2 returned a non-verbatim summary (it even said Defer counts, which contradicts the paper text), so I rely
on the local v2 text.

---------------------------------------------------------------------------------------------------------------------------

## 0. Verdicts

| statement | verdict | one line |
|---|---|---|
| TMCERT v1 | **MAJOR** (no FATAL, no false conjunct) | every conjunct and the Witness are true; (Q) as a workflow is wrong for plain `decide`; (Abs)+(Vx)+(Q) do not compose into the advertised polytope/interval certificate; (Abs) needs a domination form |
| TMGAC v0 | **MAJOR** (no FATAL, no false conjunct) | (UZ) is a theorem about a mis-transcribed usefulness recurrence: GAC counts audited safe solutions as used, `uGAC` does not; everything else true, two docstring fidelity issues |

Truth summary: I could not falsify any conjunct of either `Claim`, nor either `Witness`. The MAJORs are fidelity / composition /
workflow, not falsity. After the fixes in §3 I would accept both.

---------------------------------------------------------------------------------------------------------------------------

## 1. Truth audit (what was checked, what the edge cases do)

### TMCERT v1

| item | result |
|---|---|
| (S), (S') | proof sketch: induction on n; `n+1 <= N` gives `n < N`; uses `σ >= 0`, `Σσ = 1`, `K >= 0` of the admissible row actually chosen. 8 623 random tests with row-local `adm`, selector depending on `(n, h, s, a)`, 0 violations. Unused: `cat >= 0`, mass `<= 1`. |
| (Fx) | literally (S) at `Θ = Unit`; hypothesis "certificate for ALL admissible `th'`" is stronger than needed (only `th` is used). True, MINOR. |
| (FxGap) | `1/2, 1/2, 3/4` exact (index 1 is the first round: `risk` at `n+1 = 2` reads row `n = 1` first). True. Max over all time-dependent selectors is 3/4 = `Vrob`. |
| (Obs) | trivial; true. "lawful Red policy" in the docstring clashes with `Lawful` (game). |
| (T) | `Vstar` cert (no lawfulness needed), `<=` every cert (needs `K >= 0` from `Lawful`), `0 <= Vstar <= 1` (needs mass `<= 1`), attained by the deterministic policy `σ h s = argmax at n = N - h.length - 1` (400 random games incl. ties: 0 failures). Policy for `h.length >= N` is arbitrary and never evaluated. True. |
| (TR) | same with `A × Θ`; the optimal selector depends only on `(n, s, a)`, so the length-invariance clause is easy. 400 random: 0 failures. True. Only `adm = True` (see M3 on how row-local finite `adm` is encoded). |
| (U) | induction; needs `K >= 0` only at `a₀`; 3 585 tests, 0 violations. True. Over-hypothesised: `K >= 0` for ALL actions. |
| (Q) | **Fin indexing is right**: `i.castSucc` = n, `i.succ` = n+1; `V 0` is the `Fin` literal 0 = `⟨0,_⟩` = `valOfQ ... 0`. 10 000 random tables, both directions, 0 discrepancies. Edge cases: `N = 0` (only `V 0 >= 0` checked), `m = 0`, `k = 0`, `t = 0` all give `true` vacuously and the real cert is vacuous too, consistent. `checkLawfulQ` passing implies `Lawful` for EVERY horizon (rows are 0 beyond N); the statement only claims `LawfulUpTo N` (see m2). |
| (Vx) | pure convexity, true, no sign hypotheses needed. |
| (Abs) | true as stated (3 890 tests). Proof: induction, `Kc >= 0`, regroup `Σ_x' Kc(x') V(α x') = Σ_s' pushK(s') V(s')` (`Finset.sum_fiberwise`), apply the cert at `(n, α x, b, th)`, `n < N`. `pushK` with an empty fibre is 0, so EQUALITY forces the abstract row to have 0 mass on abstract states with no concrete preimage (restrictive, not wrong). Covered at `n >= N` is not required and not used. |
| Witness | `checkRiskQ`: i=0: th0 `0 <= 1/2`, th1 `1/2 <= 1/2`; i=1: th0 `1/2 + 1/4 = 3/4 <= 3/4`, th1 `1/2 <= 3/4`. True. `checkLawfulQ` true (all rows have mass exactly 1). 3/4 attained by `θ n = if n = 1 then 0 else 1`. The `Covered` instance is the model-0 row (n=1: cat 1/2, pushK 1/4+1/4 = 1/2; n=0: cat 0, pushK 1/2+1/2 = 1) and has concrete risk 1/2. All true. Note: the Witness never exhibits a concrete row that is NOT literally a table row, i.e. it does not exercise the interesting case (M3). |

### TMGAC v0

| item | result |
|---|---|
| (L) | all four row types checked by hand and numerically: true; hypotheses are exactly what is needed (`TD <= 1` for `cat >= 0`, `TA <= TD` for `K >= 0`, `0 <= TA` for mass, `FA ∈ [0,1]`). |
| (Z) | **identity in all cases**: 0 mismatches over 400 random instances x 6 values of β (including β ∉ [0,1], non-monotone `f`, `f(qd) < f(qa)`, `qd < qa`) with only `f 0 = 0` and `qa m 0 = 0`. Algebra: `1 - risk` of the `gac` rows equals `zGAC` termwise, no lawfulness or ordering needed. The `n+1` indexing is right (`risk (n+1)` reads `qa (n+1)`; `zGAC (m+1)` reads `qa (m+1)`). |
| (UZ) | **true as a statement about the Lean `uGAC`** (0 mismatches) but `uGAC` is NOT GAC's usefulness: see M1. |
| (M) | convexity; true. |
| (Lip) | **true, and N is tight**: derivation `d_n <= |b-b'| + d_{n-1}` using `X_a ∈ [0,1]` (needs both `Vstar`-style bounds and mass `<= 1`, i.e. exactly `Lawful`). 3 000 random lawful Boolean games: max ratio `|Δ|/(N|Δb|)` = 1.0 (attained); chain game `cat(true)=1`, `K(false)=1` has slope ratio -> 1 as b -> 0, so the constant cannot be improved in general. |
| (W) | true, including `TA > 0` at `c = 0` (2 000 random lawful instances, 0 failures). Reason: backdoor row minus continue row = `(1 - TD + TA)(1 - V) >= 0` because `V <= 1`. |
| (T5) | `risk(constRed b) = 3/4 b - 21/32 b² + 5/32 b³` on a 401-point grid, `13/50 - p(b) = (5/32)(b - 4/5)²(13/5 - b) >= 0` on [0,1] (so the bound and equality at 4/5 are right); `clocked3` = `11/32` = `Vstar exG3 3 1`; `13/50 < 11/32`. True. |
| `exV3` | all 3 rows x 2 states x 2 actions check, tight at every entry; also a certificate for any horizon (V = 1 beyond n = 3). True. |
| Witness | `Lawful exG3` true; certificate true; `<= 11/32` for every Red follows from (S) + Lawful; the 5th conjunct is a bare instance of (Z): `zGAC = 63/64 = 1 - risk` (m=2, c=1, β=1/2). True but see m5. |

---------------------------------------------------------------------------------------------------------------------------

## 2. Issues

### M1 (MAJOR, TMGAC) `uGAC` / (UZ) is not GAC's usefulness: audited safe solutions are USED in GAC

Where: `uGAC`, the reward `fun _ n c => 1 - qd (n + 1) c.val` in (UZ), the sentence "a solution counts only when it is run, not deferred or
audited", and `numerics/tmgac_check.py` (`honest(... rew = 1 - qd)`).

Why wrong. GAC v2 App. C.2: "We can identify when Blue uses a solution from U as cases in which Blue either takes the action ⟨Run⟩, or
takes the action ⟨Audit⟩ and no human error is made." Case 3 of the proof: audit, no error, "the solution is used. The game continues
having used up one audit coin"; `e[m,c] = (1-q^d)(1+e[m-1,c]) + (q^d-q^a)(0+e[m-1,c]) + ((1-p^FPR) q^a)(1+e[m-1,c-1]) + (p^FPR q^a)(0)`. Prop. C.2 as
printed has the explicit term `(1 - p^FPR_H) q^a_{m,c} (1)`. App. B: `R_Use((m,c,False), a, (m-1,c',False)) = 1 for a ≠ Defer`. Main text: usefulness
is "the proportion of solutions submitted", and an audited safe solution is submitted. Only Defer (the trusted model's solution) is
not counted. With a perfect auditor the correct reward is `(1 - qd) + qa`, so the correct recurrence is

    u^{c+1}_{m+1} = (1 - qd) + qa + qa · u^c_m + (1 - qa) · u^{c+1}_m,        u^0_{m+1} = (1 - qd) + u^0_m.

The Lean `uGAC` drops the `+ qa`. Exact example (checked): `qa = 1/2` (c > 0), `qd = 3/4`, m = 2, c = 1: Lean `uGAC = 1/2`, GAC
Prop. C.2 = **5/4**; the two differ in 1 383 of 3 442 random cells. The bridge theorem is true, but it bridges `gac` to a recurrence that is not
the one it is attributed to, and the TMGAC claim "(UZ) Bridge to GAC's usefulness (App. C)" is false as labelled. The 300-instance
numerics did not catch it because `tmgac_check.py` has the same transcription (`1 - qd`) on both sides.

Fix (Lean):

```lean
noncomputable def uGAC (qa qd : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | m + 1, 0 => (1 - qd (m + 1) 0) + uGAC qa qd m 0
  | m + 1, c + 1 => ((1 - qd (m + 1) (c + 1)) + qa (m + 1) (c + 1))
      + qa (m + 1) (c + 1) * uGAC qa qd m c + (1 - qa (m + 1) (c + 1)) * uGAC qa qd m (c + 1)

-- (UZ)
(∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ), (∀ m, qa m 0 = 0) → ∀ (m : ℕ) (c : Fin (C + 1)),
    honestER (fun _ : Unit => gacQ C f qa qd) false
      (fun _ n c => 1 - qd (n + 1) c.val + qa (n + 1) c.val) (fun _ _ _ => ()) m c [] = uGAC qa qd m c.val)
```

(The hypothesis `qa m 0 = 0` is needed at c = 0 so that GAC's literal boundary `(1 - q^d)` is the reward; I checked the corrected reward
against Prop. C.2 on all random cells, 0 mismatches.) Docstring: "(UZ) the expected number of honest solutions USED: run, or audited and
found safe (perfect auditor); deferred solutions are replaced by the trusted model's and do not count." Fix `numerics/tmgac_check.py`
(`rew = 1 - qd + qa`, `uGAC` as above) and re-run.

### M2 (MAJOR, TMCERT (Q) workflow) plain `decide` will not evaluate the ℚ checker; use `decide +kernel` or ℕ-scaled tables

Where: the docstring "written with lists, so the kernel can evaluate it by `decide`", `checkRiskQ`, `checkLawfulQ`, and the Witness
(`checkRiskQ 2 1 1 2 wCat wK wV = true`). I did not run Lean; this is from the toolchain sources (v4.34.0).

Why. The `decide` tactic's default path (`Lean/Elab/Tactic/Decide.lean`, `doElab`) does `withAtLeastTransparency .default <| whnf s` in the
ELABORATOR. In core `Init/Data/Rat/Basic.lean` the arithmetic is `@[irreducible]`: `Rat.mul` (l.168), `Rat.inv` (l.191), `Rat.add` (l.259),
`Rat.sub` (l.295), `Rat.ofScientific` (l.132). `1/2` is `Rat.div` = `Rat.mul _ (Rat.inv _)`, and `sumQ`'s `acc + _` is `Rat.add`, so the
`Decidable` instance gets stuck and `decide` reports "failed to reduce to true/false". The kernel does not honour `@[irreducible]`, so
`decide +kernel` (path `doKernel`) works; `Nat.gcd` is a kernel GMP builtin, `List.finRange n = ofFn id = Fin.foldr` is structural
(`Fin.foldr.loop` has `termination_by structural`), `Fin.castSucc/succ` are trivial, `&&`/`List.all` iterate in tail position. So the
design is salvageable but the stated workflow is wrong. Further cost notes: tables defined by long `if` chains are looked up by
re-evaluation (no memo in the kernel), so total cost is cells x table-size; define tables by formulas (as `gac` rows) or `List.getD`
lookups, not by enumeration, for N ~ 100.

Fix A (minimal): state in the docstring and in the Witness that instances are discharged by `decide +kernel`:

```lean
theorem witness_check : checkRiskQ 2 1 1 2 wCat wK wV = true := by decide +kernel
```

Fix B (recommended, robust, and it also removes two side conditions): since cat, K, V are all nonnegative, scale to ℕ so that plain
`decide` works (Nat ops are accelerated in both `Meta.whnf` and the kernel) and nonnegativity of cat, K, V holds by type:

```lean
/-- integer-scaled certificate check: cat/D, K/D, V/E, with D E : ℕ positive; all arithmetic in ℕ -/
def checkRiskN (N m k t D E : ℕ) (cat : Fin t → Fin N → Fin m → Fin k → ℕ)
    (K : Fin t → Fin N → Fin m → Fin k → Fin m → ℕ) (V : Fin (N + 1) → Fin m → ℕ) : Bool :=
  (List.finRange t).all fun th => (List.finRange N).all fun i => (List.finRange m).all fun s =>
    (List.finRange k).all fun a =>
      decide (cat th i s a * E + (List.finRange m).foldl (fun acc s' => acc + K th i s a s' * V i.castSucc s') 0
              ≤ V i.succ s * D)
```
(`cat/D + Σ (K/D)(V/E) <= V'/E` times `D·E`.) Soundness bridge: cast to ℝ with divisions; require `0 < D`, `0 < E` and `0 < t`, `0 < k` in the
theorem. `checkLawfulN` is `cat + Σ K <= D` (nonnegativity free). The (T5) instance needs D = 4, E = 64; GAC-scale tables need D = 10^k. If ℚ
is kept for readability, keep both and prove `checkRiskN` is the ℚ check after scaling.

Also: put the `0 < t` and `0 < k` guards inside the Boolean (`0 < t && 0 < k && ...`), or `checkRiskQ` returns `true` for the empty
model set / empty action set and the "certificate" is vacuous (m3).

### M3 (MAJOR, TMCERT (Abs)/(Vx)/(Q)) the advertised "interval or polytope certified by finitely many vertex checks, deployed through an abstraction" does not follow from the stated conjuncts

Three separate gaps, one repair.

(a) (Vx) is a bare inequality. Nothing says that a certificate for finitely many vertex models is a certificate for the polytope
`Θ_hull = simplex`. (S) with finite `Θ` and `adm = True` (what `checkRiskQ` certifies) only covers a nature that picks VERTEX rows; interior
rows need `Θ` = weights, a `hullGame`, and the lemma below. The docstring ("an interval or polytope of monitor rates is certified by
finitely many vertex checks") is therefore an overclaim of what is proved.

(b) (Abs) requires the concrete row to EQUAL an admissible abstract row. With the (Q) pipeline the admissible rows are the finitely many
vertex rows, so a concrete row has to equal a vertex; a concrete attack whose detection probability lies strictly inside the interval
is not covered. Equality is the wrong relation. The right one: concrete row DOMINATED by a convex combination of admissible rows
(concrete `cat` and pushed `K` componentwise `<=`; extra mass is safe termination). Domination needs `V >= 0`, otherwise it is FALSE (explicit counterexample, checked):
abstract S = {0,1}, one action/model, row at (n,0) = (cat 0, K(→1) = 1), no admissible row at s = 1 (so `V(·,1)` is unconstrained), V(0,·)=0, V(1,0)=0,
V(1,1) = -1, V(2,0) = -1 satisfies `RiskCertUpTo 2`; concrete game one state α ↦ 0, cat 0, K 0 is dominated (pushK(1) = 0 <= 1) but has risk
0 > V(2,0) = -1. Add `∀ n <= N, ∀ s, 0 <= V n s` (cheap: have `checkRiskQ` test it for all n, not just n = 0).
With hull-domination no `K >= 0` on abstract rows is needed (only `V >= 0`). I tested this version (4 394 tests, 0 violations).

(c) `Covered` is required at every concrete state, reachable or not, and every concrete action. That is correct for a worst-case
guarantee but should be stated as the lab's burden (§4).

Fix (Lean):

```lean
/-- every concrete row is dominated by a convex combination of admissible abstract rows -/
def CoveredHull {Sc Ac S A Θ : Type} [Fintype Sc] [Fintype Θ] [DecidableEq S] (N : ℕ) (Gc : Game Sc Ac)
    (α : Sc → S) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) : Prop :=
  ∀ n, n < N → ∀ x ac, ∃ (b : A) (lam : Θ → ℝ), (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧
    (∀ i, lam i ≠ 0 → adm n (α x) b i) ∧
    Gc.cat n x ac ≤ ∑ i, lam i * (G i).cat n (α x) b ∧
    ∀ s', pushK α (Gc.K n x ac) s' ≤ ∑ i, lam i * (G i).K n (α x) b s'

-- (Abs): replaces `Covered`; equality is the special case lam = indicator, slack 0
(∀ (Sc Ac S A Θ : Type) [Fintype Sc] [Fintype Ac] [Fintype S] [Fintype Θ] [DecidableEq S] (N : ℕ)
    (Gc : Game Sc Ac) (α : Sc → S) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ)
    (σc : RHist Sc Ac → Sc → Ac → ℝ),
    (∀ n, n < N → ∀ x ac x', 0 ≤ Gc.K n x ac x') → (∀ n, n ≤ N → ∀ s, 0 ≤ V n s) →
    CoveredHull N Gc α G adm → RiskCertUpTo N G adm V → IsPolicy σc →
    ∀ n, n ≤ N → ∀ x h, risk (fun _ : Unit => Gc) (fun _ _ _ _ => ()) σc n x h ≤ V n (α x))

-- (Vx) wired to the game, so nature may pick interior rows
noncomputable def hullGame {S A ι : Type} [Fintype ι] (Gv : ι → Game S A) (lam : ι → ℝ) : Game S A where
  cat n s a := ∑ i, lam i * (Gv i).cat n s a
  K n s a s' := ∑ i, lam i * (Gv i).K n s a s'
def Simplex {ι : Type} [Fintype ι] (lam : ι → ℝ) : Prop := (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1

(∀ (S A ι : Type) [Fintype S] [Fintype ι] (N : ℕ) (Gv : ι → Game S A) (V : ℕ → S → ℝ),
    (∀ i n s a s', 0 ≤ (Gv i).K n s a s') → RiskCertUpTo N Gv (fun _ _ _ _ => True) V →
    (∀ n s a lam, Simplex lam → ∀ s', 0 ≤ (hullGame Gv lam).K n s a s') ∧
    RiskCertUpTo N (hullGame Gv) (fun _ _ _ lam => Simplex lam) V)
```

Keep the bare convexity statement as a lemma, not as a conjunct. Per-cell polytopes with different vertex counts are encoded in the
finite-table checker by padding with repeated vertices (t = max vertex count), so `adm = True` suffices in (Q); say so in the docstring.

### Smaller issues (MINOR unless stated)

m1. `K >= 0` hypotheses in (S), (S'), (U), (Abs) are over all `n` (and, in (U), all actions). `gameOfQ` is 0 beyond N so the composition
with (Q) goes through, but state them for `n < N` (and `a₀` in (U)); it removes a needless lemma at every use.

m2. (Q) concludes `LawfulUpTo N`, but (T) and (TR) require `Lawful G` (all horizons). Because `gameOfQ` rows are 0 beyond N, `checkLawfulQ`
actually gives `Lawful`; state `∀ th, Lawful (gameOfQ N m k t cat K th)`. Without this, (Q) cannot be fed into (T)/(TR), i.e. a checked table
has no tightness theorem. Checked: 0 violations of lawfulness at horizons up to N+5 on every passing table.

m3. `checkRiskQ`/`checkLawfulQ` return `true` for `t = 0` or `k = 0` (vacuous certificate; `Vrob` would need `Nonempty Θ`). Add the guards (M2).

m4. (Fx): hypothesise the certificate only for `th`; as written it demands certificates for all admissible models though it uses one.

m5. TMGAC Witness conjunct 5 is a bare instance of (Z), yet the docstring says "the bridge value zGAC ... is computed". Say `= 63/64`
(checked: `zGAC = 1 - risk = 63/64`), so the example has content. The Witness also does not exercise any `adm` and does not go through
the checker (see m9).

m6. (Z) fidelity docstring. The Lean `zGAC` is the correct recurrence from GAC's case analysis (App. C.1, perfect auditor: terms
`β f(q^a)`, `β(f(q^d) - f(q^a))`, `(1-β)q^a`, rest). It is not literally the printed "λ-form": Prop. 4.1 / C.1 call the coefficient of `z^c_{m-1}` constant in β,
but it is `β(f(q^d) - f(q^a)) + (1-β)(1 - q^a)`; and the printed c = 0 boundary `(1 - β + (1 - q^d)β) z^0_{m-1}` writes the FPR where its own case
analysis ("backdoored, Blue chooses Defer") needs the TPR `f(q^d)`. Lean uses `f(q^d)` (consistent with c > 0). Say "bridge to the App. C.1 case analysis,
with the printed c = 0 boundary corrected (FPR -> TPR)".

m7. c = 0 semantics. `gac`'s docstring quotes "if the protocol attempts to audit when no audit coins are left, the code is run instead", and
at c = 0 with `TA > 0` the Lean row counts the audit zone as catastrophe (`cat = 1 - TD + TA`). GAC's own c = 0 boundary conditions
(`p[m,0]` uses `f(q^d)`, `u^0` uses `1 - q^d`) are the reading "audit zone empty or deferred", which is exactly what the `qa m 0 = 0`, `f 0 = 0`
convention encodes. So the convention is not merely cosmetic: it is the only reading under which both GAC boundary formulas hold; `gac` with
`TA > 0` at c = 0 is a third reading matching neither. (W) holds for both (checked, `TA > 0`). Reword the docstring.

m8. (T5) is a legitimate GAC protocol instance only if it is a `gacQ` with a genuine ROC; it is: `f q = min 1 (3q/2)`, `qa = qd = 1/2` while `c > 0`,
`qa m 0 = 0`, `qd m 0 = 1/2` gives `TA = TD = 3/4`, `FA = 1/2`. Add `exG3 = gacQ 1 f qa qd` (extensional) as a conjunct of the Witness so "GAC-style"
is proved, not asserted. Caveat to put in the docstring: the instance audits half of all honest problems with one coin; the float
numerics at GAC scale (0.36 vs 0.67-0.71) carry the realism claim and are not Lean.

m9. The TMGAC Witness proves the exV3 certificate by hand (real-valued `if` chain) and never calls `checkRiskQ`; the "certificate workflow" is
not exercised on the GAC instance. Add rational tables `exCat exK exV : ... → ℚ` (Fin 2 states, Fin 2 actions, one model), `checkRiskQ 3 2 2 1 ... = true`
by `decide +kernel` (or `checkRiskN`), and `gameOfQ ... 0 = exG3` up to the Bool/Fin 2 relabelling.

m10. (Obs) docstring "lawful" -> "valid"; `(α σ)` in the (Abs) docstring is `α x`; FxGap docstring should say index 1 is the first round.

m11. (M) is bare convexity and says nothing about `σ` arbitrary with `σ h s = π`; add the one-line lemma `IsPolicy σ → (∀ h s, σ h s = π) → σ = constRed (π true)`
if the docstring's "the class of Reds whose action law, given the seed, ignores the history" is to be the formal statement.

m12. (Lip): constant N is tight (checked), but for N = 100 the grid spacing needed is ~1e-4 for a 1e-2 tolerance; say so. Not an error.

---------------------------------------------------------------------------------------------------------------------------

## 3. Answers to the five CHECK items

1. Truth: see §1. No conjunct false. Edge cases: N = 0 (risk = 0 <= V 0 s, checker tests only `V 0`); n > N (not constrained, and `valOfQ`
   is 0 there, `gameOfQ` rows 0); empty `adm` or `Θ` (the selector premise is unsatisfiable, vacuous); m = 0, t = 0, k = 0 tables (vacuously true, m3);
   `Fin.castSucc`/`Fin.succ` indexing correct (0 discrepancies in 10 000 random tables, both soundness and completeness); `valOfQ` at n = N
   correct (`N < N + 1`); `pushK` with empty fibres = 0 (restricts equality only); `Covered` at n >= N irrelevant; `honestER` with nature
   fine; `Vrob` needs `Nonempty Θ` (true for `Fin t`, t > 0); Lip constant N valid and tight; W valid with `TA > 0` at c = 0; (Z) valid for
   `f(qd) < f(qa)` (identity, no ordering used).
2. (Abs). Right idea, wrong relation and incomplete interface. "EQUALS" is too strong: it is unusable with finite vertex tables (M3b);
   use hull-domination with `V >= 0` (the counterexample shows `V >= 0` is needed). Does it cover every policy once the concrete state holds the
   model's private information? Yes in the precise sense that `σc` is an arbitrary randomised function of the ENTIRE concrete history (all past
   concrete states and actions), strictly more information than any real model has, so every `liftObs` restriction is covered; private randomness and
   memory are covered if they are components of `x`. What it does NOT cover: anything that affects the future rows and is not a component of `x`
   (the concrete game is Markov in `x`); a Red that observes signals not in `x`; unreachable-state rows are still required. What a lab must
   establish: (i) a finite concrete model `(Sc, Ac, Gc, α)` in which Blue's controller and the monitor are folded in and which is Markov;
   (ii) for EVERY concrete state and EVERY concrete action the row is dominated by a convex combination of the certified vertex rows. (ii)
   is a worst-case-over-the-model's-output-space statement (e.g. every backdoor the model can write is caught with probability in the interval); a
   red-team sample bounds only the attacks found, so this is where capability re-enters. The capability-free instances are those where the row is
   controlled by Blue's own randomisation (content-independent random audits, random spot checks, a fixed defer fraction): there
   the interval holds for every attack, a point worth saying in the docstring. Also say that the statistical confidence of (ii) (e.g. 1-δ from finite
   samples) is outside the formal statement.
3. (Q) kernel-checkable: only with `decide +kernel` (M2). Plain `decide` fails on `@[irreducible]` `Rat.add/mul/inv`. Under `+kernel`, nothing else blocks
   it (structural `Fin.foldr`, GMP `Nat.gcd`); cost is linear in cells x lookup cost, so use formula-defined tables. Preferred: ℕ-scaled checker.
4. Usefulness bridge: NOT faithful (M1): GAC counts Run and audited-no-error solutions, not Defer. Safety bridge: faithful to the App. C.1
   case analysis with a perfect auditor, not to the printed λ-form or the printed c = 0 boundary (m6, m7). Also GAC's human-error parameters
   `p^FPR_H`, `p^FNR_H` are absent (scope; say so).
5. Overclaims: (Q) "kernel can evaluate it by decide"; (Vx) "interval or polytope ... certified by finitely many vertex checks";
   (Abs) "formal form of 'covers every policy the untrusted model could follow'" (true only with the worst-case hypothesis and, as written, only
   for equality-covered rows); (UZ); TMGAC Witness "is computed". Missing for a lab: (i) uncertainty never enters TMGAC (`gacQ` has no model
   index; no `adm` instance for `gac` and no Witness with an interval), so TMGAC delivers no usable certificate for a measured monitor;
   (ii) interval ROC from finite samples: Blue's thresholds are chosen on the same data (selection bias), so the intervals must be uniform over
   thresholds (DKW / ROC bands) with a union bound; TPR at `qa` and `qd` are jointly constrained by `TA <= TD`; rectangular `adm` is very conservative for
   a fixed unknown rate (FxGap: 3/4 vs 1/2 at two rounds, worse at 100), so the fixed-model route (Fx) needs a parameter-Lipschitz lemma
   (simulation lemma, `|risk_θ - risk_θ'| <= N · max row L¹ distance`) to pass from a grid of models to the whole confidence box; none exists;
   (iii) discretised scores: realised FPR/TPR at an integer threshold differ from the nominal `qa`; randomised tie-breaking makes `f` piecewise linear;
   model the realised pair as vertex rows rather than as `qa`; (iv) Blue optimisation is out of scope but compatible: DP outside, `checkRiskQ`
   verifies; say "Blue's controller is not adaptive beyond the state"; (v) auditor error rates; (vi) uncertain deployment length N.

---------------------------------------------------------------------------------------------------------------------------

## 4. Fixes in priority order

1. M1: correct `uGAC` and the (UZ) reward to `1 - qd + qa`, add `qa m 0 = 0` as hypothesis, fix the docstring and `numerics/tmgac_check.py`.
2. M3: `CoveredHull` + `V >= 0` in (Abs); `hullGame` + `Simplex` wiring for (Vx); have `checkRiskQ` test `0 <= V n s` for all `n <= N`.
3. M2: `decide +kernel` (or `checkRiskN` with plain `decide`); guards `0 < t`, `0 < k` inside the Boolean; formula-defined tables.
4. m2: (Q) concludes `Lawful`; m1: `K >= 0` for `n < N` / `a₀`.
5. m6, m7, m8, m9, m5: TMGAC docstring and Witness (c = 0 semantics; printed-form caveats; `exG3 = gacQ ...`; run `exV3` through the checker; give the 63/64 value).
6. Remaining MINORs (m3, m4, m10-m12).

## 5. Conjunct lists I would freeze

TMCERT v2 `Claim`:
(S) with `K >= 0` for `n < N`; (S'); (Fx) with the certificate hypothesis for `th` only; (FxGap); (Obs); (T) as is; (TR) as is;
(U) with `K >= 0` at `a₀` only, `n < N`; (Q) `checkRiskN`/`checkRiskQ` => `RiskCertUpTo` AND `0 <= V` for `n <= N`, `checkLawful*` => `∀ th, Lawful (gameOfQ ...)`,
guards `0 < t`, `0 < k`; (Vx) wired (`hullGame`, `Simplex`; the bare convexity statement kept as a lemma, not as a conjunct); (Abs) with `CoveredHull`
and `V >= 0`. Witness: checker accepts by `decide +kernel` (or plain `decide` for `checkRiskN`); `Lawful` of the induced games; 3/4 bound and
attainment; a `CoveredHull` instance with a genuinely interior concrete row (e.g. concrete cat 1/4 dominated by `1/2·row0 + 1/2·row1`).

TMGAC v1 `Claim`:
(L); (Z) with `f 0 = 0` and `qa m 0 = 0`, docstring corrected (printed boundary typo, perfect auditor); (UZ) with corrected `uGAC` and `qa m 0 = 0`;
(M); (Lip) (constant N, tight); (W); (T5) as is; Witness: `exG3 = gacQ 1 f qa qd` for `f q = min 1 (3q/2)`, `qa = qd = 1/2` (c > 0), `qa m 0 = 0`,
`qd m 0 = 1/2`; `exV3` through the checker; the `63/64` instance with its value; a TMGAC example with an interval `adm` (vertices on `TA`, `TD`) to exercise `adm`
and `hullGame` at least once. Do NOT add a "no usable certificate for a measured monitor" claim until the parameter-Lipschitz lemma exists.
