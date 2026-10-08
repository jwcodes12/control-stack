/-
Positive counterpart to `ComposeBlindSpot`: which coverage hypothesis lets a population-average trusted-monitor
certificate bound a content-adaptive Red.

Coverage (K, ε): Red's attack-content law a is dominated by K times the calibration population q up to an ε-mass of
uncovered content: a x ≤ K·q x + e x with e ≥ 0, Σ e ≤ ε.

- `coverage_transfer`: then Red's trusted miss Σ a·τ ≤ K·τ̄ + ε, where τ̄ = Σ q·τ is the calibrated average miss;
- `tight_K` and `tight_eps`: both terms are attained, so neither K nor ε can be dropped or improved for general τ;
  `ComposeBlindSpot` is the case ε = 1 (all of Red's mass on content the population never shows);
- `composedCov_end`: plugged into `ComposeAvg.composedPop_end`, the composed protocol risk against a history-dependent
  Red with covered content is ≤ (1 − r) + r·(K·τ̄ + ε)·L·(n_s+1)/(n_h+1).

The hypothesis is about Red's reachable attack content, not about data: sampling q certifies τ̄, never K or ε.
-/
import ControlStack.ComposeAvg

open OracleComp

namespace ControlStack.ComposeCoverage
open ControlStack.Refine ControlStack.Compose ControlStack.ComposeAvg

/-! ### Core transfer inequality (real-valued) -/

theorem coverage_transfer {X : Type} [Fintype X] (a q τ e : X → ℝ) (K ε : ℝ)
    (hτ0 : ∀ x, 0 ≤ τ x) (hτ1 : ∀ x, τ x ≤ 1) (he0 : ∀ x, 0 ≤ e x) (heps : ∑ x, e x ≤ ε)
    (hcov : ∀ x, a x ≤ K * q x + e x) (ha0 : ∀ x, 0 ≤ a x) :
    ∑ x, a x * τ x ≤ K * ∑ x, q x * τ x + ε := by
  calc ∑ x, a x * τ x ≤ ∑ x, (K * q x + e x) * τ x :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hcov x) (hτ0 x)
    _ = K * ∑ x, q x * τ x + ∑ x, e x * τ x := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ K * ∑ x, q x * τ x + ∑ x, e x := by
        gcongr with x
        exact mul_le_of_le_one_right (he0 x) (hτ1 x)
    _ ≤ K * ∑ x, q x * τ x + ε := by linarith

/-- **K is attained.** For K ≥ 1 and τ̄ = t with K·t ≤ 1: a two-point instance with a ≤ K·q (ε = 0) and Red miss K·t. -/
theorem tight_K (K t : ℝ) (hK : 1 ≤ K) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hKt : K * t ≤ 1) :
    let q : Bool → ℝ := fun x => if x then t else 1 - t
    let a : Bool → ℝ := fun x => if x then K * t else 1 - K * t
    let τ : Bool → ℝ := fun x => if x then 1 else 0
    (∀ x, a x ≤ K * q x) ∧ (∀ x, 0 ≤ a x) ∧ (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1 ∧ ∑ x, a x = 1 ∧
      ∑ x, q x * τ x = t ∧ ∑ x, a x * τ x = K * t := by
  intro q a τ
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, ?_, ?_, ?_, ?_⟩
  · cases x <;> simp [q, a] <;> nlinarith
  · cases x <;> simp [a] <;> nlinarith
  · cases x <;> simp [q] <;> linarith
  · simp [q]
  · simp [a]
  · simp [q, τ]
  · simp [a, τ]

/-- **ε is attained.** Calibration never shows the blind spot (τ̄ = 0); Red puts mass ε on it: miss ε with K = 1. -/
theorem tight_eps (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    let q : Bool → ℝ := fun x => if x then 0 else 1
    let a : Bool → ℝ := fun x => if x then ε else 1 - ε
    let e : Bool → ℝ := fun x => if x then ε else 0
    let τ : Bool → ℝ := fun x => if x then 1 else 0
    (∀ x, a x ≤ 1 * q x + e x) ∧ ∑ x, e x = ε ∧ ∑ x, q x * τ x = 0 ∧ ∑ x, a x * τ x = ε := by
  intro q a e τ
  refine ⟨fun x => ?_, ?_, ?_, ?_⟩
  · cases x <;> simp [q, a, e] <;> linarith
  · simp [e]
  · simp [q, τ]
  · simp [a, τ]

/-! ### Operational bridge -/

/-- Red's trusted-PASS probability on covered content is ≤ K·τ̄_cal + ε. -/
theorem coverage_miss {X : Type} [Fintype X] (Apop Cal : ProbComp X) (T : X → ProbComp Bool)
    (K ε : ℝ) (e : X → ℝ) (he0 : ∀ x, 0 ≤ e x) (heps : ∑ x, e x ≤ ε)
    (hcov : ∀ x, (Pr[= x | Apop]).toReal ≤ K * (Pr[= x | Cal]).toReal + e x) :
    (Pr[= true | Apop >>= T]).toReal ≤ K * (Pr[= true | Cal >>= T]).toReal + ε := by
  have expand : ∀ P : ProbComp X,
      (Pr[= true | P >>= T]).toReal = ∑ x, (Pr[= x | P]).toReal * (Pr[= true | T x]).toReal := by
    intro P
    rw [probOutput_bind_eq_tsum, tsum_fintype, ENNReal.toReal_sum (fun x _ => by finiteness)]
    simp only [ENNReal.toReal_mul]
  rw [expand Apop, expand Cal]
  exact coverage_transfer _ _ _ e K ε (fun _ => ENNReal.toReal_nonneg)
    (fun x => ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using probOutput_le_one))
    he0 heps hcov (fun _ => ENNReal.toReal_nonneg)

/-- **Composition under coverage.** History-dependent Red, attack content from a law covered (K, ε) by the calibration
population: risk ≤ (1 − r) + r·((K·τ̄_cal + ε)·L)·(n_s+1)/(n_h+1). -/
theorem composedCov_end {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z)
    (T : X → ProbComp Bool) (Apop Cal : ProbComp X) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist (Option X) (Z × Bool) → ProbComp (Option X))
    (A : Hist (Option X) (Z × Bool) → Option X → Z × Bool → ProbComp Bool) (nh ns b N : ℕ) (r L K ε : ℝ)
    (e : X → ℝ) (he0 : ∀ x, 0 ≤ e x) (heps : ∑ x, e x ≤ ε)
    (hcov : ∀ x, (Pr[= x | Apop]).toReal ≤ K * (Pr[= x | Cal]).toReal + e x)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L)
    (hrec : ∀ h v, r ≤ (Pr[= true | A h none v]).toReal)
    (hsupp : ∀ x, Pr[= x | Apop] ≠ 0 → Bad x)
    (hdom : ∀ x, Bad x → ∀ z, (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) :
    (Pr[= true | composedGameJ popBad ρ H M (popJ M T Apop) D π A nh ns b N]).toReal ≤
      (1 - r) + r * (((K * (Pr[= true | Cal >>= T]).toReal + ε) * L) * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) := by
  have h := composedPop_end Bad ρ H M T Apop D π A nh ns b N r L hr0 hr1 hL hrec hsupp hdom
  have hm := coverage_miss Apop Cal T K ε e he0 heps hcov
  refine h.trans ?_
  have hc : 0 ≤ ((ns : ℝ) + 1) / ((nh : ℝ) + 1) := by positivity
  gcongr

#print axioms coverage_transfer
#print axioms tight_K
#print axioms tight_eps
#print axioms coverage_miss
#print axioms composedCov_end

end ControlStack.ComposeCoverage
