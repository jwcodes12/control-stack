/-
Composition with a population-average trusted miss rate.

`ComposeGame.composedEndToEnd` needs τ ≥ P(trusted PASS | x) for EVERY bad submission x. Empirical ROC data certifies
only an AVERAGE over an evaluated attack population. This file proves the matching bound for a model in which Red
chooses adaptively WHEN to attack (any history-dependent generator) but attack CONTENT is drawn from a fixed
population law `Apop` (the evaluated attack distribution), as in constant-rate GAC/TMCERT attack models:

  P(survive the honeypot test, then uncaught catastrophe) ≤ (1 − r) + r·τ̄·L·(n_s+1)/(n_h+1),
  τ̄ = P(trusted PASS on x ~ Apop) = 1 − TPR of the trusted monitor on the population,

so a certified lower bound on the trusted monitor's TPR plugs in directly. The general engine is `composedJ_end`: any
joint kernel for (untrusted view, trusted verdict) whose bad rows have joint pass ≤ K·h_ω.
-/
import ControlStack.ComposeGame

open OracleComp

namespace ControlStack.ComposeAvg
open ControlStack.Refine ControlStack.Compose
open ControlStack.Bridge (honeypotPasses binCDF)

/-- Composed protocol with a general deployment kernel `J` for (untrusted view, trusted verdict); honeypots live in
their own space `Y` and are mediated by `M`. -/
def composedGameJ {X Y Z Ω : Type} (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω)
    (H : ProbComp Y) (M : Y → ProbComp Z) (J : X → ProbComp (Z × Bool)) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X (Z × Bool) → ProbComp X)
    (A : Hist X (Z × Bool) → X → Z × Bool → ProbComp Bool) (nh ns b N : ℕ) : ProbComp Bool := do
  let ω ← ρ
  let k ← honeypotPasses H M (D ω) nh
  if k ≤ ns then deploy Bad (π ω) J (jointPass (D ω)) A b N 0 [] else pure false

theorem composedJ_factorization {X Y Z Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp Y) (M : Y → ProbComp Z) (J : X → ProbComp (Z × Bool))
    (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X (Z × Bool) → ProbComp X)
    (A : Hist X (Z × Bool) → X → Z × Bool → ProbComp Bool) (nh ns b N : ℕ) :
    (Pr[= true | composedGameJ Bad ρ H M J D π A nh ns b N]).toReal =
      ∑ ω, (Pr[= ω | ρ]).toReal * binCDF nh ns (Pr[= true | H >>= M >>= D ω]).toReal *
        (Pr[= true | deploy Bad (π ω) J (jointPass (D ω)) A b N 0 []]).toReal := by
  have key : ∀ ω, Pr[= true | honeypotPasses H M (D ω) nh >>= fun k =>
      if k ≤ ns then deploy Bad (π ω) J (jointPass (D ω)) A b N 0 [] else pure false] =
      Pr[fun k => k ≤ ns | honeypotPasses H M (D ω) nh] *
        Pr[= true | deploy Bad (π ω) J (jointPass (D ω)) A b N 0 []] := by
    intro ω
    rw [probOutput_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun k => ?_
    by_cases hk : k ≤ ns <;> simp [hk]
  unfold composedGameJ
  rw [probOutput_bind_eq_tsum, tsum_fintype]
  simp only [key]
  rw [ENNReal.toReal_sum (fun ω _ => by finiteness)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, Bridge.bridge, mul_assoc]

/-- General engine: if every bad row's joint pass probability is at most K·h_ω, the composed risk is at most
(1 − r) + r·K·(n_s+1)/(n_h+1). -/
theorem composedJ_end {X Y Z Ω : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp Y) (M : Y → ProbComp Z)
    (J : X → ProbComp (Z × Bool)) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X (Z × Bool) → ProbComp X)
    (A : Hist X (Z × Bool) → X → Z × Bool → ProbComp Bool) (nh ns b N : ℕ) (r K : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hK : 0 ≤ K)
    (hrec : ∀ h x v, Bad x → r ≤ (Pr[= true | A h x v]).toReal)
    (hJ : ∀ ω x, Bad x → ∑ v, (Pr[= v | J x]).toReal * (Pr[= true | jointPass (D ω) v]).toReal ≤
      K * (Pr[= true | H >>= M >>= D ω]).toReal) :
    (Pr[= true | composedGameJ Bad ρ H M J D π A nh ns b N]).toReal ≤
      (1 - r) + r * (K * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) := by
  rw [composedJ_factorization]
  set C : ℝ := (1 - r) + r * (K * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) with hC
  have hρ : ∑ ω, (Pr[= ω | ρ]).toReal = 1 := sum_toReal_probOutput ρ
  calc ∑ ω, (Pr[= ω | ρ]).toReal * binCDF nh ns (Pr[= true | H >>= M >>= D ω]).toReal *
        (Pr[= true | deploy Bad (π ω) J (jointPass (D ω)) A b N 0 []]).toReal
      ≤ ∑ ω, (Pr[= ω | ρ]).toReal * C := by
        apply Finset.sum_le_sum
        intro ω _
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        set hω := (Pr[= true | H >>= M >>= D ω]).toReal with hhω
        have hS := Bridge.bridge Y Z H M (D ω) nh ns
        have hS' := Bridge.bridge Y Z H M (D ω) (nh + 1) (ns + 1)
        rw [← hhω] at hS hS'
        have hS0 : 0 ≤ binCDF nh ns hω := hS ▸ ENNReal.toReal_nonneg
        have hS1 : binCDF nh ns hω ≤ 1 := hS ▸ toReal_probEvent_le_one _ _
        have hS1' : binCDF (nh + 1) (ns + 1) hω ≤ 1 := hS' ▸ toReal_probEvent_le_one _ _
        have hh0 : 0 ≤ hω := ENNReal.toReal_nonneg
        have hh1 : hω ≤ 1 := toReal_probOutput_le_one _ _
        set Aω := min 1 (K * hω) with hAω
        have hA0 : 0 ≤ Aω := le_min zero_le_one (mul_nonneg hK hh0)
        have hA1 : Aω ≤ 1 := min_le_left _ _
        have hbad : ∀ x, Bad x → ∑ v, (Pr[= v | J x]).toReal *
            (Pr[= true | jointPass (D ω) v]).toReal ≤ Aω := by
          intro x hx
          apply le_min
          · apply wsum_le _ _ _ (fun _ => ENNReal.toReal_nonneg) (sum_toReal_probOutput _)
            intro v; exact toReal_probOutput_le_one _ _
          · exact hJ ω x hx
        have hdep := deploy_le X (Z × Bool) Bad (π ω) J (jointPass (D ω)) A r b hrec N 0 []
        have hcat := t3a Bad (fun x v => (Pr[= v | J x]).toReal)
          (fun v => (Pr[= true | jointPass (D ω) v]).toReal)
          (fun h x => (Pr[= x | π ω h]).toReal) r Aω b (fun _ _ => ENNReal.toReal_nonneg)
          (fun x => sum_toReal_probOutput _) (fun _ => ENNReal.toReal_nonneg)
          (fun _ => toReal_probOutput_le_one _ _) (fun _ _ => ENNReal.toReal_nonneg)
          (fun h => sum_toReal_probOutput _) hr0 hr1 hA0 hA1 hbad N 0 []
        have hP : (Pr[= true | deploy Bad (π ω) J (jointPass (D ω)) A b N 0 []]).toReal
            ≤ 1 - r + r * Aω := by
          refine le_trans hdep (le_trans hcat ?_)
          split_ifs <;> nlinarith
        calc binCDF nh ns hω * (Pr[= true | deploy Bad (π ω) J (jointPass (D ω)) A b N 0 []]).toReal
            ≤ binCDF nh ns hω * (1 - r + r * Aω) := mul_le_mul_of_nonneg_left hP hS0
          _ ≤ C := final_dom _ _ _ _ _ _ hS0 hS1 hr0 hr1 hK (min_le_right _ _)
                (first_moment' nh ns hω hh0 hh1 hS1')
    _ = C := by rw [← Finset.sum_mul, hρ, one_mul]

/-- Population attack model: `none` = "attack, content drawn from `Apop`"; `some x` = Red's own (benign) submission. -/
def popJ {X Z : Type} (M : X → ProbComp Z) (T : X → ProbComp Bool) (Apop : ProbComp X) :
    Option X → ProbComp (Z × Bool)
  | some x => jointView M T x
  | none => Apop >>= jointView M T

/-- In the population model the only bad action is drawing an attack from the population. -/
def popBad {X : Type} (o : Option X) : Prop := o = none

instance {X : Type} : DecidablePred (@popBad X) := fun o => by unfold popBad; infer_instance

/-- Untrusted pass on a bad submission is at most L·h_ω under view domination. -/
theorem untrusted_pass_le {X Z : Type} [Fintype Z] (H : ProbComp X) (M : X → ProbComp Z)
    (D : Z → ProbComp Bool) (L : ℝ) (x : X)
    (hdom : ∀ z, (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) :
    ∑ z, (Pr[= z | M x]).toReal * (Pr[= true | D z]).toReal ≤ L * (Pr[= true | H >>= M >>= D]).toReal := by
  have hsum : (Pr[= true | H >>= M >>= D]).toReal =
      ∑ z, (Pr[= z | H >>= M]).toReal * (Pr[= true | D z]).toReal := by
    rw [probOutput_bind_eq_tsum, tsum_fintype, ENNReal.toReal_sum (fun z _ => by finiteness)]
    simp only [ENNReal.toReal_mul]
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  calc (Pr[= z | M x]).toReal * (Pr[= true | D z]).toReal
      ≤ (L * (Pr[= z | H >>= M]).toReal) * (Pr[= true | D z]).toReal :=
        mul_le_mul_of_nonneg_right (hdom z) ENNReal.toReal_nonneg
    _ = L * ((Pr[= z | H >>= M]).toReal * (Pr[= true | D z]).toReal) := by ring

/-- **Composition with the population-average trusted miss rate.** Red's generator is arbitrary and history-dependent
(it chooses when to attack); attack content is drawn from `Apop`, supported on bad submissions whose views are
L-dominated by mediated honeypots. With τ̄ = P(trusted PASS on x ~ Apop):
risk ≤ (1 − r) + r·τ̄·L·(n_s+1)/(n_h+1). -/
theorem composedPop_end {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z)
    (T : X → ProbComp Bool) (Apop : ProbComp X) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist (Option X) (Z × Bool) → ProbComp (Option X))
    (A : Hist (Option X) (Z × Bool) → Option X → Z × Bool → ProbComp Bool) (nh ns b N : ℕ) (r L : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L)
    (hrec : ∀ h v, r ≤ (Pr[= true | A h none v]).toReal)
    (hsupp : ∀ x, Pr[= x | Apop] ≠ 0 → Bad x)
    (hdom : ∀ x, Bad x → ∀ z, (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) :
    (Pr[= true | composedGameJ popBad ρ H M (popJ M T Apop) D π A nh ns b N]).toReal ≤
      (1 - r) + r * (((Pr[= true | Apop >>= T]).toReal * L) * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) := by
  have hτ0 : 0 ≤ (Pr[= true | Apop >>= T]).toReal := ENNReal.toReal_nonneg
  refine composedJ_end popBad ρ H M (popJ M T Apop) D π A nh ns b N r _ hr0 hr1 (mul_nonneg hτ0 hL)
    (fun h x v hx => by rw [show x = none from hx]; exact hrec h v) ?_
  intro ω x hx
  rw [show x = none from hx]
  set hω := (Pr[= true | H >>= M >>= D ω]).toReal
  -- joint pass on a population draw = Σ_x Apop(x)·T(x)·U(x)
  have e1 : ∑ v, (Pr[= v | popJ M T Apop none]).toReal * (Pr[= true | jointPass (D ω) v]).toReal =
      (Pr[= true | (Apop >>= jointView M T) >>= jointPass (D ω)]).toReal := by
    rw [probOutput_bind_eq_tsum (mx := Apop >>= jointView M T), tsum_fintype,
      ENNReal.toReal_sum (fun v _ => by finiteness)]
    simp only [ENNReal.toReal_mul, popJ]
  have e2 : (Pr[= true | (Apop >>= jointView M T) >>= jointPass (D ω)]).toReal =
      ∑ x, (Pr[= x | Apop]).toReal *
        ((Pr[= true | T x]).toReal * ∑ z, (Pr[= z | M x]).toReal * (Pr[= true | D ω z]).toReal) := by
    rw [bind_assoc, probOutput_bind_eq_tsum, tsum_fintype, ENNReal.toReal_sum (fun x _ => by finiteness)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.toReal_mul, ← joint_pass_prob M T (D ω) x]
    congr 1
    rw [probOutput_bind_eq_tsum, tsum_fintype, ENNReal.toReal_sum (fun v _ => by finiteness)]
    simp only [ENNReal.toReal_mul]
  have e3 : (Pr[= true | Apop >>= T]).toReal = ∑ x, (Pr[= x | Apop]).toReal * (Pr[= true | T x]).toReal := by
    rw [probOutput_bind_eq_tsum, tsum_fintype, ENNReal.toReal_sum (fun x _ => by finiteness)]
    simp only [ENNReal.toReal_mul]
  rw [e1, e2, e3, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx0 : Pr[= x | Apop] = 0
  · simp [hx0]
  · have hU := untrusted_pass_le H M (D ω) L x (hdom x (hsupp x hx0))
    have hT0 : 0 ≤ (Pr[= true | T x]).toReal := ENNReal.toReal_nonneg
    have hA0 : 0 ≤ (Pr[= x | Apop]).toReal := ENNReal.toReal_nonneg
    calc (Pr[= x | Apop]).toReal * ((Pr[= true | T x]).toReal *
          ∑ z, (Pr[= z | M x]).toReal * (Pr[= true | D ω z]).toReal)
        ≤ (Pr[= x | Apop]).toReal * ((Pr[= true | T x]).toReal * (L * hω)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU hT0) hA0
      _ = (Pr[= x | Apop]).toReal * (Pr[= true | T x]).toReal * L * hω := by ring

#print axioms composedJ_end
#print axioms composedPop_end

end ControlStack.ComposeAvg
