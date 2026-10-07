/-
Composition of trusted and untrusted monitoring as one VCVio game.

The untrusted monitor is honeypot-tested exactly as in `Refinement.protocolGame`. In deployment, each
submission `x` is also shown to a trusted monitor `T x`, which has its own fresh coins: it does not see the
colluders' seed and is not chosen by Red. A submission passes only if both monitors pass it; a flag from
either one sends it to audit (or halts once the budget is spent). The generator and the audit kernel see
the full history, including the trusted verdicts.

Because the trusted coins are fresh, the two monitors' misses on a given submission are conditionally
independent given that submission. This is a property of the game, not an extra hypothesis, and it is what
makes the bound multiply: (1 − r) + r·τ·L·(n_s+1)/(n_h+1), where τ bounds the trusted monitor's miss
probability on every bad submission. The design note's shared-latent-bit counterexample is excluded
because no randomness is shared between `T` and the colluders.
-/
import ControlStack.RefinementProof

open OracleComp

namespace ControlStack.Compose
open ControlStack.Refine
open ControlStack.Bridge (honeypotPasses binCDF)

/-- Deployment view: the mediated view for the untrusted monitor, and the trusted verdict
(`true` = trusted PASS), drawn with independent fresh coins. -/
def jointView {X Z : Type} (M : X → ProbComp Z) (T : X → ProbComp Bool) (x : X) :
    ProbComp (Z × Bool) := do
  let z ← M x
  let t ← T x
  pure (z, t)

/-- Joint PASS: the trusted monitor must pass, and then the untrusted monitor decides. -/
def jointPass {Z : Type} (D : Z → ProbComp Bool) (v : Z × Bool) : ProbComp Bool :=
  if v.2 then D v.1 else pure false

/-- The composed protocol; `true` = the colluding pair survived the honeypot test and then caused an
uncaught catastrophe. -/
def composedGame {X Z Ω : Type} (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω)
    (H : ProbComp X) (M : X → ProbComp Z) (T : X → ProbComp Bool) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X (Z × Bool) → ProbComp X)
    (A : Hist X (Z × Bool) → X → Z × Bool → ProbComp Bool) (nh ns b N : ℕ) : ProbComp Bool := do
  let ω ← ρ
  let k ← honeypotPasses H M (D ω) nh
  if k ≤ ns then deploy Bad (π ω) (jointView M T) (jointPass (D ω)) A b N 0 [] else pure false

theorem composed_factorization {X Z Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (T : X → ProbComp Bool)
    (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X (Z × Bool) → ProbComp X)
    (A : Hist X (Z × Bool) → X → Z × Bool → ProbComp Bool) (nh ns b N : ℕ) :
    (Pr[= true | composedGame Bad ρ H M T D π A nh ns b N]).toReal =
      ∑ ω, (Pr[= ω | ρ]).toReal * binCDF nh ns (Pr[= true | H >>= M >>= D ω]).toReal *
        (Pr[= true | deploy Bad (π ω) (jointView M T) (jointPass (D ω)) A b N 0 []]).toReal := by
  have key : ∀ ω, Pr[= true | honeypotPasses H M (D ω) nh >>= fun k =>
      if k ≤ ns then deploy Bad (π ω) (jointView M T) (jointPass (D ω)) A b N 0 [] else pure false] =
      Pr[fun k => k ≤ ns | honeypotPasses H M (D ω) nh] *
        Pr[= true | deploy Bad (π ω) (jointView M T) (jointPass (D ω)) A b N 0 []] := by
    intro ω
    rw [probOutput_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun k => ?_
    by_cases hk : k ≤ ns <;> simp [hk]
  unfold composedGame
  rw [probOutput_bind_eq_tsum, tsum_fintype]
  simp only [key]
  rw [ENNReal.toReal_sum (fun ω _ => by finiteness)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, Bridge.bridge, mul_assoc]

/-- Conditional independence by construction: the joint pass probability of a submission factorises
into the trusted miss probability times the untrusted pass probability. -/
theorem joint_pass_prob {X Z : Type} [Fintype Z] (M : X → ProbComp Z) (T : X → ProbComp Bool)
    (D : Z → ProbComp Bool) (x : X) :
    ∑ v, (Pr[= v | jointView M T x]).toReal * (Pr[= true | jointPass D v]).toReal =
      (Pr[= true | T x]).toReal * ∑ z, (Pr[= z | M x]).toReal * (Pr[= true | D z]).toReal := by
  have e : ∑ v, (Pr[= v | jointView M T x]).toReal * (Pr[= true | jointPass D v]).toReal =
      (Pr[= true | jointView M T x >>= jointPass D]).toReal := by
    rw [probOutput_bind_eq_tsum, tsum_fintype, ENNReal.toReal_sum (fun v _ => by finiteness)]
    simp only [ENNReal.toReal_mul]
  rw [e]
  have e2 : (jointView M T x >>= jointPass D) =
      (M x >>= fun z => T x >>= fun t => if t then D z else pure false) := by
    simp [jointView, jointPass]
  rw [e2, probOutput_bind_eq_tsum, tsum_fintype, ENNReal.toReal_sum (fun z _ => by finiteness),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [probOutput_bind_eq_tsum, tsum_fintype, Fintype.sum_bool]
  simp only [if_true, ENNReal.toReal_mul]
  simp [ENNReal.toReal_mul]
  ring

/-- **Composed end-to-end bound.** For every colluding pair (seed law, untrusted monitor, adaptive
generator) and every audit kernel with recall ≥ r: if the trusted monitor misses each bad submission with
probability at most τ, and bad views are L-dominated by mediated honeypots, then
P(survive the honeypot test, then uncaught catastrophe) ≤ (1 − r) + r·τ·L·(n_s+1)/(n_h+1). -/
theorem composedEndToEnd {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z)
    (T : X → ProbComp Bool) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X (Z × Bool) → ProbComp X)
    (A : Hist X (Z × Bool) → X → Z × Bool → ProbComp Bool) (nh ns b N : ℕ) (r L τ : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hτ0 : 0 ≤ τ)
    (hrec : ∀ h x v, Bad x → r ≤ (Pr[= true | A h x v]).toReal)
    (htm : ∀ x, Bad x → (Pr[= true | T x]).toReal ≤ τ)
    (hdom : ∀ x, Bad x → ∀ z, (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) :
    (Pr[= true | composedGame Bad ρ H M T D π A nh ns b N]).toReal ≤
      (1 - r) + r * ((τ * L) * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) := by
  rw [composed_factorization]
  set C : ℝ := (1 - r) + r * ((τ * L) * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) with hC
  have hρ : ∑ ω, (Pr[= ω | ρ]).toReal = 1 := sum_toReal_probOutput ρ
  calc ∑ ω, (Pr[= ω | ρ]).toReal * binCDF nh ns (Pr[= true | H >>= M >>= D ω]).toReal *
        (Pr[= true | deploy Bad (π ω) (jointView M T) (jointPass (D ω)) A b N 0 []]).toReal
      ≤ ∑ ω, (Pr[= ω | ρ]).toReal * C := by
        apply Finset.sum_le_sum
        intro ω _
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        set hω := (Pr[= true | H >>= M >>= D ω]).toReal with hhω
        have hS := Bridge.bridge X Z H M (D ω) nh ns
        have hS' := Bridge.bridge X Z H M (D ω) (nh + 1) (ns + 1)
        rw [← hhω] at hS hS'
        have hS0 : 0 ≤ binCDF nh ns hω := hS ▸ ENNReal.toReal_nonneg
        have hS1 : binCDF nh ns hω ≤ 1 := hS ▸ toReal_probEvent_le_one _ _
        have hS1' : binCDF (nh + 1) (ns + 1) hω ≤ 1 := hS' ▸ toReal_probEvent_le_one _ _
        have hh0 : 0 ≤ hω := ENNReal.toReal_nonneg
        have hh1 : hω ≤ 1 := toReal_probOutput_le_one _ _
        have hsum : hω = ∑ z, (Pr[= z | H >>= M]).toReal * (Pr[= true | D ω z]).toReal := by
          rw [hhω, probOutput_bind_eq_tsum, tsum_fintype,
            ENNReal.toReal_sum (fun z _ => by finiteness)]
          simp only [ENNReal.toReal_mul]
        have hτL : 0 ≤ τ * L := mul_nonneg hτ0 hL
        set Aω := min 1 ((τ * L) * hω) with hAω
        have hA0 : 0 ≤ Aω := le_min zero_le_one (mul_nonneg hτL hh0)
        have hA1 : Aω ≤ 1 := min_le_left _ _
        have hbad : ∀ x, Bad x → ∑ v, (Pr[= v | jointView M T x]).toReal *
            (Pr[= true | jointPass (D ω) v]).toReal ≤ Aω := by
          intro x hx
          apply le_min
          · apply wsum_le _ _ _ (fun _ => ENNReal.toReal_nonneg) (sum_toReal_probOutput _)
            intro v; exact toReal_probOutput_le_one _ _
          · rw [joint_pass_prob]
            have hU : ∑ z, (Pr[= z | M x]).toReal * (Pr[= true | D ω z]).toReal ≤ L * hω := by
              rw [hsum, Finset.mul_sum]
              apply Finset.sum_le_sum
              intro z _
              calc (Pr[= z | M x]).toReal * (Pr[= true | D ω z]).toReal
                  ≤ (L * (Pr[= z | H >>= M]).toReal) * (Pr[= true | D ω z]).toReal :=
                    mul_le_mul_of_nonneg_right (hdom x hx z) ENNReal.toReal_nonneg
                _ = L * ((Pr[= z | H >>= M]).toReal * (Pr[= true | D ω z]).toReal) := by ring
            have hU0 : 0 ≤ ∑ z, (Pr[= z | M x]).toReal * (Pr[= true | D ω z]).toReal :=
              Finset.sum_nonneg fun z _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
            calc (Pr[= true | T x]).toReal * ∑ z, (Pr[= z | M x]).toReal * (Pr[= true | D ω z]).toReal
                ≤ τ * (L * hω) := mul_le_mul (htm x hx) hU hU0 hτ0
              _ = (τ * L) * hω := by ring
        have hdep := deploy_le X (Z × Bool) Bad (π ω) (jointView M T) (jointPass (D ω)) A r b hrec N 0 []
        have hcat := t3a Bad (fun x v => (Pr[= v | jointView M T x]).toReal)
          (fun v => (Pr[= true | jointPass (D ω) v]).toReal)
          (fun h x => (Pr[= x | π ω h]).toReal) r Aω b (fun _ _ => ENNReal.toReal_nonneg)
          (fun x => sum_toReal_probOutput _) (fun _ => ENNReal.toReal_nonneg)
          (fun _ => toReal_probOutput_le_one _ _) (fun _ _ => ENNReal.toReal_nonneg)
          (fun h => sum_toReal_probOutput _) hr0 hr1 hA0 hA1 hbad N 0 []
        have hAB : Aω ≤ 1 - r + r * Aω := by nlinarith
        have hP : (Pr[= true | deploy Bad (π ω) (jointView M T) (jointPass (D ω)) A b N 0 []]).toReal
            ≤ 1 - r + r * Aω := by
          refine le_trans hdep (le_trans hcat ?_)
          split_ifs <;> linarith
        calc binCDF nh ns hω *
              (Pr[= true | deploy Bad (π ω) (jointView M T) (jointPass (D ω)) A b N 0 []]).toReal
            ≤ binCDF nh ns hω * (1 - r + r * Aω) := mul_le_mul_of_nonneg_left hP hS0
          _ ≤ C := final_dom _ _ _ _ _ _ hS0 hS1 hr0 hr1 hτL (min_le_right _ _)
                (first_moment' nh ns hω hh0 hh1 hS1')
    _ = C := by rw [← Finset.sum_mul, hρ, one_mul]

/-- Tightness and non-vacuity. With no honeypots (n_h = n_s = 0), an always-PASS untrusted monitor,
an identity mediator with honeypots equal to the bad view (L = 1), a trusted monitor that misses with
probability τ = 1/2, and an audit with recall r = 1/2, the generator that submits the bad action at once
reaches catastrophe with probability exactly (1 − r) + r·τ = 3/4, which equals the bound. -/
theorem composed_tight :
    (Pr[= true | composedGame (fun x : Bool => x = true) (pure ()) (pure true) (fun x => pure x)
        (fun _ => (fun k : Fin 2 => decide (k = 0)) <$> $[0..1]) (fun _ _ => pure true)
        (fun _ _ => pure true) (fun _ _ _ => (fun k : Fin 2 => decide (k = 0)) <$> $[0..1])
        0 0 1 1]).toReal = 3 / 4 ∧
    (3 / 4 : ℝ) = (1 - 1 / 2) + 1 / 2 * ((1 / 2 * 1) * (((0 : ℝ) + 1) / ((0 : ℝ) + 1))) := by
  have hq : Pr[= true | ((fun k : Fin 2 => decide (k = 0)) <$> $[0..1] : ProbComp Bool)] = 2⁻¹ := by
    rw [probOutput_map_eq_sum_fintype_ite]
    simp
    norm_num
  have hq' : Pr[= false | ((fun k : Fin 2 => decide (k = 0)) <$> $[0..1] : ProbComp Bool)] = 2⁻¹ := by
    have h := probOutput_true_add_false_one ((fun k : Fin 2 => decide (k = 0)) <$> $[0..1])
    rw [hq] at h
    rw [← ENNReal.add_right_inj (a := 2⁻¹) (by simp), ENNReal.inv_two_add_inv_two, h]
  refine ⟨?_, by norm_num⟩
  simp [composedGame, honeypotPasses, deploy, jointView, jointPass]
  rw [probOutput_bind_eq_tsum, tsum_fintype, Fin.sum_univ_two]
  have hm : ((fun a : Fin 2 => !decide (a = 0)) <$> $[0..1] : ProbComp Bool) =
      (fun c => !c) <$> ((fun k : Fin 2 => decide (k = 0)) <$> $[0..1]) := by
    rw [Functor.map_map]
  simp
  rw [hm, probOutput_not_true, hq']
  have h2 : (1 + 1 : ENNReal) = 2 := by norm_num
  rw [h2, ENNReal.toReal_add (by simp) (by finiteness), ENNReal.toReal_mul]
  simp
  norm_num

#print axioms composedEndToEnd
#print axioms composed_tight

end ControlStack.Compose
