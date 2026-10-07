/- VCVio game-level hockey-stick composition for soft-slack honeypot testing. -/
import ControlStack.SoftSlack

open OracleComp

namespace ControlStack.SoftHockey
open ControlStack.Refine ControlStack.SoftSlack

/-- The finite output law of an operational probability computation. -/
noncomputable def viewLaw {Z : Type} [Fintype Z] (c : ProbComp Z) : Z → ℝ :=
  fun z => (Pr[= z | c]).toReal

/-- Hockey-stick divergence between finite real-valued laws. -/
noncomputable def hs {Z : Type} [Fintype Z] (η : ℝ) (P Q : Z → ℝ) : ℝ :=
  ∑ z, max 0 (P z - Real.exp η * Q z)

def isRule {Z : Type} (φ : Z → ℝ) : Prop := ∀ z, 0 ≤ φ z ∧ φ z ≤ 1

theorem viewLaw_nonneg {Z : Type} [Fintype Z] (c : ProbComp Z) (z : Z) :
    0 ≤ viewLaw c z := ENNReal.toReal_nonneg

theorem viewLaw_sum {Z : Type} [Fintype Z] (c : ProbComp Z) :
    ∑ z, viewLaw c z = 1 := sum_toReal_probOutput c

theorem passRule_isRule {Z : Type} (D : Z → ProbComp Bool) :
    isRule (fun z => (Pr[= true | D z]).toReal) := by
  intro z
  exact ⟨ENNReal.toReal_nonneg, toReal_probOutput_le_one _ _⟩

theorem viewLaw_pass {Z : Type} [Fintype Z] (c : ProbComp Z) (D : Z → ProbComp Bool) :
    ∑ z, viewLaw c z * (Pr[= true | D z]).toReal =
      (Pr[= true | c >>= D]).toReal := by
  rw [probOutput_bind_eq_tsum, tsum_fintype,
    ENNReal.toReal_sum (fun z _ => by finiteness)]
  simp only [ENNReal.toReal_mul, viewLaw]

/-- Finite hockey-stick testing inequality, instantiated with an operational monitor rule. -/
theorem hockey_pass_bound {Z : Type} [Fintype Z] (η : ℝ) (P Q : Z → ℝ)
    (D : Z → ProbComp Bool) :
    (∑ z, P z * (Pr[= true | D z]).toReal) ≤
      Real.exp η * (∑ z, Q z * (Pr[= true | D z]).toReal) + hs η P Q := by
  unfold hs
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z _
  have hφ := passRule_isRule D z
  have hmax : (P z - Real.exp η * Q z) * (Pr[= true | D z]).toReal ≤
      max 0 (P z - Real.exp η * Q z) := by
    have hm : P z - Real.exp η * Q z ≤ max 0 (P z - Real.exp η * Q z) := le_max_right _ _
    have hz : 0 ≤ max 0 (P z - Real.exp η * Q z) := le_max_left _ _
    calc
      (P z - Real.exp η * Q z) * (Pr[= true | D z]).toReal ≤
          max 0 (P z - Real.exp η * Q z) * (Pr[= true | D z]).toReal :=
        mul_le_mul_of_nonneg_right hm hφ.1
      _ ≤ max 0 (P z - Real.exp η * Q z) := by nlinarith [hφ.2]
  have heq : P z * (Pr[= true | D z]).toReal =
      Real.exp η * (Q z * (Pr[= true | D z]).toReal) +
        (P z - Real.exp η * Q z) * (Pr[= true | D z]).toReal := by ring
  linarith

theorem operational_hockey_bound {Z : Type} [Fintype Z]
    (η δ : ℝ) (H : ProbComp Z) (X : ProbComp Z) (D : Z → ProbComp Bool)
    (hδ : hs η (viewLaw X) (viewLaw H) ≤ δ) :
    (Pr[= true | X >>= D]).toReal ≤
      Real.exp η * (Pr[= true | H >>= D]).toReal + δ := by
  have ht := hockey_pass_bound η (viewLaw X) (viewLaw H) D
  rw [viewLaw_pass X D, viewLaw_pass H D] at ht
  linarith

/-- Soft-slack protocol bound from a uniform hockey-stick envelope on bad submissions. -/
theorem softEndToEndHockey {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool)
    (nh ns b N : ℕ) (r η δ : ℝ) (hns : 1 ≤ ns)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hδ0 : 0 ≤ δ)
    (hrec : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal)
    (hhs : ∀ x, Bad x → hs η (viewLaw (M x)) (viewLaw (H >>= M)) ≤ δ) :
    (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal ≤
      (1 - r) + r * (δ + Real.exp η * ((ns : ℝ) / ((nh : ℝ) + 1))) := by
  rw [protocol_survival_formula Bad ρ H M D π A nh ns b N hns]
  set B : ℝ := (ns : ℝ) / ((nh : ℝ) + 1) with hB
  set C : ℝ := (1 - r) + r * (δ + Real.exp η * B) with hC
  have hρ : ∑ ω, (Pr[= ω | ρ]).toReal = 1 := sum_toReal_probOutput ρ
  calc ∑ ω, (Pr[= ω | ρ]).toReal *
        (1 - (Pr[= true | H >>= M >>= D ω]).toReal / (ns : ℝ)) ^ nh *
        (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
      ≤ ∑ ω, (Pr[= ω | ρ]).toReal * C := by
        apply Finset.sum_le_sum
        intro ω _
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        set hω := (Pr[= true | H >>= M >>= D ω]).toReal with hhω
        set Sω := (1 - hω / (ns : ℝ)) ^ nh with hSω
        have hbridge := bridge X Z H M (D ω) (ns - 1) nh
        have hns' : ns - 1 + 1 = ns := Nat.sub_add_cancel hns
        rw [hns'] at hbridge
        rw [← hhω] at hbridge
        have hSprob : (Pr[= true | survives H M (D ω) (ns - 1) nh]).toReal = Sω := by
          simpa [Sω, hω] using hbridge
        have hS0 : 0 ≤ Sω := hSprob ▸ ENNReal.toReal_nonneg
        have hS1 : Sω ≤ 1 := hSprob ▸ toReal_probOutput_le_one _ _
        have hh0 : 0 ≤ hω := ENNReal.toReal_nonneg
        have hh1 : hω ≤ 1 := toReal_probOutput_le_one _ _
        have hmoment := soft_survival_first_moment nh ns hω hns hh0 hh1
        set Aω := min 1 (Real.exp η * hω + δ) with hAω
        have hA0 : 0 ≤ Aω := le_min zero_le_one (by positivity)
        have hA1 : Aω ≤ 1 := min_le_left _ _
        have hbad : ∀ x, Bad x → ∑ z, (Pr[= z | M x]).toReal *
            (Pr[= true | D ω z]).toReal ≤ Aω := by
          intro x hx
          apply le_min
          · apply wsum_le _ _ _ (fun _ => ENNReal.toReal_nonneg) (sum_toReal_probOutput _)
            intro z; exact toReal_probOutput_le_one _ _
          · have hp := operational_hockey_bound η δ (H >>= M) (M x) (D ω) (hhs x hx)
            have hpass : (∑ z, (Pr[= z | M x]).toReal *
                (Pr[= true | D ω z]).toReal) = (Pr[= true | M x >>= D ω]).toReal :=
              viewLaw_pass (M x) (D ω)
            rw [hpass]
            rw [hhω]
            exact hp
        have hdep := deploy_le X Z Bad (π ω) M (D ω) A r b hrec N 0 []
        have hcat := t3a Bad (fun x z => (Pr[= z | M x]).toReal)
          (fun z => (Pr[= true | D ω z]).toReal)
          (fun h x => (Pr[= x | π ω h]).toReal) r Aω b
          (fun _ _ => ENNReal.toReal_nonneg) (fun x => sum_toReal_probOutput _)
          (fun _ => ENNReal.toReal_nonneg) (fun _ => toReal_probOutput_le_one _ _)
          (fun _ _ => ENNReal.toReal_nonneg) (fun h => sum_toReal_probOutput _)
          hr0 hr1 hA0 hA1 hbad N 0 []
        have hAB : Aω ≤ 1 - r + r * Aω := by nlinarith
        have hcatBound : (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal ≤
            1 - r + r * Aω := by
          refine le_trans hdep (le_trans hcat ?_)
          split_ifs <;> linarith
        calc Sω * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
            ≤ Sω * (1 - r + r * min 1 (Real.exp η * hω + δ)) :=
              mul_le_mul_of_nonneg_left hcatBound hS0
          _ ≤ C := by
            have he : 0 ≤ Real.exp η := (Real.exp_pos η).le
            have hmin : min 1 (Real.exp η * hω + δ) ≤ Real.exp η * hω + δ := min_le_right _ _
            have hscaled : Sω * (Real.exp η * hω + δ) ≤ Real.exp η * B + δ := by
              calc
                Sω * (Real.exp η * hω + δ) = Real.exp η * (hω * Sω) + δ * Sω := by ring
                _ ≤ Real.exp η * B + δ := by
                  exact add_le_add
                    (mul_le_mul_of_nonneg_left (by simpa [Sω] using hmoment) he)
                    (by
                      calc
                        δ * Sω ≤ δ * 1 := mul_le_mul_of_nonneg_left hS1 hδ0
                        _ = δ := by ring)
            calc
              Sω * (1 - r + r * min 1 (Real.exp η * hω + δ))
                  = Sω * (1 - r) + r * (Sω * min 1 (Real.exp η * hω + δ)) := by ring
              _ ≤ (1 - r) + r * (Sω * (Real.exp η * hω + δ)) := by
                    apply add_le_add
                    · have h1r : 0 ≤ 1 - r := by linarith
                      calc
                        Sω * (1 - r) = (1 - r) * Sω := by ring
                        _ ≤ (1 - r) * 1 := mul_le_mul_of_nonneg_left hS1 h1r
                        _ = 1 - r := by ring
                    · exact mul_le_mul_of_nonneg_left
                        (mul_le_mul_of_nonneg_left hmin hS0) hr0
              _ ≤ C := by
                    rw [hC]
                    calc
                      1 - r + r * (Sω * (Real.exp η * hω + δ)) ≤
                          1 - r + r * (Real.exp η * B + δ) :=
                        by have hmul := mul_le_mul_of_nonneg_left hscaled hr0; linarith
                      _ = 1 - r + r * (δ + Real.exp η * B) := by ring
    _ = C := by rw [← Finset.sum_mul, hρ, one_mul]

#print axioms operational_hockey_bound
#print axioms softEndToEndHockey

end ControlStack.SoftHockey
