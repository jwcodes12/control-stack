/-
VCVio interface for the constant-hazard soft-slack honeypot test.

Each honeypot is sampled and monitored freshly. A PASS then triggers an independent
rejection coin with probability `1/(d+1)`; a rejection ends the test. Setting
`ns = d+1` gives the UMSURV soft-slack hazard `1/ns`, with survival `(1 - h/ns)^n`.
-/
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.ProbComp
import ControlStack.RefinementProof

open OracleComp

namespace ControlStack.SoftSlack
open ControlStack.Refine

def rejectionCoin (d : ℕ) : ProbComp Bool := do
  let j ← $[0..d]
  pure (j.val = 0)

def survives {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (d : ℕ) : ℕ → ProbComp Bool
  | 0 => pure true
  | n + 1 => do
      let pass ← H >>= M >>= D
      if pass then do
        let reject ← rejectionCoin d
        if reject then pure false else survives H M D d n
      else
        survives H M D d n

theorem rejection_rate (d : ℕ) :
  (Pr[= true | rejectionCoin d]).toReal = 1 / ((d + 1 : ℕ) : ℝ) := by
  simp [rejectionCoin, probOutput_map_eq_sum_finSupport_ite, ProbComp.finSupport_uniformFin,
    ProbComp.probOutput_uniformFin, Finset.sum_ite_eq']
  rw [ENNReal.toReal_add (by simp) (by simp)]
  norm_num

theorem survives_step {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z)
    (D : Z → ProbComp Bool) (d n : ℕ) :
    Pr[= true | survives H M D d (n + 1)] =
      Pr[= true | H >>= M >>= D] * Pr[= false | rejectionCoin d] *
          Pr[= true | survives H M D d n] +
        Pr[= false | H >>= M >>= D] * Pr[= true | survives H M D d n] := by
  rw [survives]
  simp only [probOutput_bind_eq_tsum, tsum_fintype, Fintype.sum_bool]
  have hbranch :
      Pr[= true | do
        let reject ← rejectionCoin d
        if reject then pure false else survives H M D d n] =
        Pr[= false | rejectionCoin d] * Pr[= true | survives H M D d n] := by
    rw [probOutput_bind_eq_tsum, tsum_fintype, Fintype.sum_bool]
    simp
  simp
  rw [hbranch]
  ring

theorem survives_step_real {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z)
    (D : Z → ProbComp Bool) (d n : ℕ) :
    (Pr[= true | survives H M D d (n + 1)]).toReal =
      (1 - (Pr[= true | H >>= M >>= D]).toReal / ((d + 1 : ℕ) : ℝ)) *
        (Pr[= true | survives H M D d n]).toReal := by
  rw [survives_step, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ControlStack.Refine.probOutput_false_toReal, rejection_rate,
    ControlStack.Refine.probOutput_false_toReal]
  ring

def BridgeClaim : Prop :=
  ∀ (X Z : Type) (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (d n : ℕ),
    (Pr[= true | survives H M D d n]).toReal =
      (1 - (Pr[= true | H >>= M >>= D]).toReal / ((d + 1 : ℕ) : ℝ)) ^ n

theorem bridge : BridgeClaim := by
  intro X Z H M D d n
  induction n with
  | zero => simp [survives]
  | succ n ih =>
      rw [survives_step_real, ih]
      ring

theorem geom_poly_bound (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + (n : ℝ) * x) * (1 - x) ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
      rw [hcast]
      have hfactor : (1 + ((n : ℝ) + 1) * x) * (1 - x) ≤ 1 + (n : ℝ) * x := by
        nlinarith [sq_nonneg x]
      calc
        (1 + ((n : ℝ) + 1) * x) * ((1 - x) ^ n * (1 - x))
            = ((1 + ((n : ℝ) + 1) * x) * (1 - x)) * (1 - x) ^ n := by ring
        _ ≤ (1 + (n : ℝ) * x) * (1 - x) ^ n :=
              mul_le_mul_of_nonneg_right hfactor (pow_nonneg (by linarith) n)
        _ ≤ 1 := ih

theorem soft_survival_first_moment (nh ns : ℕ) (h : ℝ) (hns : 1 ≤ ns)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    h * (1 - h / (ns : ℝ)) ^ nh ≤ (ns : ℝ) / ((nh : ℝ) + 1) := by
  have hns0 : 0 < (ns : ℝ) := by exact_mod_cast (by omega : 0 < ns)
  let x := h / (ns : ℝ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hns1 : (1 : ℝ) ≤ (ns : ℝ) := by exact_mod_cast hns
  have hx1 : x ≤ 1 := by
    dsimp [x]
    rw [div_le_one hns0]
    exact hh1.trans hns1
  have hpoly := geom_poly_bound nh x hx0 hx1
  have hweight : ((nh : ℝ) + 1) * x ≤ 1 + (nh : ℝ) * x := by
    have hn : (nh : ℝ) + 1 = ((nh + 1 : ℕ) : ℝ) := by norm_num
    rw [hn]
    nlinarith [mul_le_mul_of_nonneg_right hx1 (show 0 ≤ (nh : ℝ) by positivity)]
  have hprod : ((nh : ℝ) + 1) * (x * (1 - x) ^ nh) ≤ 1 := by
    calc
      ((nh : ℝ) + 1) * (x * (1 - x) ^ nh)
          = (((nh : ℝ) + 1) * x) * (1 - x) ^ nh := by ring
      _ ≤ (1 + (nh : ℝ) * x) * (1 - x) ^ nh :=
            mul_le_mul_of_nonneg_right hweight (pow_nonneg (by linarith) nh)
      _ ≤ 1 := hpoly
  have hfrac : x * (1 - x) ^ nh ≤ 1 / ((nh : ℝ) + 1) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [hprod]
  have hx : h = (ns : ℝ) * x := by
    dsimp [x]
    field_simp
  rw [hx]
  calc
    (ns : ℝ) * x * (1 - (ns : ℝ) * x / (ns : ℝ)) ^ nh
        = (ns : ℝ) * (x * (1 - x) ^ nh) := by field_simp
    _ ≤ (ns : ℝ) * (1 / ((nh : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = (ns : ℝ) / ((nh : ℝ) + 1) := by ring

/- Whole protocol with a constant-hazard soft-slack test before deployment. -/
def softProtocolGame {X Z Ω : Type} (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool)
    (nh ns b N : ℕ) : ProbComp Bool := do
  let ω ← ρ
  let kept ← survives H M (D ω) (ns - 1) nh
  if kept then deploy Bad (π ω) M (D ω) A b N 0 [] else pure false

/-- The soft-slack protocol factors into test survival and deployment, conditional on its seed. -/
theorem protocol_factorization {X Z Ω : Type} [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool)
    (nh ns b N : ℕ) :
    (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal =
      ∑ ω, (Pr[= ω | ρ]).toReal *
        (Pr[= true | survives H M (D ω) (ns - 1) nh]).toReal *
        (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal := by
  have key : ∀ ω, Pr[= true | survives H M (D ω) (ns - 1) nh >>= fun kept =>
      if kept then deploy Bad (π ω) M (D ω) A b N 0 [] else pure false] =
      Pr[= true | survives H M (D ω) (ns - 1) nh] *
        Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []] := by
    intro ω
    rw [probOutput_bind_eq_tsum, tsum_fintype, Fintype.sum_bool]
    simp
  unfold softProtocolGame
  rw [probOutput_bind_eq_tsum, tsum_fintype]
  simp only [key]
  rw [ENNReal.toReal_sum (fun ω _ => by finiteness)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  ring

/-- Closed form of the seed-conditional soft-slack survival probability. -/
theorem protocol_survival_formula {X Z Ω : Type} [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool)
    (nh ns b N : ℕ) (hns : 1 ≤ ns) :
    (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal =
      ∑ ω, (Pr[= ω | ρ]).toReal *
        (1 - (Pr[= true | H >>= M >>= D ω]).toReal / (ns : ℝ)) ^ nh *
        (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal := by
  rw [protocol_factorization]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [bridge]
  have hn : ns - 1 + 1 = ns := Nat.sub_add_cancel hns
  rw [hn]

/-- End-to-end soft-slack bound under the same domination and recall hypotheses as the hard-slack bridge. -/
theorem softEndToEnd {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool)
    (nh ns b N : ℕ) (r L : ℝ) (hns : 1 ≤ ns)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L)
    (hrec : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal)
    (hdom : ∀ x, Bad x → ∀ z,
      (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) :
    (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal ≤
      (1 - r) + r * (L * ((ns : ℝ) / ((nh : ℝ) + 1))) := by
  rw [protocol_survival_formula Bad ρ H M D π A nh ns b N hns]
  set C : ℝ := (1 - r) + r * (L * ((ns : ℝ) / ((nh : ℝ) + 1))) with hC
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
        have hB := soft_survival_first_moment nh ns hω hns hh0 hh1
        have hsum : hω = ∑ z, (Pr[= z | H >>= M]).toReal * (Pr[= true | D ω z]).toReal := by
          rw [hhω, probOutput_bind_eq_tsum, tsum_fintype,
            ENNReal.toReal_sum (fun z _ => by finiteness)]
          simp only [ENNReal.toReal_mul]
        set Aω := min 1 (L * hω) with hAω
        have hA0 : 0 ≤ Aω := le_min zero_le_one (mul_nonneg hL hh0)
        have hA1 : Aω ≤ 1 := min_le_left _ _
        have hbad : ∀ x, Bad x → ∑ z, (Pr[= z | M x]).toReal *
            (Pr[= true | D ω z]).toReal ≤ Aω := by
          intro x hx
          apply le_min
          · apply wsum_le _ _ _ (fun _ => ENNReal.toReal_nonneg) (sum_toReal_probOutput _)
            intro z; exact toReal_probOutput_le_one _ _
          · rw [hsum, Finset.mul_sum]
            apply Finset.sum_le_sum
            intro z _
            calc (Pr[= z | M x]).toReal * (Pr[= true | D ω z]).toReal
                ≤ (L * (Pr[= z | H >>= M]).toReal) * (Pr[= true | D ω z]).toReal :=
                  mul_le_mul_of_nonneg_right (hdom x hx z) ENNReal.toReal_nonneg
              _ = L * ((Pr[= z | H >>= M]).toReal * (Pr[= true | D ω z]).toReal) := by ring
        have hdep := deploy_le X Z Bad (π ω) M (D ω) A r b hrec N 0 []
        have hcat := t3a Bad (fun x z => (Pr[= z | M x]).toReal)
          (fun z => (Pr[= true | D ω z]).toReal)
          (fun h x => (Pr[= x | π ω h]).toReal) r Aω b
          (fun _ _ => ENNReal.toReal_nonneg) (fun x => sum_toReal_probOutput _)
          (fun _ => ENNReal.toReal_nonneg) (fun _ => toReal_probOutput_le_one _ _)
          (fun _ _ => ENNReal.toReal_nonneg) (fun h => sum_toReal_probOutput _)
          hr0 hr1 hA0 hA1 hbad N 0 []
        have hAB : Aω ≤ 1 - r + r * Aω := by nlinarith
        have hP : (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal ≤
            1 - r + r * Aω := by
          refine le_trans hdep (le_trans hcat ?_)
          split_ifs <;> linarith
        have hbound := ControlStack.Refine.final_dom Sω hω L r Aω
          ((ns : ℝ) / ((nh : ℝ) + 1))
          hS0 hS1 hr0 hr1 hL (min_le_right _ _) hB
        calc Sω * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
            ≤ Sω * (1 - r + r * Aω) := mul_le_mul_of_nonneg_left hP hS0
          _ ≤ C := hbound
    _ = C := by rw [← Finset.sum_mul, hρ, one_mul]

#print axioms bridge
#print axioms protocol_survival_formula
#print axioms softEndToEnd

end ControlStack.SoftSlack
