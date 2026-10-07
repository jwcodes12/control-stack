/-
VCVio operational bridge for stratified honeypot testing.

Each declared class gets an independent block of `m` honeypot calls and a separate
hard slack counter. Deployment starts only if every class block passes.
-/
import ControlStack.RefinementProof

open OracleComp

namespace ControlStack.StratifiedGame
open ControlStack.Refine ControlStack.Bridge

/-- The test for one class: accept iff at most `sc` honeypots PASS. -/
def classPasses {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z)
    (D : Z → ProbComp Bool) (m sc : ℕ) : ProbComp Bool :=
  (fun k => decide (k ≤ sc)) <$> honeypotPasses H M D m

/-- Run an independent hard-slack test for each class, halting at the first failure. -/
def stratifiedSurvives {X Z C : Type} (H : C → ProbComp X) (M : X → ProbComp Z)
    (D : Z → ProbComp Bool) (m sc : ℕ) : List C → ProbComp Bool
  | [] => pure true
  | e :: es => do
      let pass ← classPasses (H e) M D m sc
      if pass then stratifiedSurvives H M D m sc es else pure false

/-- One class passes with the binomial CDF probability from the honeypot bridge. -/
theorem classPasses_bridge {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z)
    (D : Z → ProbComp Bool) (m sc : ℕ) :
    (Pr[= true | classPasses H M D m sc]).toReal =
      binCDF m sc (Pr[= true | H >>= M >>= D]).toReal := by
  unfold classPasses
  rw [← probEvent_eq_eq_probOutput, probEvent_map]
  simpa [Function.comp_def, decide_eq_true_eq] using bridge X Z H M D m sc

/-- The stratified test's success probability is the product of its independent class CDFs. -/
theorem stratifiedSurvives_prob {X Z C : Type} (H : C → ProbComp X)
    (M : X → ProbComp Z) (D : Z → ProbComp Bool) (m sc : ℕ) (classes : List C) :
    (Pr[= true | stratifiedSurvives H M D m sc classes]).toReal =
      (classes.map fun e =>
        (Pr[= true | classPasses (H e) M D m sc]).toReal).prod := by
  induction classes with
  | nil => simp [stratifiedSurvives]
  | cons e es ih =>
      have hstep : Pr[= true | stratifiedSurvives H M D m sc (e :: es)] =
          Pr[= true | classPasses (H e) M D m sc] *
            Pr[= true | stratifiedSurvives H M D m sc es] := by
        rw [stratifiedSurvives, probOutput_bind_eq_tsum, tsum_fintype, Fintype.sum_bool]
        simp
      rw [hstep, ENNReal.toReal_mul, ih]
      simp [List.map, List.prod_cons]

/-- Replacing each class's test probability by its binomial closed form. -/
theorem stratifiedSurvives_binomial {X Z C : Type} (H : C → ProbComp X)
    (M : X → ProbComp Z) (D : Z → ProbComp Bool) (m sc : ℕ) (classes : List C) :
    (Pr[= true | stratifiedSurvives H M D m sc classes]).toReal =
      (classes.map fun e => binCDF m sc (Pr[= true | H e >>= M >>= D]).toReal).prod := by
  rw [stratifiedSurvives_prob]
  induction classes with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [classPasses_bridge]
      rw [ih]

/-- Seeded stratified protocol: all class audits pass before the ordinary deployment game begins. -/
def stratifiedProtocolGame {X Z C Ω : Type} (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : Ω → C → ProbComp X) (M : X → ProbComp Z)
    (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X)
    (A : Hist X Z → X → Z → ProbComp Bool) (classes : List C)
    (m sc b N : ℕ) : ProbComp Bool := do
  let ω ← ρ
  let kept ← stratifiedSurvives (H ω) M (D ω) m sc classes
  if kept then deploy Bad (π ω) M (D ω) A b N 0 [] else pure false

/-- Exact decomposition of the stratified protocol into seed, test, and deployment probabilities. -/
theorem stratifiedProtocol_factorization {X Z C Ω : Type} [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : Ω → C → ProbComp X) (M : X → ProbComp Z)
    (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X)
    (A : Hist X Z → X → Z → ProbComp Bool) (classes : List C)
    (m sc b N : ℕ) :
    (Pr[= true | stratifiedProtocolGame Bad ρ H M D π A classes m sc b N]).toReal =
      ∑ ω, (Pr[= ω | ρ]).toReal *
        (Pr[= true | stratifiedSurvives (H ω) M (D ω) m sc classes]).toReal *
        (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal := by
  have key : ∀ ω, Pr[= true | stratifiedSurvives (H ω) M (D ω) m sc classes >>= fun kept =>
      if kept then deploy Bad (π ω) M (D ω) A b N 0 [] else pure false] =
      Pr[= true | stratifiedSurvives (H ω) M (D ω) m sc classes] *
        Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []] := by
    intro ω
    rw [probOutput_bind_eq_tsum, tsum_fintype, Fintype.sum_bool]
    simp
  unfold stratifiedProtocolGame
  rw [probOutput_bind_eq_tsum, tsum_fintype]
  simp only [key]
  rw [ENNReal.toReal_sum (fun ω _ => by finiteness)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  ring

/-- Closed-form seeded decomposition, with one independent binomial CDF per tested class. -/
theorem stratifiedProtocol_binomial {X Z C Ω : Type} [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : Ω → C → ProbComp X) (M : X → ProbComp Z)
    (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X)
    (A : Hist X Z → X → Z → ProbComp Bool) (classes : List C)
    (m sc b N : ℕ) :
    (Pr[= true | stratifiedProtocolGame Bad ρ H M D π A classes m sc b N]).toReal =
      ∑ ω, (Pr[= ω | ρ]).toReal *
        (classes.map fun e => binCDF m sc (Pr[= true | H ω e >>= M >>= D ω]).toReal).prod *
        (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal := by
  rw [stratifiedProtocol_factorization]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [stratifiedSurvives_binomial]

/-- A list of probabilities has product at most one. -/
theorem listProduct_nonneg {C : Type} (classes : List C) (f : C → ℝ)
    (hf0 : ∀ e ∈ classes, 0 ≤ f e) : 0 ≤ (classes.map f).prod := by
  induction classes with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_nonneg (hf0 a (by simp))
        (ih (by intro x hx; exact hf0 x (List.mem_cons_of_mem a hx)))

theorem listProduct_le_one {C : Type} (classes : List C) (f : C → ℝ)
    (hf0 : ∀ e ∈ classes, 0 ≤ f e) (hf1 : ∀ e ∈ classes, f e ≤ 1) :
    (classes.map f).prod ≤ 1 := by
  induction classes with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.prod_cons]
      have ha0 := hf0 a (by simp)
      have ha1 := hf1 a (by simp)
      have htail0 : 0 ≤ (as.map f).prod :=
        listProduct_nonneg as f (by intro x hx; exact hf0 x (List.mem_cons_of_mem a hx))
      have htail1 := ih
        (by intro x hx; exact hf0 x (List.mem_cons_of_mem a hx))
        (by intro x hx; exact hf1 x (List.mem_cons_of_mem a hx))
      calc
        f a * (as.map f).prod ≤ 1 * (as.map f).prod :=
          mul_le_mul_of_nonneg_right ha1 htail0
        _ = (as.map f).prod := by ring
        _ ≤ 1 := htail1

/-- A product of class survival probabilities is bounded by any included class factor. -/
theorem listProduct_le_factor {C : Type} (classes : List C) (f : C → ℝ)
    (hf0 : ∀ e ∈ classes, 0 ≤ f e) (hf1 : ∀ e ∈ classes, f e ≤ 1)
    (e : C) (he : e ∈ classes) : (classes.map f).prod ≤ f e := by
  induction classes generalizing e with
  | nil => simp at he
  | cons a as ih =>
      simp only [List.map_cons, List.prod_cons]
      rcases List.mem_cons.mp he with hea | he
      · subst e
        have htail0 : 0 ≤ (as.map f).prod :=
          listProduct_nonneg as f (by intro x hx; exact hf0 x (List.mem_cons_of_mem a hx))
        have htail1 := listProduct_le_one as f
          (by intro x hx; exact hf0 x (List.mem_cons_of_mem a hx))
          (by intro x hx; exact hf1 x (List.mem_cons_of_mem a hx))
        calc
          f a * (as.map f).prod ≤ f a * 1 := mul_le_mul_of_nonneg_left htail1 (hf0 a (by simp))
          _ = f a := by ring
      · have htail := ih
          (by intro x hx; exact hf0 x (List.mem_cons_of_mem a hx))
          (by intro x hx; exact hf1 x (List.mem_cons_of_mem a hx)) e he
        have htail0 : 0 ≤ (as.map f).prod :=
          listProduct_nonneg as f (by intro x hx; exact hf0 x (List.mem_cons_of_mem a hx))
        have ha1 := hf1 a (by simp)
        calc
          f a * (as.map f).prod ≤ 1 * (as.map f).prod :=
            mul_le_mul_of_nonneg_right ha1 htail0
          _ = (as.map f).prod := by ring
          _ ≤ f e := htail


/-- End-to-end operational safety for the stratified test under classwise domination. -/
theorem stratifiedProtocolEndToEnd {X Z C Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (classOf : X → C) (classes : List C)
    (ρ : ProbComp Ω) (H : Ω → C → ProbComp X) (M : X → ProbComp Z)
    (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X)
    (A : Hist X Z → X → Z → ProbComp Bool) (m sc b N : ℕ) (r L : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L)
    (hrec : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal)
    (hclass : ∀ x, Bad x → classOf x ∈ classes)
    (hdom : ∀ ω x z, Bad x →
      (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H ω (classOf x) >>= M]).toReal) :
    (Pr[= true | stratifiedProtocolGame Bad ρ H M D π A classes m sc b N]).toReal ≤
      (1 - r) + r * (L * (((sc : ℝ) + 1) / ((m : ℝ) + 1))) := by
  rw [stratifiedProtocol_binomial]
  set B : ℝ := ((sc : ℝ) + 1) / ((m : ℝ) + 1)
  set Cbound : ℝ := (1 - r) + r * (L * B)
  have hρ : ∑ ω, (Pr[= ω | ρ]).toReal = 1 := sum_toReal_probOutput ρ
  calc
    ∑ ω, (Pr[= ω | ρ]).toReal *
        (classes.map (fun e => binCDF m sc
          (Pr[= true | H ω e >>= M >>= D ω]).toReal)).prod *
        (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
      ≤ ∑ ω, (Pr[= ω | ρ]).toReal * Cbound := by
        apply Finset.sum_le_sum
        intro ω _
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        let pass := fun x => ∑ z, (Pr[= z | M x]).toReal * (Pr[= true | D ω z]).toReal
        have hpass0 : ∀ x, 0 ≤ pass x := by
          intro x
          exact Finset.sum_nonneg fun z _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        have hpass1 : ∀ x, pass x ≤ 1 := by
          intro x
          apply wsum_le _ _ _ (fun _ => ENNReal.toReal_nonneg) (sum_toReal_probOutput _)
          intro z
          exact toReal_probOutput_le_one _ _
        let badSet := Finset.univ.filter Bad
        let Aω := if hne : badSet.Nonempty then badSet.sup' hne pass else 0
        have hA0 : 0 ≤ Aω := by
          by_cases hne : badSet.Nonempty
          · rcases hne with ⟨x, hx⟩
            dsimp only [Aω]
            rw [dif_pos ⟨x, hx⟩]
            exact le_trans (hpass0 x) (Finset.le_sup' pass hx)
          · simp [Aω, hne]
        have hA1 : Aω ≤ 1 := by
          by_cases hne : badSet.Nonempty
          · dsimp only [Aω]
            rw [dif_pos hne]
            exact Finset.sup'_le hne pass (by intro x hx; exact hpass1 x)
          · simp [Aω, hne]
        have hbad : ∀ x, Bad x → pass x ≤ Aω := by
          intro x hx
          have hne : badSet.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
          dsimp only [Aω]
          rw [dif_pos hne]
          exact Finset.le_sup' pass (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
        have hdep := deploy_le X Z Bad (π ω) M (D ω) A r b hrec N 0 []
        have hcat := t3a Bad (fun x z => (Pr[= z | M x]).toReal)
          (fun z => (Pr[= true | D ω z]).toReal)
          (fun h x => (Pr[= x | π ω h]).toReal) r Aω b
          (fun _ _ => ENNReal.toReal_nonneg) (fun x => sum_toReal_probOutput _)
          (fun _ => ENNReal.toReal_nonneg) (fun _ => toReal_probOutput_le_one _ _)
          (fun _ _ => ENNReal.toReal_nonneg) (fun h => sum_toReal_probOutput _)
          hr0 hr1 hA0 hA1 hbad N 0 []
        have hAdeploy : (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal ≤
            1 - r + r * Aω := by
          refine le_trans hdep (le_trans hcat ?_)
          have hAB : Aω ≤ 1 - r + r * Aω := by
            have hr : 0 ≤ 1 - r := by linarith
            have hA : 0 ≤ 1 - Aω := by linarith
            nlinarith [mul_nonneg hr hA]
          split_ifs <;> linarith
        let factors := fun e => binCDF m sc (Pr[= true | H ω e >>= M >>= D ω]).toReal
        have hf0 : ∀ e ∈ classes, 0 ≤ factors e := by
          intro e _
          dsimp [factors]
          rw [← classPasses_bridge]
          exact ENNReal.toReal_nonneg
        have hf1 : ∀ e ∈ classes, factors e ≤ 1 := by
          intro e _
          dsimp [factors]
          rw [← classPasses_bridge]
          exact toReal_probOutput_le_one _ _
        let S := (classes.map factors).prod
        have hS0 : 0 ≤ S := listProduct_nonneg classes factors hf0
        have hS1 : S ≤ 1 := listProduct_le_one classes factors hf0 hf1
        have hAS : Aω * S ≤ L * B := by
          by_cases hex : ∃ x, Bad x
          · have hne : badSet.Nonempty := by
              obtain ⟨x, hx⟩ := hex
              exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
            obtain ⟨x0, hx0mem, hmax⟩ := Finset.exists_max_image badSet pass hne
            have hx0 : Bad x0 := (Finset.mem_filter.mp hx0mem).2
            have hAeq : Aω = pass x0 := by
              dsimp only [Aω]
              rw [dif_pos hne]
              apply le_antisymm
              · exact Finset.sup'_le hne pass (fun x hx => hmax x hx)
              · exact Finset.le_sup' pass hx0mem
            let e0 := classOf x0
            have he0 : e0 ∈ classes := hclass x0 hx0
            have hsel : pass x0 ≤ Aω := hbad x0 hx0
            have hrate : pass x0 ≤ L * (Pr[= true | H ω e0 >>= M >>= D ω]).toReal := by
              have hxsum : pass x0 = ∑ z, (Pr[= z | M x0]).toReal * (Pr[= true | D ω z]).toReal := rfl
              have hesum : (Pr[= true | H ω e0 >>= M >>= D ω]).toReal =
                  ∑ z, (Pr[= z | H ω e0 >>= M]).toReal * (Pr[= true | D ω z]).toReal := by
                rw [probOutput_bind_eq_tsum, tsum_fintype,
                  ENNReal.toReal_sum (fun z _ => by finiteness)]
                simp only [ENNReal.toReal_mul]
              rw [hxsum, hesum, Finset.mul_sum]
              apply Finset.sum_le_sum
              intro z _
              calc
                (Pr[= z | M x0]).toReal * (Pr[= true | D ω z]).toReal ≤
                    (L * (Pr[= z | H ω e0 >>= M]).toReal) * (Pr[= true | D ω z]).toReal :=
                      mul_le_mul_of_nonneg_right (hdom ω x0 z hx0) ENNReal.toReal_nonneg
                _ = L * ((Pr[= z | H ω e0 >>= M]).toReal *
                    (Pr[= true | D ω z]).toReal) := by ring
            have hSfactor : S ≤ factors e0 := listProduct_le_factor classes factors hf0 hf1 e0 he0
            have he0rate0 : 0 ≤ (Pr[= true | H ω e0 >>= M >>= D ω]).toReal := ENNReal.toReal_nonneg
            have he0rate1 : (Pr[= true | H ω e0 >>= M >>= D ω]).toReal ≤ 1 :=
              toReal_probOutput_le_one _ _
            have hnext : binCDF (m + 1) (sc + 1)
                (Pr[= true | H ω e0 >>= M >>= D ω]).toReal ≤ 1 := by
              rw [← classPasses_bridge]
              exact toReal_probOutput_le_one _ _
            have hmoment := first_moment' m sc
              (Pr[= true | H ω e0 >>= M >>= D ω]).toReal he0rate0 he0rate1 hnext
            have hrateA : Aω ≤ L * (Pr[= true | H ω e0 >>= M >>= D ω]).toReal := by
              rw [hAeq]
              exact hrate
            calc
              Aω * S ≤ (L * (Pr[= true | H ω e0 >>= M >>= D ω]).toReal) * factors e0 :=
                mul_le_mul hrateA hSfactor hS0 (mul_nonneg hL he0rate0)
              _ = L * ((Pr[= true | H ω e0 >>= M >>= D ω]).toReal * factors e0) := by ring
              _ ≤ L * B := by
                exact mul_le_mul_of_nonneg_left (by simpa [factors] using hmoment) hL
          · have hAeq : Aω = 0 := by
              have hne : ¬ badSet.Nonempty := by
                intro hne
                obtain ⟨x, hx⟩ := hne
                exact hex ⟨x, (Finset.mem_filter.mp hx).2⟩
              have heq : badSet = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
              simp [Aω, hne, heq]
            rw [hAeq]
            nlinarith [mul_nonneg hL (show 0 ≤ B by positivity)]
        have hpoint : S * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal ≤ Cbound := by
          calc
            S * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal ≤
                S * (1 - r + r * Aω) := mul_le_mul_of_nonneg_left hAdeploy hS0
            _ = S * (1 - r) + r * (Aω * S) := by ring
            _ ≤ Cbound := by
              dsimp [Cbound, B]
              have hfirst : S * (1 - r) ≤ 1 - r := by
                have hr' : 0 ≤ 1 - r := by linarith [hr1]
                simpa using mul_le_mul_of_nonneg_right hS1 hr'
              have hsecond := mul_le_mul_of_nonneg_left hAS hr0
              nlinarith
        simpa [S, factors] using hpoint
    _ = Cbound := by
      rw [← Finset.sum_mul, hρ, one_mul]

#print axioms stratifiedSurvives_binomial
#print axioms stratifiedProtocol_binomial
#print axioms stratifiedProtocolEndToEnd

end ControlStack.StratifiedGame
