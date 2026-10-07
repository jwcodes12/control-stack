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

#print axioms stratifiedSurvives_binomial
#print axioms stratifiedProtocol_binomial

end ControlStack.StratifiedGame
