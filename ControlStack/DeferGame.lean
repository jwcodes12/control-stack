/-
VCVio operational bridge for audit-then-defer deployment.

At exhausted audit budget, a fresh halt computation may safely stop the run; if it
continues, a service computation may safely incriminate a flagged bad submission.
-/
import ControlStack.RefinementProof

open OracleComp

namespace ControlStack.DeferGame
open ControlStack.Refine

abbrev Service (X Z : Type) := Hist X Z → X → Z → ℝ

/-- Service-dependent catastrophe recursion from the proofledger defer statement. -/
noncomputable def catV {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (φ : Z → ℝ) (π : Hist X Z → X → ℝ)
    (r η : ℝ) (a : Service X Z) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else catV Bad M φ π r η a b n u (h ++ [(x,z,true)])) +
       (1 - φ z) * (if u < b then
         (if Bad x then 1-r else catV Bad M φ π r η a b n (u+1) (h ++ [(x,z,false)]))
        else (1-η) * (if Bad x then 1-a h x z else 1) *
          catV Bad M φ π r η a b n u (h ++ [(x,z,false)])))

/-- `true` means an uncaught catastrophe. Halt and service `true` outputs mean safe. -/
def deployV {X Z : Type} (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool)
    (Halt : Hist X Z → X → Z → ProbComp Bool)
    (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ProbComp Bool
  | 0, _, _ => pure false
  | n+1, u, h => do
      let x ← π h
      let z ← M x
      let pass ← D z
      if pass then
        if Bad x then pure true else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,true)])
      else if u < b then
        if Bad x then (fun caught => !caught) <$> A h x z
        else deployV Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)])
      else do
        let halt ← Halt h x z
        if halt then pure false
        else if Bad x then
          (fun caught => !caught) <$> Svc h x z
        else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,false)])

/-- One operational step, expanded over the finite output spaces. -/
theorem deployV_step {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool)
    (Halt : Hist X Z → X → Z → ProbComp Bool)
    (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) :
    Pr[= true | deployV Bad π M D A Halt Svc b (n+1) u h] =
      ∑ x, Pr[= x | π h] * ∑ z, Pr[= z | M x] *
        (Pr[= true | D z] * Pr[= true | (if Bad x then pure true else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,true)]) : ProbComp Bool)] +
         Pr[= false | D z] * (if u < b then
           Pr[= true | (if Bad x then (fun caught => !caught) <$> A h x z
             else deployV Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)]) : ProbComp Bool)]
           else Pr[= true | (if Bad x then do
             let halt ← Halt h x z
             if halt then pure false else (fun caught => !caught) <$> Svc h x z
             else do
             let halt ← Halt h x z
             if halt then pure false else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) : ProbComp Bool)])) := by
  rw [deployV]
  simp only [probOutput_bind_eq_tsum, tsum_fintype, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  by_cases hx : Bad x <;> simp [hx]

/-- The operational defer recursion equals `catV` when the measured halt and service
probabilities are `η` and `a h x z`, respectively. -/
def DeferBridgeClaim : Prop :=
  ∀ {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool)
    (Halt : Hist X Z → X → Z → ProbComp Bool)
    (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) (r η : ℝ)
    (a : Service X Z)
    (hA : ∀ h x z, Bad x → (Pr[= true | A h x z]).toReal = r)
    (hH : ∀ h x z, (Pr[= true | Halt h x z]).toReal = η)
    (hS : ∀ h x z, Bad x → (Pr[= true | Svc h x z]).toReal = a h x z),
    ∀ n u h, (Pr[= true | deployV Bad π M D A Halt Svc b n u h]).toReal =
      catV Bad (fun x z => (Pr[= z | M x]).toReal)
        (fun z => (Pr[= true | D z]).toReal)
        (fun h x => (Pr[= x | π h]).toReal) r η a b n u h

end ControlStack.DeferGame

namespace ControlStack.DeferGame
open OracleComp
open ControlStack.Refine
/-- At an exhausted budget, a bad flag is catastrophic only when both the
halt coin and the service fail to return a safe outcome. -/
theorem exhausted_benign_probability (H C : ProbComp Bool) :
    Pr[= true | do
      let halt ← H
      if halt then pure false else C] =
      Pr[= false | H] * Pr[= true | C] := by
  rw [probOutput_bind_eq_tsum]
  rw [tsum_fintype]
  simp only [Fintype.sum_bool]
  simp

theorem exhausted_bad_probability (H S : ProbComp Bool) :
    Pr[= true | do
      let halt ← H
      if halt then pure false else (fun caught => !caught) <$> S] =
      Pr[= false | H] * Pr[= false | S] := by
  rw [probOutput_bind_eq_tsum]
  rw [tsum_fintype]
  simp only [Fintype.sum_bool]
  simp [ControlStack.Refine.probOutput_not_true]

/-- Exact ENNReal recursion induced by the operational defer game. -/
noncomputable def catVE {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool)
    (Halt : Hist X Z → X → Z → ProbComp Bool)
    (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ENNReal
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, Pr[= x | π h] * ∑ z, Pr[= z | M x] *
      (Pr[= true | D z] * (if Bad x then 1 else catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,true)])) +
       Pr[= false | D z] * (if u < b then
         (if Bad x then Pr[= false | A h x z]
          else catVE Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)]))
        else if Bad x then Pr[= false | Halt h x z] * Pr[= false | Svc h x z]
          else Pr[= false | Halt h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)])))

/-- The operational catastrophe probability is exactly `catVE`, with no conversion
through `ℝ` and no calibration assumptions on the component kernels. -/
theorem deployV_eq_catVE {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool)
    (Halt : Hist X Z → X → Z → ProbComp Bool)
    (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) :
    ∀ n u h, Pr[= true | deployV Bad π M D A Halt Svc b n u h] =
      catVE Bad π M D A Halt Svc b n u h := by
  intro n
  induction n with
  | zero => intro u h; simp [deployV, catVE]
  | succ n ih =>
      intro u h
      rw [deployV_step]
      by_cases hub : u < b
      · simp [catVE, ih, hub, ControlStack.Refine.probOutput_not_true]
      · simp [catVE, ih, hub, ControlStack.Refine.probOutput_not_true, exhausted_bad_probability, exhausted_benign_probability]

end ControlStack.DeferGame
