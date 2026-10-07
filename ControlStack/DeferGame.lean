/-
VCVio operational bridge for audit-then-defer deployment.

At exhausted audit budget, a fresh halt computation may safely stop the run. On a
bad flagged submission, service catches it with its measured probability; if it
misses, the trusted replacement stays in place and deployment continues.
-/
import ControlStack.RefinementProof

open OracleComp

namespace ControlStack.DeferGame
open ControlStack.Refine

abbrev Service (X Z : Type) := Hist X Z → X → Z → ℝ

/-- Service-dependent catastrophe recursion from the ledger defer statement. -/
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
        else if Bad x then do
          let caught ← Svc h x z
          if caught then pure false
          else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,false)])
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
             if halt then pure false else do
               let caught ← Svc h x z
               if caught then pure false
               else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,false)])
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

/-- A safe halt gates access to the continuation with the false-output probability. -/
theorem halt_then_prob (H K : ProbComp Bool) :
    Pr[= true | do let halt ← H; if halt then pure false else K] =
      Pr[= false | H] * Pr[= true | K] := by
  rw [probOutput_bind_eq_tsum, tsum_fintype, Fintype.sum_bool]
  simp

theorem halt_then_real (H K : ProbComp Bool) :
    (Pr[= true | do let halt ← H; if halt then pure false else K]).toReal =
      (1 - (Pr[= true | H]).toReal) * (Pr[= true | K]).toReal := by
  rw [halt_then_prob, ENNReal.toReal_mul, ControlStack.Refine.probOutput_false_toReal]

/-- On a missed service check, the replacement stays in place and the continuation
is reached. -/
theorem halt_service_continue_real (H S C : ProbComp Bool) :
    (Pr[= true | do
      let halt ← H
      if halt then pure false else do
        let caught ← S
        if caught then pure false else C]).toReal =
      (1 - (Pr[= true | H]).toReal) *
        (1 - (Pr[= true | S]).toReal) * (Pr[= true | C]).toReal := by
  rw [halt_then_real, halt_then_real]
  ring

theorem calibrated_exhausted_benign_real (H C : ProbComp Bool) (η : ℝ)
    (hH : (Pr[= true | H]).toReal = η) :
    (Pr[= true | do let halt ← H; if halt then pure false else C]).toReal =
      (1 - η) * (Pr[= true | C]).toReal := by
  rw [halt_then_real, hH]

theorem calibrated_exhausted_bad_real (H S C : ProbComp Bool) (η a c : ℝ)
    (hH : (Pr[= true | H]).toReal = η)
    (hS : (Pr[= true | S]).toReal = a)
    (hC : (Pr[= true | C]).toReal = c) :
    (Pr[= true | do
      let halt ← H
      if halt then pure false else do
        let caught ← S
        if caught then pure false else C]).toReal = (1 - η) * (1 - a) * c := by
  rw [halt_service_continue_real, hH, hS, hC]

theorem calibrated_audit_escape_real (A : ProbComp Bool) (r : ℝ)
    (hA : (Pr[= true | A]).toReal = r) :
    (Pr[= true | (fun caught => !caught) <$> A]).toReal = 1 - r := by
  rw [ControlStack.Refine.probOutput_not_true, ControlStack.Refine.probOutput_false_toReal, hA]

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
/-- At an exhausted budget, a bad flag reaches continuation only when both
the halt coin and service miss. -/
theorem exhausted_benign_probability (H C : ProbComp Bool) :
    Pr[= true | do
      let halt ← H
      if halt then pure false else C] =
      Pr[= false | H] * Pr[= true | C] := by
  rw [probOutput_bind_eq_tsum]
  rw [tsum_fintype]
  simp only [Fintype.sum_bool]
  simp

theorem exhausted_bad_then_probability (H S C : ProbComp Bool) :
    Pr[= true | do
      let halt ← H
      if halt then pure false else do
        let caught ← S
        if caught then pure false else C] =
      Pr[= false | H] * Pr[= false | S] * Pr[= true | C] := by
  rw [halt_then_prob]
  rw [halt_then_prob]
  exact (mul_assoc _ _ _).symm

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
        else if Bad x then Pr[= false | Halt h x z] * Pr[= false | Svc h x z] *
          catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)])
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
      · simp [catVE, ih, hub, ControlStack.Refine.probOutput_not_true,
          exhausted_bad_then_probability, exhausted_benign_probability, mul_assoc]

theorem catVE_ne_top {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool)
    (Halt : Hist X Z → X → Z → ProbComp Bool)
    (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) :
    catVE Bad π M D A Halt Svc b n u h ≠ ⊤ := by
  rw [← deployV_eq_catVE Bad π M D A Halt Svc b n u h]
  exact probOutput_ne_top

theorem catVE_transition_ne_top {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool)
    (Halt : Hist X Z → X → Z → ProbComp Bool)
    (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ)
    (h : Hist X Z) (x : X) (z : Z) :
    (Pr[= true | D z] * (if Bad x then 1 else catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,true)])) +
      Pr[= false | D z] * (if u < b then
        (if Bad x then Pr[= false | A h x z]
         else catVE Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)]))
       else if Bad x then Pr[= false | Halt h x z] * Pr[= false | Svc h x z] *
         catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)])
         else Pr[= false | Halt h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]))) ≠ ⊤ := by
  apply ENNReal.add_ne_top.2
  constructor
  · apply ENNReal.mul_ne_top probOutput_ne_top
    by_cases hx : Bad x
    · simp [hx]
    · simp [hx]
      exact catVE_ne_top Bad π M D A Halt Svc b n u (h ++ [(x,z,true)])
  · apply ENNReal.mul_ne_top probOutput_ne_top
    by_cases hu : u < b
    · simp [hu]
      by_cases hx : Bad x
      · simp [hx]
      · simp [hx]
        exact catVE_ne_top Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)])
    · rw [if_neg hu]
      by_cases hx : Bad x
      · simp [hx]
        have hc : catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) ≠ ⊤ :=
          catVE_ne_top Bad π M D A Halt Svc b n u (h ++ [(x,z,false)])
        have hsc : Pr[= false | Svc h x z] *
            catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) ≠ ⊤ :=
          ENNReal.mul_ne_top probOutput_ne_top hc
        have hfinal : Pr[= false | Halt h x z] *
            (Pr[= false | Svc h x z] *
              catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)])) ≠ ⊤ :=
          ENNReal.mul_ne_top probOutput_ne_top hsc
        simpa [mul_assoc] using hfinal
      · simp [hx]
        exact ENNReal.mul_ne_top probOutput_ne_top
          (catVE_ne_top Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]))

theorem catVE_inner_ne_top {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool)
    (Halt : Hist X Z → X → Z → ProbComp Bool)
    (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ)
    (h : Hist X Z) (x : X) :
    (∑ z, Pr[= z | M x] *
      (Pr[= true | D z] * (if Bad x then 1 else catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,true)])) +
        Pr[= false | D z] * (if u < b then
          (if Bad x then Pr[= false | A h x z]
           else catVE Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)]))
       else if Bad x then Pr[= false | Halt h x z] * Pr[= false | Svc h x z] *
         catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)])
           else Pr[= false | Halt h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)])))) ≠ ⊤ := by
  apply ENNReal.sum_ne_top.2
  intro z _
  exact ENNReal.mul_ne_top probOutput_ne_top
    (catVE_transition_ne_top Bad π M D A Halt Svc b n u h x z)

/-- The operational ENNReal recursion converts to the calibrated real-valued
ledger recursion when the monitor, halt, and service probabilities match. -/
theorem catVE_toReal_eq_catV {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool)
    (Halt : Hist X Z → X → Z → ProbComp Bool)
    (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) (r η : ℝ)
    (a : Service X Z)
    (hA : ∀ h x z, Bad x → (Pr[= true | A h x z]).toReal = r)
    (hH : ∀ h x z, (Pr[= true | Halt h x z]).toReal = η)
    (hS : ∀ h x z, Bad x → (Pr[= true | Svc h x z]).toReal = a h x z) :
    ∀ n u h, (catVE Bad π M D A Halt Svc b n u h).toReal =
      catV Bad (fun x z => (Pr[= z | M x]).toReal)
        (fun z => (Pr[= true | D z]).toReal)
        (fun h x => (Pr[= x | π h]).toReal) r η a b n u h := by
  intro n
  induction n with
  | zero => intro u h; simp [catVE, catV]
  | succ n ih =>
    intro u h
    simp only [catVE, catV]
    rw [ENNReal.toReal_sum (fun x _ => ENNReal.mul_ne_top probOutput_ne_top
      (catVE_inner_ne_top Bad π M D A Halt Svc b n u h x))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun z _ => ENNReal.mul_ne_top
      probOutput_ne_top (catVE_transition_ne_top Bad π M D A Halt Svc b n u h x z))]
    congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    have htr := catVE_transition_ne_top Bad π M D A Halt Svc b n u h x z
    rcases ENNReal.add_ne_top.mp htr with ⟨hpass, hfail⟩
    rw [ENNReal.toReal_mul, ENNReal.toReal_add hpass hfail,
      ENNReal.toReal_mul, ENNReal.toReal_mul]
    by_cases hx : Bad x <;> by_cases hu : u < b <;>
      simp [hx, hu, ih, hA, hH, hS, ControlStack.Refine.probOutput_false_toReal]

theorem defer_bridge : DeferBridgeClaim := by
  intro X Z _ _ Bad _ π M D A Halt Svc b r η a hA hH hS n u h
  rw [deployV_eq_catVE]
  exact catVE_toReal_eq_catV Bad π M D A Halt Svc b r η a hA hH hS n u h

end ControlStack.DeferGame
