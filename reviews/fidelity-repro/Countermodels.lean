import ControlStack

/-!
  Isolated reproductions for English-to-Lean applicability mismatches.
  None contradicts a Lean theorem; each witnesses why an extra real-world
  inference is invalid. Source: 083874048518b68d754f0c392ad0cb84f01174ba.
-/
namespace FidelityRepro

open ControlStack.Gate

-- F01: A valid gate Spec can observe zero effects even when a dangerous
-- state is reached, because effects is a modeling projection.
def hiddenHarmSystem : System Bool Bool Unit where
  step := fun _ action => action
  effects := fun _ => []

def hiddenHarmSpec : Spec hiddenHarmSystem where
  Inv := fun _ => True
  ok := fun _ _ => True
  step_inv := by intro _ _ _; trivial
  log_prefix := by intro _ _; simp [hiddenHarmSystem]
  inv_ok := by intro _ _ _ he; simp [hiddenHarmSystem] at he

theorem f01_satisfiable_spec_and_hidden_harm :
    (hiddenHarmSystem.run false [true]) = true ∧
    hiddenHarmSystem.effects (hiddenHarmSystem.run false [true]) = [] ∧
    hiddenHarmSpec.Inv (hiddenHarmSystem.run false [true]) := by
  refine ⟨rfl, rfl, ?_⟩
  trivial

theorem f01_existing_theorem_still_applies :
    hiddenHarmSpec.Inv (hiddenHarmSystem.run false [true]) ∧
    hiddenHarmSystem.effects false <+:
      hiddenHarmSystem.effects (hiddenHarmSystem.run false [true]) ∧
    ∀ e ∈ hiddenHarmSystem.effects (hiddenHarmSystem.run false [true]),
      hiddenHarmSpec.ok (hiddenHarmSystem.run false [true]) e := by
  exact Spec.trace_safe hiddenHarmSpec false [true] trivial

-- F06: a one-round attack can be detected while its external irreversible
-- side effect has already happened. survInd is zero because the round was
-- audited. The harm marker is an intentionally *external* interpretation.
def auditSchedule : Finset (Fin 1) := {0}

def attackWithCatch : List (ControlStack.Leakage.AOut Unit) :=
  [(true, (), true)]

def outsideIrreversibleHarm (t : List (ControlStack.Leakage.AOut Unit)) : Bool :=
  t.any (fun o => o.1)

theorem f06_attack_is_audited :
    ControlStack.Leakage.attackSet (N := 1) attackWithCatch =
      auditSchedule := by decide

theorem f06_not_survival :
    ControlStack.Leakage.survInd (N := 1) 1 auditSchedule attackWithCatch = 0 := by
  have hx : ¬ Disjoint auditSchedule
      (ControlStack.Leakage.attackSet (N := 1) attackWithCatch) := by decide
  simp [ControlStack.Leakage.survInd, hx]

theorem f06_harm_even_when_survival_zero :
    outsideIrreversibleHarm attackWithCatch = true ∧
    ControlStack.Leakage.survInd (N := 1) 1 auditSchedule attackWithCatch = 0 := by
  constructor
  · decide
  · exact f06_not_survival

-- F12: under the same Bernoulli(1/2) marginals, coupling changes the
-- probability of joint acceptance. The core composition theorem defines
-- the product sampling law, so this does not refute it.
def independent (z t : Bool) : ℚ := 1 / 4
def sameCoin (z t : Bool) : ℚ := if z = t then 1 / 2 else 0
def bothPass (z t : Bool) : ℚ := if z && t then 1 else 0

theorem f12_same_first_marginal (z : Bool) :
    (∑ t : Bool, independent z t) = (∑ t : Bool, sameCoin z t) := by
  cases z <;> norm_num [Fintype.sum_bool, independent, sameCoin]

theorem f12_same_second_marginal (t : Bool) :
    (∑ z : Bool, independent z t) = (∑ z : Bool, sameCoin z t) := by
  cases t <;> norm_num [Fintype.sum_bool, independent, sameCoin]

theorem f12_product_accepts_quarter :
    (∑ z : Bool, ∑ t : Bool, independent z t * bothPass z t) = 1 / 4 := by
  norm_num [Fintype.sum_bool, independent, bothPass] <;> decide

theorem f12_correlated_accepts_half :
    (∑ z : Bool, ∑ t : Bool, sameCoin z t * bothPass z t) = 1 / 2 := by
  norm_num [Fintype.sum_bool, sameCoin, bothPass]

theorem f12_same_marginals_different_joint_risk :
    (∑ z : Bool, ∑ t : Bool, independent z t * bothPass z t) <
    (∑ z : Bool, ∑ t : Bool, sameCoin z t * bothPass z t) := by
  rw [f12_product_accepts_quarter, f12_correlated_accepts_half]
  norm_num

#print axioms f01_satisfiable_spec_and_hidden_harm
#print axioms f01_existing_theorem_still_applies
#print axioms f06_not_survival
#print axioms f06_harm_even_when_survival_zero
#print axioms f12_same_marginals_different_joint_risk

end FidelityRepro
