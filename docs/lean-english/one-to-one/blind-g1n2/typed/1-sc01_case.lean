import ControlStack.SafetyCaseSC01

open scoped BigOperators
open Classical

namespace ControlStack.SafetyCaseSC01

def Back_sc01_case : Prop :=
  (∀ (Ω S O : Type) [Fintype Ω] [Fintype S] [Fintype O]
      (rho : Ω → ℝ) (W : S → O → ℝ)
      (enc : Ω → Fin (2 ^ 32) → ControlStack.ScenarioARepair.Transcript × S → ℝ)
      (dec : Ω → ControlStack.ScenarioARepair.Transcript × O → Fin (2 ^ 32) → ℝ)
      (c : O → ℝ),
    ControlStack.Covert.IsDist rho →
    (∀ omega m, ControlStack.Covert.IsDist (enc omega m)) →
    (∀ omega y, ControlStack.Covert.IsDist (dec omega y)) →
    (∀ o, 0 ≤ c o) →
    (∀ s o, W s o ≤ c o) →
    (∑ o, c o) ≤ (65536 : ℝ) / 59049 →
    ControlStack.SideChannel.sideSuccess rho W enc dec ≤ (1 : ℝ) / 2 ^ 16) ∧
  (∀ p : ℝ, 0 ≤ p → p ≤ (9 : ℝ) / 10 →
    ControlStack.ScenarioAUsefulness.passProb p ≤ (1 : ℝ) / 80) ∧
  (ControlStack.ScenarioAUsefulness.tail 64 ((93382 : ℝ) / 100000) ≤ (1 : ℝ) / 80 ∧
    (9 : ℝ) / 10 ≤ (93382 : ℝ) / 100000) ∧
  (ControlStack.GatewayCore.viewSpace (C := 1) (fun _ => 1) (fun _ => 8) = 9 ∧
    Fintype.card ControlStack.ScenarioARepair.Transcript = 9 ^ 5) ∧
  (∀ (L : Type) [DecidableEq L] (tr : List (ControlStack.LifetimeLedger.Ev L)),
    (∀ e ∈ tr, ¬ ControlStack.LifetimeLedger.Ev.isRestore e) →
    (∀ ell k, ControlStack.LifetimeLedger.Ev.charge ell k ∈ tr → k = 9) →
    ∀ ell : L,
      (((ControlStack.LifetimeLedger.run (2 ^ 16)
        (some (fun _ : L => 1), []) tr).2).filter (fun a => a.1 = ell)).length ≤ 5)

end ControlStack.SafetyCaseSC01
