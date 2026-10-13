import ControlStack.Scenarios.SC05Signal

namespace ControlStack.SC05

def Back_zero_dependence_is_blind : Prop :=
  ∀ (Ω M V : Type) [Fintype Ω] [Fintype M] [Fintype V]
    (ρ : Ω → ℝ) (out : Ω → V → ℝ) (dec : Ω → V → M → ℝ),
    ControlStack.Covert.IsDist ρ →
    (∀ ω, ControlStack.Covert.IsDist (out ω)) →
    (∀ ω v, ControlStack.Covert.IsDist (dec ω v)) →
    ControlStack.Covert.successProb ρ (fun ω _m v => out ω v) dec =
      (Fintype.card M : ℝ)⁻¹

end ControlStack.SC05
