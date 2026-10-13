-- EXCERPT of ControlStack/CovertChannel.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.Covert

open Finset

/-- a probability vector -/
def IsDist {α : Type} [Fintype α] (p : α → ℝ) : Prop := (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- probability that the decoder recovers a uniform secret, averaged over the shared seed -/
noncomputable def successProb {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V]
    (ρ : Ω → ℝ) (enc : Ω → M → V → ℝ) (dec : Ω → V → M → ℝ) : ℝ :=
  ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ v, enc ω m v * dec ω v m)

end ControlStack.Covert

