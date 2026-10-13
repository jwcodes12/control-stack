-- EXCERPT of ControlStack/SideChannel.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SideChannel

open Finset ControlStack.Covert

/-- success probability with a mediated view v ∈ V and a side observation o ~ W(s) of a sender-chosen side state s -/
noncomputable def sideSuccess {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O]
    (ρ : Ω → ℝ) (W : S → O → ℝ) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) : ℝ :=
  ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ x : V × S, enc ω m x * ∑ o, W x.2 o * dec ω (x.1, o) m)

/-- Binary symmetric side channel with crossover q ≤ 1/2: Σ_o max_s W s o = 2(1 − q). -/
def bsc (q : ℝ) : Bool → Bool → ℝ := fun s o => if s = o then 1 - q else q

end ControlStack.SideChannel

