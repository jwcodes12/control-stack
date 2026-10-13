-- EXCERPT of ControlStack/CovertNoGo.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.CovertNoGo

open ControlStack.Covert

/-- success of a trace-level encoder whose traces are observed through `view` -/
noncomputable def successView {M T V : Type} [Fintype M] [Fintype T]
    (view : T → V) (enc : M → T → ℝ) (dec : V → M → ℝ) : ℝ :=
  (Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ t, enc m t * dec (view t) m

end ControlStack.CovertNoGo

