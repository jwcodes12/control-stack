import ControlStack.CovertChannel

open scoped BigOperators

namespace ControlStack.Covert

def Back_covert_bound_lifetime : Prop :=
  ∀ (E : ℕ) (Ω M : Type) (V : Fin E → Type)
      [Fintype Ω] [Fintype M] [Nonempty M] [∀ e, Fintype (V e)]
      (rho : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ)
      (dec : Ω → ((e : Fin E) → V e) → M → ℝ),
    IsDist rho →
    (∀ omega m, IsDist (enc omega m)) →
    (∀ omega v, IsDist (dec omega v)) →
    successProb rho enc dec ≤
      (∏ e : Fin E, (Fintype.card (V e) : ℝ)) / (Fintype.card M : ℝ)

end ControlStack.Covert
