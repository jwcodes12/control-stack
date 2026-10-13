import ControlStack.GatewayCore

open scoped BigOperators
open Classical

namespace ControlStack.GatewayCore

def Back_core_bound : Prop :=
  ∀ (C L : ℕ) (Ω M R : Type) (S : Fin C → Type)
      [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R]
      [∀ c, Fintype (S c)] [Fintype (Ev C R)]
      (slots : Fin C → ℕ) (valid : (c : Fin C) → R → Option (S c))
      (rho : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ)
      (dec : Ω → View S slots → M → ℝ),
    ControlStack.Covert.IsDist rho →
    (∀ omega m, ControlStack.Covert.IsDist (enc omega m)) →
    (∀ omega v, ControlStack.Covert.IsDist (dec omega v)) →
    ControlStack.Covert.successProb rho
      (fun omega m => ControlStack.GatewayModel.push
        (fun tr : Fin L → Ev C R =>
          finalView (runG valid (init (S := S) (slots := slots)) (List.ofFn tr)))
        (enc omega m)) dec ≤
      (viewSpace slots (fun c => Fintype.card (S c)) : ℝ) / (Fintype.card M : ℝ)

end ControlStack.GatewayCore
