import ControlStack.Families.F2.ChannelInstances

open scoped BigOperators
open ControlStack.Covert ControlStack.Leakage

namespace ControlStack.ChannelInstances

def Back_sc02_accumulated : Prop :=
  ∀ (k E : ℕ) (Ω Y O : Type) [Fintype Ω] [Fintype Y] [Fintype O]
      (rho : Ω → ℝ)
      (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ)
      (dec : Ω → List O → Fin (2 ^ k) → ℝ)
      (c : List O → O → ℝ) (L : ℕ → ℝ),
    IsDist rho →
    (∀ omega g, IsDist (dec omega g)) →
    (∀ omega m h z, 0 ≤ K omega m h z) →
    (∀ g o, 0 ≤ c g o) →
    (∀ i, 0 ≤ L i) →
    (∀ omega m, Dominated (K omega m) c) →
    (∀ g, (∑ o, c g o) ≤ L g.length) →
    (∑ omega, rho omega * ((Fintype.card (Fin (2 ^ k)) : ℝ)⁻¹ *
      ∑ m, val (K omega m) (fun g => dec omega g m) E [])) ≤
      (∏ e : Fin E, L e.val) / (2 : ℝ) ^ k

end ControlStack.ChannelInstances
