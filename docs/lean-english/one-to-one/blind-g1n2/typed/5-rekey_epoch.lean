import ControlStack.Families.F2.ChannelInstances

open scoped BigOperators
open ControlStack.Covert ControlStack.Leakage

namespace ControlStack.ChannelInstances

def Back_rekey_epoch : Prop :=
  ∀ (n a E : ℕ) (Ω M Y O : Type)
      [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] [Fintype O]
      (rho : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ)
      (dec : Ω → List O → M → ℝ) (c : List O → O → ℝ) (L : ℝ),
    a + E ≤ n →
    IsDist rho →
    (∀ omega g, IsDist (dec omega g)) →
    (∀ omega m h z, 0 ≤ K omega m h z) →
    (∀ g o, 0 ≤ c g o) →
    0 ≤ L →
    (∀ omega m, Dominated (K omega m) c) →
    (∀ g, a ≤ g.length → g.length < a + E → (∑ o, c g o) ≤ L) →
    (∀ g, (g.length < a ∨ a + E ≤ g.length) → (∑ o, c g o) ≤ 1) →
    (∑ omega, rho omega * ((Fintype.card M : ℝ)⁻¹ *
      ∑ m, val (K omega m) (fun g => dec omega g m) n [])) ≤
      L ^ E / (Fintype.card M : ℝ)

end ControlStack.ChannelInstances
