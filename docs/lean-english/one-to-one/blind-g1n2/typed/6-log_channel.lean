import ControlStack.Families.F2.ChannelInstances

open scoped BigOperators
open ControlStack.Covert ControlStack.Leakage

namespace ControlStack.ChannelInstances

def Back_log_channel : Prop :=
  ∀ (Kt Q f m : ℕ) (Ω M Y : Type)
      [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
      (rho : Ω → ℝ)
      (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) →
        Y × (Fin Kt × (Fin f → Fin Q)) → ℝ)
      (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ),
    IsDist rho →
    (∀ omega g, IsDist (dec omega g)) →
    (∀ omega secret h z, 0 ≤ K omega secret h z) →
    (∀ omega secret h, (∑ y, ∑ o, K omega secret h (y, o)) ≤ 1) →
    (∑ omega, rho omega * ((Fintype.card M : ℝ)⁻¹ *
      ∑ secret, val (K omega secret) (fun g => dec omega g secret) m [])) ≤
      (Kt : ℝ) ^ m * (Q : ℝ) ^ (f * m) / (Fintype.card M : ℝ)

end ControlStack.ChannelInstances
