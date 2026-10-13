import ControlStack.Families.F6.MonitorCollusion

namespace ControlStack.MonitorCollusion

open ControlStack.Covert

-- NOTE
-- NOT_FORMALISABLE: No information measure is defined in the excerpts for
-- the phrase "log base 2 of K bits". The statement below is the explicit
-- K / number-of-messages bound on exact decoding success.
-- AMBIGUOUS: The English does not require finitely many views or specify
-- the treatment of shared randomness. The available successProb uses finite
-- views and a finite shared seed, independent of the uniform message. Those
-- are the conventions below; a deterministic codebook uses a one-point seed.
def Back_canon_channel : Prop :=
  ∀ (Ω M V : Type) [Fintype Ω] [Fintype M] [Fintype V] [Nonempty M]
    (K : ℕ) (canon : V → Fin K) (ρ : Ω → ℝ)
    (enc : Ω → M → V → ℝ) (dec : Ω → Fin K → M → ℝ),
    IsDist ρ →
      (∀ ω m, IsDist (enc ω m)) →
        (∀ ω k, IsDist (dec ω k)) →
          successProb ρ enc (fun ω v m => dec ω (canon v) m) ≤
            (K : ℝ) / (Fintype.card M : ℝ)

end ControlStack.MonitorCollusion
