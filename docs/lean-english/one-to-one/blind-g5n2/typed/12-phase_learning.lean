import ControlStack.Families.F6.MonitorCollusion

namespace ControlStack.MonitorCollusion

open Finset ControlStack.Covert ControlStack.Leakage

-- NOTE
-- AMBIGUOUS: The English does not state that the hidden-state and visible-output
-- alphabets are finite. The provided val and Dominated definitions require
-- finite alphabets, so the statement below uses that scope.
-- Bool represents the two phases. Each val holds its phase constant throughout
-- the m rounds; guess sees only the visible transcript. No kernel normalization
-- or upper bound on its total mass is assumed.
def Back_phase_learning : Prop :=
  ∀ (Y O : Type) [Fintype Y] [Fintype O]
    (K : Bool → List (Y × O) → Y × O → ℝ)
    (c : List O → O → ℝ) (L : ℝ)
    (guess : List O → Bool → ℝ) (m : ℕ),
    (∀ φ h z, 0 ≤ K φ h z) →
      (∀ φ, Dominated (K φ) c) →
        0 ≤ L →
          (∀ g, (∑ o, c g o) ≤ L) →
            (∀ t, IsDist (guess t)) →
              (val (K false) (fun t => guess t false) m [] +
                val (K true) (fun t => guess t true) m []) / 2 ≤
                  L ^ m / 2

end ControlStack.MonitorCollusion
