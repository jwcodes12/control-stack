namespace PL_bg5n2_12
open Finset ControlStack.MonitorCollusion ControlStack.Covert ControlStack.Leakage
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

def OriginalFamily : Prop :=
  ∀ (Y O : Type) [Fintype Y] [Fintype O]
    (K : Bool → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (L : ℝ),
    (∀ φ h z, 0 ≤ K φ h z) → (∀ φ, Dominated (K φ) c) →
    (∀ g o, 0 ≤ c g o) → 0 ≤ L → (∀ g, ∑ o, c g o ≤ L) →
    ∀ (guess : List O → Bool → ℝ), (∀ t, IsDist (guess t)) → ∀ m,
      (∑ φ : Bool, (1/2:ℝ)*val (K φ) (fun t => guess t φ) m []) ≤ (1/2)*L^m
def Claim : Prop :=
  (∀ (Y O : Type) [Fintype Y] [Fintype O]
    (K : Bool → List (Y × O) → Y × O → ℝ) (L : ℝ)
    (guess : List O → Bool → ℝ) (m : ℕ),
    ((val (K false) (fun t => guess t false) m [] +
      val (K true) (fun t => guess t true) m []) / 2 ≤ L^m/2 ↔
     (∑ φ : Bool, (1/2:ℝ)*val (K φ) (fun t => guess t φ) m []) ≤ (1/2)*L^m)) ∧
  (Back_phase_learning ↔ OriginalFamily)
def BasicWitness : Prop :=
  (∀ φ h z, 0 ≤ bscK φ h z) ∧
  (∀ φ, Dominated (bscK φ) (fun _ _ => (101/200:ℝ))) ∧
  (∀ g : List Bool, (∑ _o : Bool, (101/200:ℝ)) ≤ 101/100) ∧
  (∀ t : List Bool, IsDist (fun _ : Bool => (1/2:ℝ))) ∧
  (101/100:ℝ)^10/2 < 553/1000
def HeavyK : Bool → List (Unit × Unit) → Unit × Unit → ℝ := fun _ _ _ => 3
def HeavyC : List Unit → Unit → ℝ := fun _ _ => 3
noncomputable def HalfGuess : List Unit → Bool → ℝ := fun _ _ => 1/2
def LimitWitness : Prop :=
  (∀ φ h z, 0 ≤ HeavyK φ h z) ∧
  (∀ φ, Dominated (HeavyK φ) HeavyC) ∧
  (∀ g o, 0 ≤ HeavyC g o) ∧ (0 ≤ (3:ℝ)) ∧
  (∀ g, (∑ o, HeavyC g o) ≤ 3) ∧
  (∀ t, IsDist (HalfGuess t)) ∧
  (val (HeavyK false) (fun t => HalfGuess t false) 1 [] +
    val (HeavyK true) (fun t => HalfGuess t true) 1 []) / 2 = 3/2 ∧
  (1:ℝ) < 3/2
def Witness : Prop := BasicWitness ∧ LimitWitness
end PL_bg5n2_12
