open scoped BigOperators
open ControlStack Finset
open ControlStack.Covert ControlStack.Leakage
open ControlStack.ChannelInstances
namespace PL_bg1n2_5

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

def FrozenBack : Prop :=
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


noncomputable def delta {A : Type} [Fintype A] [DecidableEq A] (a : A) : A → ℝ :=
  fun x => if x = a then 1 else 0


def BackHyp (n a E : ℕ) (Ω M Y O : Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → M → ℝ) (c : List O → O → ℝ) (L : ℝ) : Prop :=
  a + E ≤ n ∧ IsDist rho ∧ (∀ omega g, IsDist (dec omega g)) ∧
    (∀ omega m h z, 0 ≤ K omega m h z) ∧ (∀ g o, 0 ≤ c g o) ∧
    0 ≤ L ∧ (∀ omega m, Dominated (K omega m) c) ∧
    (∀ g, a ≤ g.length → g.length < a + E → (∑ o, c g o) ≤ L) ∧
    (∀ g, (g.length < a ∨ a + E ≤ g.length) → (∑ o, c g o) ≤ 1)

def OrigHyp (n a E : ℕ) (Ω M Y O : Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → M → ℝ) (c : List O → O → ℝ) (L : ℝ) : Prop :=
  a + E ≤ n ∧ IsDist rho ∧ (∀ omega g, IsDist (dec omega g)) ∧
    (∀ omega m h z, 0 ≤ K omega m h z) ∧ (∀ g o, 0 ≤ c g o) ∧
    0 ≤ L ∧ (∀ omega m, Dominated (K omega m) c) ∧
    (∀ g, (a ≤ g.length ∧ g.length < a + E) → (∑ o, c g o) ≤ L) ∧
    (∀ g, ¬(a ≤ g.length ∧ g.length < a + E) → (∑ o, c g o) ≤ 1)

def BackConclusion (n a E : ℕ) (Ω M Y O : Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → M → ℝ) (c : List O → O → ℝ) (L : ℝ) : Prop :=
  (∑ omega, rho omega * ((Fintype.card M : ℝ)⁻¹ *
    ∑ m, val (K omega m) (fun g => dec omega g m) n [])) ≤ L ^ E / (Fintype.card M : ℝ)

def OrigConclusion (n a E : ℕ) (Ω M Y O : Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → M → ℝ) (c : List O → O → ℝ) (L : ℝ) : Prop :=
  (∑ omega, rho omega * ((Fintype.card M : ℝ)⁻¹ *
    ∑ m, val (K omega m) (fun g => dec omega g m) n [])) ≤ L ^ E / (Fintype.card M : ℝ)

def BackAt (n a E : ℕ) (Ω M Y O : Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → M → ℝ) (c : List O → O → ℝ) (L : ℝ) : Prop := BackHyp n a E Ω M Y O rho K dec c L → BackConclusion n a E Ω M Y O rho K dec c L

def OrigAt (n a E : ℕ) (Ω M Y O : Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → M → ℝ) (c : List O → O → ℝ) (L : ℝ) : Prop := OrigHyp n a E Ω M Y O rho K dec c L → OrigConclusion n a E Ω M Y O rho K dec c L

def ComponentwiseClaim : Prop :=
  ∀ (n a E : ℕ) (Ω M Y O : Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → M → ℝ) (c : List O → O → ℝ) (L : ℝ), (BackHyp n a E Ω M Y O rho K dec c L ↔ OrigHyp n a E Ω M Y O rho K dec c L) ∧ (BackConclusion n a E Ω M Y O rho K dec c L ↔ OrigConclusion n a E Ω M Y O rho K dec c L)

def Witness : Prop :=
  ∃ (rho : Unit → ℝ) (K : Unit → Fin 4 → List (Unit × Bool) → Unit × Bool → ℝ)
    (dec : Unit → List Bool → Fin 4 → ℝ),
    BackHyp 3 1 1 Unit (Fin 4) Unit Bool rho K dec (fun _ _ => 1 / 2) 1

def Original : Prop :=
  ∀ {Ω Y O : Type} [Fintype Ω] [Fintype Y] [Fintype O] {M : Type} [Fintype M] [Nonempty M] (n a E : ℕ) (hE : a + E ≤ n) (L : ℝ) (hL0 : 0 ≤ L)
    (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (dec : Ω → List O → M → ℝ)
    (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c)
    (hc0 : ∀ g o, 0 ≤ c g o)
    (hin : ∀ g, a ≤ g.length ∧ g.length < a + E → ∑ o, c g o ≤ L)
    (hout : ∀ g, ¬(a ≤ g.length ∧ g.length < a + E) → ∑ o, c g o ≤ 1)
    (hdec : ∀ ω t, IsDist (dec ω t)),
    ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n [])
      ≤ L ^ E / (Fintype.card M : ℝ)

def BackSchema : Prop := ∀ (n a E : ℕ) (Ω M Y O : Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → M → ℝ) (c : List O → O → ℝ) (L : ℝ), BackAt n a E Ω M Y O rho K dec c L

def OrigSchema : Prop := ∀ (n a E : ℕ) (Ω M Y O : Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → M → ℝ) (c : List O → O → ℝ) (L : ℝ), OrigAt n a E Ω M Y O rho K dec c L

def PointwiseClaim : Prop :=
  ComponentwiseClaim ∧ ∀ (n a E : ℕ) (Ω M Y O : Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → M → ℝ) (c : List O → O → ℝ) (L : ℝ), BackAt n a E Ω M Y O rho K dec c L ↔ OrigAt n a E Ω M Y O rho K dec c L

def Claim : Prop :=
  (FrozenBack ↔ BackSchema) ∧ (Original ↔ OrigSchema) ∧ PointwiseClaim

end PL_bg1n2_5
