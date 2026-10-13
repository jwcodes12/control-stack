open scoped BigOperators
open ControlStack Finset
open ControlStack.Covert ControlStack.Leakage
open ControlStack.ChannelInstances
namespace PL_bg1n2_4

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

def FrozenBack : Prop :=
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


noncomputable def delta {A : Type} [Fintype A] [DecidableEq A] (a : A) : A → ℝ :=
  fun x => if x = a then 1 else 0


def BackHyp (k E : ℕ) (Ω Y O : Type) [Fintype Ω] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → Fin (2 ^ k) → ℝ) (c : List O → O → ℝ) (L : ℕ → ℝ) : Prop :=
  IsDist rho ∧ (∀ omega g, IsDist (dec omega g)) ∧
    (∀ omega m h z, 0 ≤ K omega m h z) ∧ (∀ g o, 0 ≤ c g o) ∧
    (∀ i, 0 ≤ L i) ∧ (∀ omega m, Dominated (K omega m) c) ∧
    (∀ g, (∑ o, c g o) ≤ L g.length)

def OrigHyp (k E : ℕ) (Ω Y O : Type) [Fintype Ω] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → Fin (2 ^ k) → ℝ) (c : List O → O → ℝ) (L : ℕ → ℝ) : Prop :=
  IsDist rho ∧ (∀ omega g, IsDist (dec omega g)) ∧
    (∀ omega m h z, 0 ≤ K omega m h z) ∧ (∀ g o, 0 ≤ c g o) ∧
    (∀ i, 0 ≤ L i) ∧ (∀ omega m, Dominated (K omega m) c) ∧
    (∀ g, (∑ o, c g o) ≤ L g.length)

def BackConclusion (k E : ℕ) (Ω Y O : Type) [Fintype Ω] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → Fin (2 ^ k) → ℝ) (c : List O → O → ℝ) (L : ℕ → ℝ) : Prop :=
  (∑ omega, rho omega * ((Fintype.card (Fin (2 ^ k)) : ℝ)⁻¹ *
    ∑ m, val (K omega m) (fun g => dec omega g m) E [])) ≤
    (∏ e : Fin E, L e.val) / (2 : ℝ) ^ k

def OrigConclusion (k E : ℕ) (Ω Y O : Type) [Fintype Ω] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → Fin (2 ^ k) → ℝ) (c : List O → O → ℝ) (L : ℕ → ℝ) : Prop :=
  (∑ omega, rho omega * (((2 : ℝ) ^ k)⁻¹ *
    ∑ m, val (K omega m) (fun g => dec omega g m) E [])) ≤
    (∏ e ∈ Finset.range E, L e) / (2 : ℝ) ^ k

def BackAt (k E : ℕ) (Ω Y O : Type) [Fintype Ω] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → Fin (2 ^ k) → ℝ) (c : List O → O → ℝ) (L : ℕ → ℝ) : Prop := BackHyp k E Ω Y O rho K dec c L → BackConclusion k E Ω Y O rho K dec c L

def OrigAt (k E : ℕ) (Ω Y O : Type) [Fintype Ω] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → Fin (2 ^ k) → ℝ) (c : List O → O → ℝ) (L : ℕ → ℝ) : Prop := OrigHyp k E Ω Y O rho K dec c L → OrigConclusion k E Ω Y O rho K dec c L

def ComponentwiseClaim : Prop :=
  ∀ (k E : ℕ) (Ω Y O : Type) [Fintype Ω] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → Fin (2 ^ k) → ℝ) (c : List O → O → ℝ) (L : ℕ → ℝ), (BackHyp k E Ω Y O rho K dec c L ↔ OrigHyp k E Ω Y O rho K dec c L) ∧ (BackConclusion k E Ω Y O rho K dec c L ↔ OrigConclusion k E Ω Y O rho K dec c L)

def Witness : Prop :=
  (∃ (rho : Unit → ℝ) (K : Unit → Fin 4 → List (Unit × Bool) → Unit × Bool → ℝ)
    (dec : Unit → List Bool → Fin 4 → ℝ),
    BackHyp 2 2 Unit Unit Bool rho K dec (fun _ _ => 1) (fun _ => 2)) ∧
  (BackHyp 1 1 Unit Unit Unit (fun _ => 1) (fun _ _ _ _ => 4)
    (fun _ _ => delta 0) (fun _ _ => 4) (fun _ => 4) ∧
   (∑ omega : Unit, (1 : ℝ) * ((Fintype.card (Fin 2) : ℝ)⁻¹ *
     ∑ m : Fin 2, val (fun (_ : List (Unit × Unit)) _ => (4 : ℝ))
       (fun (_ : List Unit) => delta (0 : Fin 2) m) 1 [])) = 2)

def Original : Prop :=
  ∀ {Ω Y O : Type} [Fintype Ω] [Fintype Y] [Fintype O] (k E : ℕ) (ρ : Ω → ℝ) (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ)
    (c : List O → O → ℝ) (L : ℕ → ℝ) (dec : Ω → List O → Fin (2 ^ k) → ℝ)
    (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c)
    (hc0 : ∀ g o, 0 ≤ c g o) (hL0 : ∀ i, 0 ≤ L i) (hL : ∀ g, ∑ o, c g o ≤ L g.length)
    (hdec : ∀ ω t, IsDist (dec ω t)),
    ∑ ω, ρ ω * (((2 : ℝ) ^ k)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) E [])
      ≤ (∏ e ∈ range E, L e) / 2 ^ k

def BackSchema : Prop := ∀ (k E : ℕ) (Ω Y O : Type) [Fintype Ω] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → Fin (2 ^ k) → ℝ) (c : List O → O → ℝ) (L : ℕ → ℝ), BackAt k E Ω Y O rho K dec c L

def OrigSchema : Prop := ∀ (k E : ℕ) (Ω Y O : Type) [Fintype Ω] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → Fin (2 ^ k) → ℝ) (c : List O → O → ℝ) (L : ℕ → ℝ), OrigAt k E Ω Y O rho K dec c L

def PointwiseClaim : Prop :=
  ComponentwiseClaim ∧ ∀ (k E : ℕ) (Ω Y O : Type) [Fintype Ω] [Fintype Y] [Fintype O]
    (rho : Ω → ℝ) (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ)
    (dec : Ω → List O → Fin (2 ^ k) → ℝ) (c : List O → O → ℝ) (L : ℕ → ℝ), BackAt k E Ω Y O rho K dec c L ↔ OrigAt k E Ω Y O rho K dec c L

def Claim : Prop :=
  (FrozenBack ↔ BackSchema) ∧ (Original ↔ OrigSchema) ∧ PointwiseClaim

end PL_bg1n2_4
