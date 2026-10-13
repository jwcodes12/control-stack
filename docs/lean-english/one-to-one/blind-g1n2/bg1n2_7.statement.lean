open scoped BigOperators
open ControlStack Finset
open ControlStack.Covert ControlStack.Leakage
open ControlStack.ChannelInstances
namespace PL_bg1n2_7

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

def FrozenBack : Prop :=
  ∀ (Kc m : ℕ) (Ω M Y : Type)
      [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
      (rho : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ)
      (dec : Ω → List (Fin Kc) → M → ℝ),
    IsDist rho →
    (∀ omega g, IsDist (dec omega g)) →
    (∀ omega secret h z, 0 ≤ K omega secret h z) →
    (∀ omega secret h, (∑ y, ∑ o, K omega secret h (y, o)) ≤ 1) →
    (∑ omega, rho omega * ((Fintype.card M : ℝ)⁻¹ *
      ∑ secret, val (K omega secret) (fun g => dec omega g secret) m [])) ≤
      (Kc : ℝ) ^ m / (Fintype.card M : ℝ)


noncomputable def delta {A : Type} [Fintype A] [DecidableEq A] (a : A) : A → ℝ :=
  fun x => if x = a then 1 else 0


def BackHyp (Kc m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ)
    (dec : Ω → List (Fin Kc) → M → ℝ) : Prop :=
  IsDist rho ∧ (∀ omega g, IsDist (dec omega g)) ∧ (∀ omega secret h z, 0 ≤ K omega secret h z) ∧
    (∀ omega secret h, (∑ y, ∑ o, K omega secret h (y, o)) ≤ 1)

def OrigHyp (Kc m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ)
    (dec : Ω → List (Fin Kc) → M → ℝ) : Prop :=
  IsDist rho ∧ (∀ omega g, IsDist (dec omega g)) ∧ (∀ omega secret h z, 0 ≤ K omega secret h z) ∧
    (∀ omega secret h, (∑ z, K omega secret h z) ≤ 1)

def BackConclusion (Kc m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ)
    (dec : Ω → List (Fin Kc) → M → ℝ) : Prop :=
  (∑ omega, rho omega * ((Fintype.card M : ℝ)⁻¹ *
    ∑ secret, val (K omega secret) (fun g => dec omega g secret) m [])) ≤
    (Kc : ℝ) ^ m / (Fintype.card M : ℝ)

def OrigConclusion (Kc m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ)
    (dec : Ω → List (Fin Kc) → M → ℝ) : Prop :=
  (∑ omega, rho omega * ((Fintype.card M : ℝ)⁻¹ *
    ∑ secret, val (K omega secret) (fun g => dec omega g secret) m [])) ≤
    (Kc : ℝ) ^ m / (Fintype.card M : ℝ)

def BackAt (Kc m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ)
    (dec : Ω → List (Fin Kc) → M → ℝ) : Prop := BackHyp Kc m Ω M Y rho K dec → BackConclusion Kc m Ω M Y rho K dec

def OrigAt (Kc m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ)
    (dec : Ω → List (Fin Kc) → M → ℝ) : Prop := OrigHyp Kc m Ω M Y rho K dec → OrigConclusion Kc m Ω M Y rho K dec

def ComponentwiseClaim : Prop :=
  ∀ (Kc m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ)
    (dec : Ω → List (Fin Kc) → M → ℝ), (BackHyp Kc m Ω M Y rho K dec ↔ OrigHyp Kc m Ω M Y rho K dec) ∧ (BackConclusion Kc m Ω M Y rho K dec ↔ OrigConclusion Kc m Ω M Y rho K dec)

def Witness : Prop :=
  ∃ (rho : Unit → ℝ) (K : Unit → Fin 4 → List (Unit × Fin 2) → Unit × Fin 2 → ℝ)
    (dec : Unit → List (Fin 2) → Fin 4 → ℝ),
    BackHyp 2 2 Unit (Fin 4) Unit rho K dec

def Original : Prop :=
  ∀  {Ω M Y : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] (Kc m : ℕ)
    (ρ : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ) (dec : Ω → List (Fin Kc) → M → ℝ)
    (hρ : IsDist ρ) (hK0 : ∀ ω x h z, 0 ≤ K ω x h z) (hK1 : ∀ ω x h, ∑ z, K ω x h z ≤ 1)
    (hdec : ∀ ω t, IsDist (dec ω t)),
    ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ x, val (K ω x) (fun t => dec ω t x) m [])
      ≤ (Kc : ℝ) ^ m / (Fintype.card M : ℝ)

def BackSchema : Prop := ∀ (Kc m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ)
    (dec : Ω → List (Fin Kc) → M → ℝ), BackAt Kc m Ω M Y rho K dec

def OrigSchema : Prop := ∀ (Kc m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ)
    (dec : Ω → List (Fin Kc) → M → ℝ), OrigAt Kc m Ω M Y rho K dec

def PointwiseClaim : Prop :=
  ComponentwiseClaim ∧ ∀ (Kc m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ)
    (dec : Ω → List (Fin Kc) → M → ℝ), BackAt Kc m Ω M Y rho K dec ↔ OrigAt Kc m Ω M Y rho K dec

def Claim : Prop :=
  (FrozenBack ↔ BackSchema) ∧ (Original ↔ OrigSchema) ∧ PointwiseClaim

end PL_bg1n2_7
