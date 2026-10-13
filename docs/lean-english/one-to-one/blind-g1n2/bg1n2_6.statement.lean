open scoped BigOperators
open ControlStack Finset
open ControlStack.Covert ControlStack.Leakage
open ControlStack.ChannelInstances
namespace PL_bg1n2_6

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

def FrozenBack : Prop :=
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


noncomputable def delta {A : Type} [Fintype A] [DecidableEq A] (a : A) : A → ℝ :=
  fun x => if x = a then 1 else 0


def BackHyp (Kt Q f m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) → Y × (Fin Kt × (Fin f → Fin Q)) → ℝ)
    (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ) : Prop :=
  IsDist rho ∧ (∀ omega g, IsDist (dec omega g)) ∧ (∀ omega secret h z, 0 ≤ K omega secret h z) ∧
    (∀ omega secret h, (∑ y, ∑ o, K omega secret h (y, o)) ≤ 1)

def OrigHyp (Kt Q f m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) → Y × (Fin Kt × (Fin f → Fin Q)) → ℝ)
    (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ) : Prop :=
  IsDist rho ∧ (∀ omega g, IsDist (dec omega g)) ∧ (∀ omega secret h z, 0 ≤ K omega secret h z) ∧
    (∀ omega secret h, (∑ z, K omega secret h z) ≤ 1)

def BackConclusion (Kt Q f m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) → Y × (Fin Kt × (Fin f → Fin Q)) → ℝ)
    (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ) : Prop :=
  (∑ omega, rho omega * ((Fintype.card M : ℝ)⁻¹ *
    ∑ secret, val (K omega secret) (fun g => dec omega g secret) m [])) ≤
    (Kt : ℝ) ^ m * (Q : ℝ) ^ (f * m) / (Fintype.card M : ℝ)

def OrigConclusion (Kt Q f m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) → Y × (Fin Kt × (Fin f → Fin Q)) → ℝ)
    (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ) : Prop :=
  (∑ omega, rho omega * ((Fintype.card M : ℝ)⁻¹ *
    ∑ secret, val (K omega secret) (fun g => dec omega g secret) m [])) ≤
    (Kt : ℝ) ^ m * (Q : ℝ) ^ (f * m) / (Fintype.card M : ℝ)

def BackAt (Kt Q f m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) → Y × (Fin Kt × (Fin f → Fin Q)) → ℝ)
    (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ) : Prop := BackHyp Kt Q f m Ω M Y rho K dec → BackConclusion Kt Q f m Ω M Y rho K dec

def OrigAt (Kt Q f m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) → Y × (Fin Kt × (Fin f → Fin Q)) → ℝ)
    (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ) : Prop := OrigHyp Kt Q f m Ω M Y rho K dec → OrigConclusion Kt Q f m Ω M Y rho K dec

def ComponentwiseClaim : Prop :=
  ∀ (Kt Q f m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) → Y × (Fin Kt × (Fin f → Fin Q)) → ℝ)
    (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ), (BackHyp Kt Q f m Ω M Y rho K dec ↔ OrigHyp Kt Q f m Ω M Y rho K dec) ∧ (BackConclusion Kt Q f m Ω M Y rho K dec ↔ OrigConclusion Kt Q f m Ω M Y rho K dec)

def Witness : Prop :=
  ∃ (rho : Unit → ℝ) (K : Unit → Fin 4 → List (Unit × (Fin 2 × (Fin 1 → Fin 2))) → Unit × (Fin 2 × (Fin 1 → Fin 2)) → ℝ)
    (dec : Unit → List (Fin 2 × (Fin 1 → Fin 2)) → Fin 4 → ℝ),
    BackHyp 2 2 1 2 Unit (Fin 4) Unit rho K dec

def Original : Prop :=
  ∀  {Ω M Y : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] (Kt f Q m : ℕ)
    (ρ : Ω → ℝ) (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) → Y × (Fin Kt × (Fin f → Fin Q)) → ℝ)
    (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ)
    (hρ : IsDist ρ) (hK0 : ∀ ω x h z, 0 ≤ K ω x h z) (hK1 : ∀ ω x h, ∑ z, K ω x h z ≤ 1)
    (hdec : ∀ ω t, IsDist (dec ω t)),
    ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ x, val (K ω x) (fun t => dec ω t x) m [])
      ≤ (Kt : ℝ) ^ m * (Q : ℝ) ^ (f * m) / (Fintype.card M : ℝ)

def BackSchema : Prop := ∀ (Kt Q f m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) → Y × (Fin Kt × (Fin f → Fin Q)) → ℝ)
    (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ), BackAt Kt Q f m Ω M Y rho K dec

def OrigSchema : Prop := ∀ (Kt Q f m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) → Y × (Fin Kt × (Fin f → Fin Q)) → ℝ)
    (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ), OrigAt Kt Q f m Ω M Y rho K dec

def PointwiseClaim : Prop :=
  ComponentwiseClaim ∧ ∀ (Kt Q f m : ℕ) (Ω M Y : Type) [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y]
    (rho : Ω → ℝ) (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) → Y × (Fin Kt × (Fin f → Fin Q)) → ℝ)
    (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ), BackAt Kt Q f m Ω M Y rho K dec ↔ OrigAt Kt Q f m Ω M Y rho K dec

def Claim : Prop :=
  (FrozenBack ↔ BackSchema) ∧ (Original ↔ OrigSchema) ∧ PointwiseClaim

end PL_bg1n2_6
