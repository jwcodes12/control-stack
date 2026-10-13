open scoped BigOperators
open ControlStack Finset
open ControlStack.Covert ControlStack.Leakage
open ControlStack.Covert
namespace PL_bg1n2_3

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

def FrozenBack : Prop :=
  ∀ (E : ℕ) (Ω M : Type) (V : Fin E → Type)
      [Fintype Ω] [Fintype M] [Nonempty M] [∀ e, Fintype (V e)]
      (rho : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ)
      (dec : Ω → ((e : Fin E) → V e) → M → ℝ),
    IsDist rho →
    (∀ omega m, IsDist (enc omega m)) →
    (∀ omega v, IsDist (dec omega v)) →
    successProb rho enc dec ≤
      (∏ e : Fin E, (Fintype.card (V e) : ℝ)) / (Fintype.card M : ℝ)


noncomputable def delta {A : Type} [Fintype A] [DecidableEq A] (a : A) : A → ℝ :=
  fun x => if x = a then 1 else 0


def BackHyp (E : ℕ) (Ω M : Type) (V : Fin E → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [∀ e, Fintype (V e)]
    (rho : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ)
    (dec : Ω → ((e : Fin E) → V e) → M → ℝ) : Prop :=
  IsDist rho ∧ (∀ omega m, IsDist (enc omega m)) ∧ (∀ omega v, IsDist (dec omega v))

def OrigHyp (E : ℕ) (Ω M : Type) (V : Fin E → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [∀ e, Fintype (V e)]
    (rho : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ)
    (dec : Ω → ((e : Fin E) → V e) → M → ℝ) : Prop :=
  IsDist rho ∧ (∀ omega m, IsDist (enc omega m)) ∧ (∀ omega v, IsDist (dec omega v))

def BackConclusion (E : ℕ) (Ω M : Type) (V : Fin E → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [∀ e, Fintype (V e)]
    (rho : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ)
    (dec : Ω → ((e : Fin E) → V e) → M → ℝ) : Prop :=
  successProb rho enc dec ≤ (∏ e : Fin E, (Fintype.card (V e) : ℝ)) / (Fintype.card M : ℝ)

def OrigConclusion (E : ℕ) (Ω M : Type) (V : Fin E → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [∀ e, Fintype (V e)]
    (rho : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ)
    (dec : Ω → ((e : Fin E) → V e) → M → ℝ) : Prop :=
  successProb rho enc dec ≤ (∏ e : Fin E, (Fintype.card (V e) : ℝ)) / (Fintype.card M : ℝ)

def BackAt (E : ℕ) (Ω M : Type) (V : Fin E → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [∀ e, Fintype (V e)]
    (rho : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ)
    (dec : Ω → ((e : Fin E) → V e) → M → ℝ) : Prop := BackHyp E Ω M V rho enc dec → BackConclusion E Ω M V rho enc dec

def OrigAt (E : ℕ) (Ω M : Type) (V : Fin E → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [∀ e, Fintype (V e)]
    (rho : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ)
    (dec : Ω → ((e : Fin E) → V e) → M → ℝ) : Prop := OrigHyp E Ω M V rho enc dec → OrigConclusion E Ω M V rho enc dec

def ComponentwiseClaim : Prop :=
  ∀ (E : ℕ) (Ω M : Type) (V : Fin E → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [∀ e, Fintype (V e)]
    (rho : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ)
    (dec : Ω → ((e : Fin E) → V e) → M → ℝ), (BackHyp E Ω M V rho enc dec ↔ OrigHyp E Ω M V rho enc dec) ∧ (BackConclusion E Ω M V rho enc dec ↔ OrigConclusion E Ω M V rho enc dec)

def Witness : Prop :=
  ∃ (rho : Unit → ℝ) (enc : Unit → Fin 4 → (Fin 2 → Fin 2) → ℝ)
    (dec : Unit → (Fin 2 → Fin 2) → Fin 4 → ℝ),
    BackHyp 2 Unit (Fin 4) (fun _ => Fin 2) rho enc dec

def Original : Prop :=
  ∀  {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] {E : ℕ}
    (V : Fin E → Type) [∀ e, Fintype (V e)] [∀ e, DecidableEq (V e)]
    (ρ : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ) (dec : Ω → ((e : Fin E) → V e) → M → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)),
    successProb ρ enc dec ≤ (∏ e, (Fintype.card (V e) : ℝ)) / (Fintype.card M : ℝ)

def BackSchema : Prop := ∀ (E : ℕ) (Ω M : Type) (V : Fin E → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [∀ e, Fintype (V e)]
    (rho : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ)
    (dec : Ω → ((e : Fin E) → V e) → M → ℝ), BackAt E Ω M V rho enc dec

def OrigSchema : Prop := ∀ (E : ℕ) (Ω M : Type) (V : Fin E → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [∀ e, Fintype (V e)]
    (rho : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ)
    (dec : Ω → ((e : Fin E) → V e) → M → ℝ), OrigAt E Ω M V rho enc dec

def PointwiseClaim : Prop :=
  ComponentwiseClaim ∧ ∀ (E : ℕ) (Ω M : Type) (V : Fin E → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [∀ e, Fintype (V e)]
    (rho : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ)
    (dec : Ω → ((e : Fin E) → V e) → M → ℝ), BackAt E Ω M V rho enc dec ↔ OrigAt E Ω M V rho enc dec

def Claim : Prop :=
  (FrozenBack ↔ BackSchema) ∧ (Original ↔ OrigSchema) ∧ PointwiseClaim

end PL_bg1n2_3
