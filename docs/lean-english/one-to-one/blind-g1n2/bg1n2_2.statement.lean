open scoped BigOperators
open ControlStack Finset
open ControlStack.Covert ControlStack.Leakage
open ControlStack.GatewayCore
namespace PL_bg1n2_2

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

def FrozenBack : Prop :=
  ∀ (C L : ℕ) (Ω M R : Type) (S : Fin C → Type)
      [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R]
      [∀ c, Fintype (S c)] [Fintype (Ev C R)]
      (slots : Fin C → ℕ) (valid : (c : Fin C) → R → Option (S c))
      (rho : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ)
      (dec : Ω → View S slots → M → ℝ),
    ControlStack.Covert.IsDist rho →
    (∀ omega m, ControlStack.Covert.IsDist (enc omega m)) →
    (∀ omega v, ControlStack.Covert.IsDist (dec omega v)) →
    ControlStack.Covert.successProb rho
      (fun omega m => ControlStack.GatewayModel.push
        (fun tr : Fin L → Ev C R =>
          finalView (runG valid (init (S := S) (slots := slots)) (List.ofFn tr)))
        (enc omega m)) dec ≤
      (viewSpace slots (fun c => Fintype.card (S c)) : ℝ) / (Fintype.card M : ℝ)


noncomputable def delta {A : Type} [Fintype A] [DecidableEq A] (a : A) : A → ℝ :=
  fun x => if x = a then 1 else 0


def BackHyp (C L : ℕ) (Ω M R : Type) (S : Fin C → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R]
    [∀ c, Fintype (S c)] [Fintype (Ev C R)]
    (slots : Fin C → ℕ) (valid : (c : Fin C) → R → Option (S c))
    (rho : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ)
    (dec : Ω → View S slots → M → ℝ) : Prop :=
  IsDist rho ∧ (∀ omega m, IsDist (enc omega m)) ∧ (∀ omega v, IsDist (dec omega v))

def OrigHyp (C L : ℕ) (Ω M R : Type) (S : Fin C → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R]
    [∀ c, Fintype (S c)] [Fintype (Ev C R)]
    (slots : Fin C → ℕ) (valid : (c : Fin C) → R → Option (S c))
    (rho : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ)
    (dec : Ω → View S slots → M → ℝ) : Prop :=
  IsDist rho ∧ (∀ omega m, IsDist (enc omega m)) ∧ (∀ omega v, IsDist (dec omega v))

def BackConclusion (C L : ℕ) (Ω M R : Type) (S : Fin C → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R]
    [∀ c, Fintype (S c)] [Fintype (Ev C R)]
    (slots : Fin C → ℕ) (valid : (c : Fin C) → R → Option (S c))
    (rho : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ)
    (dec : Ω → View S slots → M → ℝ) : Prop :=
  successProb rho
    (fun omega m => ControlStack.GatewayModel.push
      (fun tr : Fin L → Ev C R => finalView (runG valid (init (S := S) (slots := slots)) (List.ofFn tr)))
      (enc omega m)) dec ≤
    (viewSpace slots (fun c => Fintype.card (S c)) : ℝ) / (Fintype.card M : ℝ)

def OrigConclusion (C L : ℕ) (Ω M R : Type) (S : Fin C → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R]
    [∀ c, Fintype (S c)] [Fintype (Ev C R)]
    (slots : Fin C → ℕ) (valid : (c : Fin C) → R → Option (S c))
    (rho : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ)
    (dec : Ω → View S slots → M → ℝ) : Prop :=
  (∑ omega, rho omega * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ tr, enc omega m tr *
    dec omega (finalView (runG valid (init (S := S) (slots := slots)) (List.ofFn tr))) m)) ≤
    (viewSpace slots (fun c => Fintype.card (S c)) : ℝ) / (Fintype.card M : ℝ)

def BackAt (C L : ℕ) (Ω M R : Type) (S : Fin C → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R]
    [∀ c, Fintype (S c)] [Fintype (Ev C R)]
    (slots : Fin C → ℕ) (valid : (c : Fin C) → R → Option (S c))
    (rho : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ)
    (dec : Ω → View S slots → M → ℝ) : Prop := BackHyp C L Ω M R S slots valid rho enc dec → BackConclusion C L Ω M R S slots valid rho enc dec

def OrigAt (C L : ℕ) (Ω M R : Type) (S : Fin C → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R]
    [∀ c, Fintype (S c)] [Fintype (Ev C R)]
    (slots : Fin C → ℕ) (valid : (c : Fin C) → R → Option (S c))
    (rho : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ)
    (dec : Ω → View S slots → M → ℝ) : Prop := OrigHyp C L Ω M R S slots valid rho enc dec → OrigConclusion C L Ω M R S slots valid rho enc dec

def ComponentwiseClaim : Prop :=
  ∀ (C L : ℕ) (Ω M R : Type) (S : Fin C → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R]
    [∀ c, Fintype (S c)] [Fintype (Ev C R)]
    (slots : Fin C → ℕ) (valid : (c : Fin C) → R → Option (S c))
    (rho : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ)
    (dec : Ω → View S slots → M → ℝ), (BackHyp C L Ω M R S slots valid rho enc dec ↔ OrigHyp C L Ω M R S slots valid rho enc dec) ∧ (BackConclusion C L Ω M R S slots valid rho enc dec ↔ OrigConclusion C L Ω M R S slots valid rho enc dec)

def Witness : Prop :=
  ∃ (inst : Fintype (Ev 1 Unit)),
    letI := inst
    ∃ (rho : Unit → ℝ) (enc : Unit → Fin 2 → (Fin 1 → Ev 1 Unit) → ℝ)
      (dec : Unit → View (fun _ : Fin 1 => Bool) (fun _ => 1) → Fin 2 → ℝ),
      BackHyp 1 1 Unit (Fin 2) Unit (fun _ => Bool) (fun _ => 1)
        (fun _ _ => some false) rho enc dec

def Original : Prop :=
  ∀ {C : ℕ} {R : Type} {S : Fin C → Type} {slots : Fin C → ℕ} {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R]
    [∀ c, Fintype (S c)] [∀ c, DecidableEq (S c)]
    [Fintype (Ev C R)] (valid : (c : Fin C) → R → Option (S c)) (L : ℕ)
    (ρ : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ) (dec : Ω → View S slots → M → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)),
    (∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ tr, enc ω m tr *
        dec ω (finalView (runG valid (init (S := S) (slots := slots)) (List.ofFn tr))) m))
      ≤ (viewSpace slots (fun c => Fintype.card (S c)) : ℝ) / (Fintype.card M : ℝ)

def BackSchema : Prop := ∀ (C L : ℕ) (Ω M R : Type) (S : Fin C → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R]
    [∀ c, Fintype (S c)] [Fintype (Ev C R)]
    (slots : Fin C → ℕ) (valid : (c : Fin C) → R → Option (S c))
    (rho : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ)
    (dec : Ω → View S slots → M → ℝ), BackAt C L Ω M R S slots valid rho enc dec

def OrigSchema : Prop := ∀ (C L : ℕ) (Ω M R : Type) (S : Fin C → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R]
    [∀ c, Fintype (S c)] [Fintype (Ev C R)]
    (slots : Fin C → ℕ) (valid : (c : Fin C) → R → Option (S c))
    (rho : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ)
    (dec : Ω → View S slots → M → ℝ), OrigAt C L Ω M R S slots valid rho enc dec

def PointwiseClaim : Prop :=
  ComponentwiseClaim ∧ ∀ (C L : ℕ) (Ω M R : Type) (S : Fin C → Type)
    [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R]
    [∀ c, Fintype (S c)] [Fintype (Ev C R)]
    (slots : Fin C → ℕ) (valid : (c : Fin C) → R → Option (S c))
    (rho : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ)
    (dec : Ω → View S slots → M → ℝ), BackAt C L Ω M R S slots valid rho enc dec ↔ OrigAt C L Ω M R S slots valid rho enc dec

def Claim : Prop :=
  (FrozenBack ↔ BackSchema) ∧ (Original ↔ OrigSchema) ∧ PointwiseClaim

end PL_bg1n2_2
