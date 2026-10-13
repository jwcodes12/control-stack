namespace PL_bg1a_4
open ControlStack.SC05

def Back_zero_dependence_is_blind : Prop :=
  ∀ (Ω M V : Type) [Fintype Ω] [Fintype M] [Fintype V]
    (ρ : Ω → ℝ) (out : Ω → V → ℝ) (dec : Ω → V → M → ℝ),
    ControlStack.Covert.IsDist ρ →
    (∀ ω, ControlStack.Covert.IsDist (out ω)) →
    (∀ ω v, ControlStack.Covert.IsDist (dec ω v)) →
    ControlStack.Covert.successProb ρ (fun ω _m v => out ω v) dec =
      (Fintype.card M : ℝ)⁻¹


def BackAt (Ω M V : Type) [Fintype Ω] [Fintype M] [Fintype V] (ρ : Ω → ℝ) (out : Ω → V → ℝ) (dec : Ω → V → M → ℝ) : Prop :=
  ControlStack.Covert.successProb ρ (fun ω _m v => out ω v) dec = (Fintype.card M : ℝ)⁻¹
def OrigAt (Ω M V : Type) [Fintype Ω] [Fintype M] [Fintype V] (ρ : Ω → ℝ) (out : Ω → V → ℝ) (dec : Ω → V → M → ℝ) : Prop :=
  ControlStack.Covert.successProb ρ (fun ω _m v => out ω v) dec = (Fintype.card M : ℝ)⁻¹

def Claim : Prop :=
  (Back_zero_dependence_is_blind = (∀ (Ω M V : Type) [Fintype Ω] [Fintype M] [Fintype V] (ρ : Ω → ℝ) (out : Ω → V → ℝ) (dec : Ω → V → M → ℝ) (_hρ : ControlStack.Covert.IsDist ρ) (_ho : ∀ ω, ControlStack.Covert.IsDist (out ω)) (_hd : ∀ ω v, ControlStack.Covert.IsDist (dec ω v)), BackAt Ω M V ρ out dec)) ∧
  (∀ (Ω M V : Type) [Fintype Ω] [Fintype M] [Fintype V] (ρ : Ω → ℝ) (out : Ω → V → ℝ) (dec : Ω → V → M → ℝ) (_hρ : ControlStack.Covert.IsDist ρ) (_ho : ∀ ω, ControlStack.Covert.IsDist (out ω)) (_hd : ∀ ω v, ControlStack.Covert.IsDist (dec ω v)), BackAt Ω M V ρ out dec ↔ OrigAt Ω M V ρ out dec)

def Witness : Prop :=
  ControlStack.Covert.IsDist (fun _ : Unit => (1 : ℝ)) ∧
  (∀ _ω : Unit, ControlStack.Covert.IsDist (fun _ : Bool => (1 : ℝ) / 2)) ∧
  (∀ (_ω : Unit) (_v : Bool), ControlStack.Covert.IsDist (fun _ : Bool => (1 : ℝ) / 2)) ∧
  ControlStack.Covert.successProb (fun _ : Unit => (1 : ℝ))
    (fun (_ : Unit) (_ : Bool) (_ : Bool) => (1 : ℝ) / 2)
    (fun (_ : Unit) (_ : Bool) (_ : Bool) => (1 : ℝ) / 2) = (1 : ℝ) / 2
end PL_bg1a_4
