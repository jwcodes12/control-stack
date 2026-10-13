namespace PL_bg5n2_11
open Finset ControlStack.MonitorCollusion ControlStack.Covert ControlStack.Leakage
def Back_canon_channel : Prop :=
  ∀ (Ω M V : Type) [Fintype Ω] [Fintype M] [Fintype V] [Nonempty M]
    (K : ℕ) (canon : V → Fin K) (ρ : Ω → ℝ)
    (enc : Ω → M → V → ℝ) (dec : Ω → Fin K → M → ℝ),
    IsDist ρ →
      (∀ ω m, IsDist (enc ω m)) →
        (∀ ω k, IsDist (dec ω k)) →
          successProb ρ enc (fun ω v m => dec ω (canon v) m) ≤
            (K : ℝ) / (Fintype.card M : ℝ)

noncomputable def OrigSeed {M V : Type} [Fintype M] [Fintype V] [DecidableEq M]
    (K : ℕ) (canon : V → Fin K) (enc : M → V → ℝ) (dec : Fin K → M → ℝ) : ℝ :=
  ∑ m, (Fintype.card M : ℝ)⁻¹ * ∑ v, enc m v * ∑ a, dec (canon v) a * (if a = m then 1 else 0)
noncomputable def BackSeed {M V : Type} [Fintype M] [Fintype V]
    (K : ℕ) (canon : V → Fin K) (enc : M → V → ℝ) (dec : Fin K → M → ℝ) : ℝ :=
  (Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ v, enc m v * dec (canon v) m
def OriginalFamily : Prop :=
  ∀ (M V : Type) [Fintype M] [Fintype V] [DecidableEq M] [Nonempty M]
    (K : ℕ) (canon : V → Fin K) (enc : M → V → ℝ),
    (∀ m, IsDist (enc m)) → ∀ (dec : Fin K → M → ℝ),
    (∀ k, IsDist (dec k)) →
      OrigSeed K canon enc dec ≤ (K : ℝ) * (Fintype.card M : ℝ)⁻¹
def Claim : Prop :=
  (∀ (M V : Type) [Fintype M] [Fintype V] [DecidableEq M]
    (K : ℕ) (canon : V → Fin K) (enc : M → V → ℝ) (dec : Fin K → M → ℝ),
    (BackSeed K canon enc dec ≤ (K : ℝ)/(Fintype.card M : ℝ) ↔
     OrigSeed K canon enc dec ≤ (K : ℝ)*(Fintype.card M : ℝ)⁻¹)) ∧
  (Back_canon_channel ↔ OriginalFamily)
def Witness : Prop :=
  IsDist (fun _ : Unit => (1:ℝ)) ∧
  (∀ m : Bool, IsDist (fun v : Bool => if v = m then (1:ℝ) else 0)) ∧
  (∀ k : Fin 2, IsDist (fun m : Bool => if m = (k.val == 1) then (1:ℝ) else 0)) ∧
  successProb (fun _ : Unit => (1:ℝ))
    (fun (_ : Unit) (m v : Bool) => if v = m then 1 else 0)
    (fun (_ : Unit) (v m : Bool) => if m = (((if v then 1 else 0 : Fin 2).val) == 1) then 1 else 0) = 1
end PL_bg5n2_11
