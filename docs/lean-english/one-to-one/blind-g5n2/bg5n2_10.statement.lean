namespace PL_bg5n2_10
open Finset ControlStack.MonitorCollusion ControlStack.Covert ControlStack.Leakage
def Back_collusion_uniform : Prop :=
  ∀ (V : Type) [Fintype V] (P Q : V → ℝ) (monitor : V → Bool → ℝ),
    IsDist P → IsDist Q →
      (∀ v, IsDist (monitor v)) →
        (passRate P (fun v => monitor v true) +
          passRate Q (fun v => monitor v false)) / 2 ≤
            (1 + tv P Q) / 2

def Claim : Prop :=
  (Back_collusion_uniform = (∀ (V : Type) [Fintype V] (P Q : V → ℝ) (monitor : V → Bool → ℝ),
    IsDist P → IsDist Q → (∀ v, IsDist (monitor v)) →
      (passRate P (fun v => monitor v true) + passRate Q (fun v => monitor v false))/2 ≤ (1+tv P Q)/2)) ∧
  (∀ (V : Type) [Fintype V] (P Q : V → ℝ) (monitor : V → Bool → ℝ),
    IsDist P → IsDist Q → (∀ v, IsDist (monitor v)) →
    ((passRate P (fun v => monitor v true) + passRate Q (fun v => monitor v false))/2 ≤ (1+tv P Q)/2 ↔
     (∑ φ : Bool, (1/2 : ℝ) * ∑ v, (if φ then P v else Q v) *
       ∑ a : Bool, monitor v a * (if a = φ then 1 else 0)) ≤ (1+tv P Q)/2))
def Witness : Prop :=
  IsDist stegoReal ∧ IsDist stegoHoney ∧
  (∀ v : Bool, IsDist (fun a : Bool => if a = v then (1:ℝ) else 0)) ∧
  (passRate stegoReal (fun v => if true = v then 1 else 0) +
    passRate stegoHoney (fun v => if false = v then 1 else 0))/2 = 1
end PL_bg5n2_10
