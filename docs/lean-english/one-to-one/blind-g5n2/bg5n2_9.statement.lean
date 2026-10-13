namespace PL_bg5n2_9
open Finset ControlStack.MonitorCollusion ControlStack.Covert ControlStack.Leakage
def Back_pass_transfer : Prop :=
  ∀ (V : Type) [Fintype V] (P Q β : V → ℝ),
    IsDist P → IsDist Q →
      (∀ v, 0 ≤ β v ∧ β v ≤ 1) →
        |passRate P β - passRate Q β| ≤ tv P Q

def Claim : Prop :=
  (Back_pass_transfer = (∀ (V : Type) [Fintype V] (P Q β : V → ℝ),
    IsDist P → IsDist Q → (∀ v, 0 ≤ β v ∧ β v ≤ 1) →
      |passRate P β - passRate Q β| ≤ tv P Q)) ∧
  (∀ (V : Type) [Fintype V] (P Q β : V → ℝ),
    IsDist P → IsDist Q → (∀ v, 0 ≤ β v ∧ β v ≤ 1) →
      (|passRate P β - passRate Q β| ≤ tv P Q ↔
       |passRate Q β - passRate P β| ≤ tv P Q))
def Witness : Prop :=
  IsDist stegoReal ∧ IsDist stegoHoney ∧
  (∀ v, 0 ≤ stegoMonitor v ∧ stegoMonitor v ≤ 1) ∧
  passRate stegoReal stegoMonitor = 1 ∧ passRate stegoHoney stegoMonitor = 0 ∧ tv stegoReal stegoHoney = 1
end PL_bg5n2_9
