import ControlStack.Scenarios.SC27ExtensionOnly

namespace ControlStack.SC27ExtensionOnly

def Back_tampered_never_anchored : Prop :=
  ∀ (E : Env) (s : St) (l : List ℕ) (ops : List Op),
    Inv E s →
    (∃ a ∈ s.anchors, a.2 = l) →
    ∀ a ∈ (run E true s ops).anchors,
      a ∈ s.anchors ∨ l <+: a.2

end ControlStack.SC27ExtensionOnly
