import ControlStack.Scenarios.SC27ExtensionOnly

namespace ControlStack.SC27ExtensionOnly

def Back_anchors_chain : Prop :=
  ∀ (E : Env) (ops : List Op),
    let final := run E true init ops
    final.anchors.Pairwise (fun a b => a.2 <+: b.2) ∧
    (∀ a ∈ final.anchors,
      ∃ latest, final.last = some latest ∧ a.2 <+: latest)

end ControlStack.SC27ExtensionOnly
