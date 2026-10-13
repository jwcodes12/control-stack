namespace PL_bg7n1_7
open ControlStack.SC27ExtensionOnly


def FrozenBack : Prop :=
  ∀ (E : Env) (ops : List Op),
    let final := run E true init ops
    final.anchors.Pairwise (fun a b => a.2 <+: b.2) ∧
    (∀ a ∈ final.anchors,
      ∃ latest, final.last = some latest ∧ a.2 <+: latest)

def BackAt (E : Env) (ops : List Op) : Prop :=
  let final := run E true init ops
  final.anchors.Pairwise (fun a b => a.2 <+: b.2) ∧
  (∀ a ∈ final.anchors, ∃ latest, final.last = some latest ∧ a.2 <+: latest)

def OrigAt (E : Env) (ops : List Op) : Prop :=
  (run E true init ops).anchors.Pairwise (fun a b => a.2 <+: b.2) ∧
  ∀ a ∈ (run E true init ops).anchors, ∃ l, (run E true init ops).last = some l ∧ a.2 <+: l

def Claim : Prop :=
  (FrozenBack ↔ (∀ (E : Env) (ops : List Op), BackAt E ops)) ∧
  (∀ (E : Env) (ops : List Op), (BackAt E ops ↔ OrigAt E ops))

def Witness : Prop :=
  let t := run E0 true init [.append 5, .anchor, .append 6, .anchor]
  t.anchors = [(6, [5]), (607, [5, 6])] ∧ t.last = some [5, 6]

end PL_bg7n1_7
