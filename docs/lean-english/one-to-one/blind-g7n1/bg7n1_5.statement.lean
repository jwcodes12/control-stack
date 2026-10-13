namespace PL_bg7n1_5
open ControlStack.SC27ExtensionOnly
open ControlStack.SC27Chain (chainHead)

def FrozenBack : Prop :=
  ∀ (E : Env) (ops : List Op),
    let final := run E true init ops
    Set.InjOn (chainHead E.H E.h0)
      {l | l ∈ final.accepted ∨ ∃ a ∈ final.anchors, a.2 = l} →
    ∀ m ∈ final.accepted,
      (∃ a ∈ final.anchors, a.2 = m) ∧
      (∃ latest, final.last = some latest ∧ m <+: latest)

def BackAt (E : Env) (ops : List Op) : Prop :=
  let final := run E true init ops
  ∀ m ∈ final.accepted, (∃ a ∈ final.anchors, a.2 = m) ∧
    (∃ latest, final.last = some latest ∧ m <+: latest)

def OrigAt (E : Env) (ops : List Op) : Prop :=
  ∀ m ∈ (run E true init ops).accepted,
  (∃ a ∈ (run E true init ops).anchors, a.2 = m) ∧
    ∃ l, (run E true init ops).last = some l ∧ m <+: l

def Claim : Prop :=
  (FrozenBack ↔ (∀ (E : Env) (ops : List Op), Set.InjOn (chainHead E.H E.h0) {l | l ∈ (run E true init ops).accepted ∨ ∃ a ∈ (run E true init ops).anchors, a.2 = l} → BackAt E ops)) ∧
  (∀ (E : Env) (ops : List Op), Set.InjOn (chainHead E.H E.h0) {l | l ∈ (run E true init ops).accepted ∨ ∃ a ∈ (run E true init ops).anchors, a.2 = l} → (BackAt E ops ↔ OrigAt E ops))

def Witness : Prop :=
  let t := run E0 true init [.append 5, .anchor, .verify [5]]
  t.accepted = [[5]] ∧ t.anchors = [(6, [5])] ∧ t.last = some [5] ∧
  Set.InjOn (chainHead E0.H E0.h0) {l | l ∈ t.accepted ∨ ∃ a ∈ t.anchors, a.2 = l} ∧
  (let u := run E0 true init [.append 5, .anchor, .append 6, .anchor, .verify [5]]
   u.accepted = [[5]] ∧ u.last = some [5, 6])

end PL_bg7n1_5
