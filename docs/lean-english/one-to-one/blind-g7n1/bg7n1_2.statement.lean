namespace PL_bg7n1_2
open ControlStack.SC27Chain

open ControlStack.SC27Chain (chainHead)

def FrozenBack : Prop :=
  ∀ (E : Env) (ops : List Op),
    let final := run E full init ops
    Set.InjOn (chainHead E.H E.h0)
      {l | l ∈ final.accepted ∨ ∃ a ∈ final.anchors, a.2 = some l} →
    ∀ m ∈ final.accepted, ∃ a ∈ final.anchors, a.2 = some m

def BackAt (E : Env) (ops : List Op) : Prop :=
  let final := run E full init ops
  ∀ m ∈ final.accepted, ∃ a ∈ final.anchors, a.2 = some m

def OrigAt (E : Env) (ops : List Op) : Prop :=
  ∀ m ∈ (run E full init ops).accepted, ∃ a ∈ (run E full init ops).anchors, a.2 = some m

def Claim : Prop :=
  (FrozenBack ↔ (∀ (E : Env) (ops : List Op), Set.InjOn (chainHead E.H E.h0) {l | l ∈ (run E full init ops).accepted ∨ ∃ a ∈ (run E full init ops).anchors, a.2 = some l} → BackAt E ops)) ∧
  (∀ (E : Env) (ops : List Op), Set.InjOn (chainHead E.H E.h0) {l | l ∈ (run E full init ops).accepted ∨ ∃ a ∈ (run E full init ops).anchors, a.2 = some l} → (BackAt E ops ↔ OrigAt E ops))

def Witness : Prop :=
  let t := run E0 full init [.append 5, .anchor, .verify [5]]
  t.accepted = [[5]] ∧ t.anchors = [(6, some [5])] ∧
  Set.InjOn (chainHead E0.H E0.h0) {l | l ∈ t.accepted ∨ ∃ a ∈ t.anchors, a.2 = some l} ∧
  (run E0 full init [.append 5, .rewrite [7], .anchor, .verify [7]]).accepted = [[7]] ∧
  (run E0 full init [.append 5, .anchor, .append 6, .anchor, .verify [5]]).accepted = [[5]]

end PL_bg7n1_2
