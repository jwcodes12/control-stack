namespace PL_bg7n1_6
open ControlStack.SC27ExtensionOnly


def FrozenBack : Prop :=
  ∀ (E : Env) (s : St) (l : List ℕ) (ops : List Op),
    Inv E s →
    (∃ a ∈ s.anchors, a.2 = l) →
    ∀ a ∈ (run E true s ops).anchors,
      a ∈ s.anchors ∨ l <+: a.2

def BackAt (E : Env) (s : St) (l : List ℕ) (ops : List Op) : Prop :=
  ∀ a ∈ (run E true s ops).anchors, a ∈ s.anchors ∨ l <+: a.2

def OrigAt (E : Env) (s : St) (l : List ℕ) (ops : List Op) : Prop :=
  ∀ a ∈ (run E true s ops).anchors, a ∈ s.anchors ∨ l <+: a.2

def Claim : Prop :=
  (FrozenBack ↔ (∀ (E : Env) (s : St) (l : List ℕ) (ops : List Op), Inv E s → (∃ a ∈ s.anchors, a.2 = l) → BackAt E s l ops)) ∧
  (∀ (E : Env) (s : St) (l : List ℕ) (ops : List Op), Inv E s → (∃ a ∈ s.anchors, a.2 = l) → (BackAt E s l ops ↔ OrigAt E s l ops))

def Witness : Prop :=
  let s := run E0 true init [.append 5, .anchor]
  Inv E0 s ∧ (∃ a ∈ s.anchors, a.2 = [5]) ∧
  (run E0 true s [.append 6, .anchor]).anchors = [(6, [5]), (607, [5, 6])]

end PL_bg7n1_6
