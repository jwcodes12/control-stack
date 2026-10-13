namespace PL_bg3n2_6
open ControlStack.SC17 ControlStack

def BackClosed : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true → (run E full s ops).applied = s.applied

def BackAt (E : Env) (s : St) (ops : List Op) : Prop :=
  (run E full s ops).applied = s.applied
def OrigAt (E : Env) (s : St) (ops : List Op) : Prop :=
  (run E full s ops).applied = s.applied

def OrigClosed : Prop := ∀ E s ops, s.halted = true → OrigAt E s ops
def OriginalDeclaration : OrigClosed := @ControlStack.SC17.halt_freezes

def Claim : Prop :=
  (BackClosed ↔ ∀ E s ops, s.halted = true → BackAt E s ops) ∧
  (∀ E s ops, s.halted = true → (BackAt E s ops ↔ OrigAt E s ops))

def Witness : Prop :=
  let s := run E0 full (init []) [.propose 1 0 dA, .approve 2 0, .apply 0, .halt 9]
  s.halted = true ∧ s.applied ≠ [] ∧
  (run E0 full s [.oob (7, 7, 7), .apply 0]).live ≠ s.live ∧
  BackAt E0 s [.oob (7, 7, 7), .apply 0]

end PL_bg3n2_6
