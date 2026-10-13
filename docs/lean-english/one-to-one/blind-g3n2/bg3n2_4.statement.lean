namespace PL_bg3n2_4
open ControlStack.SC17 ControlStack

def BackClosed : Prop :=
  ∀ (E : Env) (g0 : List G) (ops : List Op),
    Good E (run E full (init g0) ops)

def BackAt (E : Env) (g0 : List G) (ops : List Op) : Prop :=
  Good E (run E full (init g0) ops)
def OrigAt (E : Env) (g0 : List G) (ops : List Op) : Prop :=
  Good E (run E full (init g0) ops)

def OrigClosed : Prop := ∀ E g0 ops, OrigAt E g0 ops
def OriginalDeclaration : OrigClosed := @ControlStack.SC17.sc17_safe

def Claim : Prop :=
  (BackClosed ↔ ∀ E g0 ops, BackAt E g0 ops) ∧
  (∀ E g0 ops, BackAt E g0 ops ↔ OrigAt E g0 ops)

def Witness : Prop :=
  (run E0 full (init []) [.propose 1 0 dA, .approve 2 0, .apply 0]).applied.map AppRec.id = [0] ∧
  OrigAt E0 [] [.propose 1 0 dA, .approve 2 0, .apply 0]

end PL_bg3n2_4
