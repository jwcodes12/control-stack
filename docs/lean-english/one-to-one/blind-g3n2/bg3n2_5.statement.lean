namespace PL_bg3n2_5
open ControlStack.SC17 ControlStack

def BackClosed : Prop :=
  ∀ (E : Env) (s : St),
    s.halted = false →
      (step E full s Op.reconcile).live =
        (step E full s Op.reconcile).desired

def BackAt (E : Env) (s : St) : Prop :=
  (step E full s Op.reconcile).live = (step E full s Op.reconcile).desired
def OrigAt (E : Env) (s : St) : Prop :=
  (step E full s .reconcile).live = (step E full s .reconcile).desired

def OrigClosed : Prop := ∀ E s, s.halted = false → OrigAt E s
def OriginalDeclaration : OrigClosed := @ControlStack.SC17.reconcile_restores

def Claim : Prop :=
  (BackClosed ↔ ∀ E s, s.halted = false → BackAt E s) ∧
  (∀ E s, s.halted = false → (BackAt E s ↔ OrigAt E s))

def Witness : Prop :=
  let s := { init [] with live := [(7, 7, 7)] }
  s.halted = false ∧ s.live ≠ s.desired ∧ BackAt E0 s

end PL_bg3n2_5
