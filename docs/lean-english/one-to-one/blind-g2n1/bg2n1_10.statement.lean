namespace PL_bg2n1_10
open ControlStack.SC12

def Back_sc12_safe : Prop :=
  ∀ (admins : List ℕ) (ops : List Op),
    Good (run admins full init ops)

def EnglishOk (s : St) : Prop :=
  ∀ e ∈ s.live, e.reg = true ∧ e.origin ∈ s.active ∧ e.origin ∉ s.ended
def BackAt (admins : List ℕ) (ops : List Op) : Prop := Good (run admins full init ops)
def OrigAt (admins : List ℕ) (ops : List Op) : Prop := Good (run admins full init ops)
def Claim : Prop :=
  (Back_sc12_safe = (∀ admins ops, BackAt admins ops)) ∧
  (∀ admins ops, BackAt admins ops ↔ OrigAt admins ops) ∧
  (∀ s, EnglishOk s ↔ Good s)
def Witness : Prop :=
  init.active = [] ∧ init.ended = [] ∧ init.live = [] ∧ init.fired = [] ∧ init.halted = false ∧
  let s := run [9] full init
    [.start 9 1, .spawn 1 5 true 999, .bypass 1 6 true, .fire 5, .endSession 9 1, .fire 5]
  s.fired = [(5, 1, 0)] ∧ s.live = [] ∧ s.ended = [1]

end PL_bg2n1_10
