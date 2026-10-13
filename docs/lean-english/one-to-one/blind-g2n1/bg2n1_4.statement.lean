namespace PL_bg2n1_4
open ControlStack.SC09

def Back_sc09_safe : Prop :=
  ∀ (P : Policy) (ops : List Op),
    Good P (run P full init ops)

def EnglishOk (P : Policy) (s : St) : Prop :=
  (∀ q ∈ s.procs, ∀ c ∈ q.caps, (q.lin, c) ∈ s.granted) ∧
  (∀ u ∈ s.used, (u.lin, u.cap) ∈ s.granted ∨
    ∃ r ∈ P.elev, u.via = some (r.bin, r.args) ∧ r.cap = u.cap)
def BackAt (P : Policy) (ops : List Op) : Prop := Good P (run P full init ops)
def OrigAt (P : Policy) (ops : List Op) : Prop := Good P (run P full init ops)
def Claim : Prop :=
  (Back_sc09_safe = (∀ P ops, BackAt P ops)) ∧
  (∀ P ops, BackAt P ops ↔ OrigAt P ops) ∧
  (∀ P s, EnglishOk P s ↔ Good P s)
def Witness : Prop :=
  init.procs = [] ∧ init.granted = [] ∧ init.used = [] ∧ init.halted = false ∧
  (run P0 full init [.start 9 1 1, .grant 9 1 1 7, .use 1 7,
      .elevate 1 50 3, .spawn 1 2 [7], .use 2 7]).used =
    [⟨1, 7, none⟩, ⟨1, 8, some (50, 3)⟩, ⟨1, 7, none⟩]

end PL_bg2n1_4
