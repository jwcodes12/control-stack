namespace PL_bg2n2_3

open ControlStack ControlStack.AuthInstances

def FrozenBack : Prop :=
∀ (admins U : List ℕ) (ops : List (ℕ × SC12.Op)),
    (∀ u ∈ U, u ∉ admins) →
      let s := ControlStack.AuthenticatedLog.authRun
        (SC12.step admins SC12.full) claim12 SC12.init ops;
      SC12.Good s ∧
        ∀ e ∈ s.live, ∃ c : ℕ,
          c ∈ admins ∧ c ∉ U ∧ (c, SC12.Op.start c e.origin) ∈ ops

def BackAt (admins U : List ℕ) (ops : List (ℕ × SC12.Op)) (s : SC12.St) : Prop :=
  SC12.Good s ∧ ∀ e ∈ s.live, ∃ c : ℕ,
    c ∈ admins ∧ c ∉ U ∧ (c, SC12.Op.start c e.origin) ∈ ops
def OrigAt (admins U : List ℕ) (ops : List (ℕ × SC12.Op)) (s : SC12.St) : Prop :=
  SC12.Good s ∧ ∀ e ∈ s.live, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
    (o = SC12.Op.start c e.origin ∧ c ∈ admins)
def Claim : Prop := ∀ (admins U : List ℕ) (ops : List (ℕ × SC12.Op)) (s : SC12.St),
  BackAt admins U ops s ↔ OrigAt admins U ops s
def Witness : Prop :=
  let admins := [9]; let U := [1]
  let ops : List (ℕ × SC12.Op) := [(9, .start 9 5), (1, .spawn 5 6 true 0), (1, .fire 6)]
  let s := AuthenticatedLog.authRun (SC12.step admins SC12.full) claim12 SC12.init ops
  (∀ u ∈ U, u ∉ admins) ∧
  s.live = [⟨5, 5, 5, false, true⟩, ⟨6, 5, 5, true, true⟩] ∧
  s.fired = [(6, 5, 0)] ∧ (9, SC12.Op.start 9 5) ∈ ops ∧ 9 ∉ U

end PL_bg2n2_3
