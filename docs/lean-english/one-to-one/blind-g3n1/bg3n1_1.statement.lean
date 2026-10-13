namespace PL_bg3n1_1

open ControlStack
open ControlStack.SC15

def BackClosed : Prop :=
  ∀ (E : Env) (ops : List Op),
    let s := run E full init ops
    ∀ c ∈ s.merged, MergeOk E s c

def BackAt (E : Env) (s : St) : Prop :=
  ∀ c ∈ s.merged, MergeOk E s c
def OrigAt (E : Env) (s : St) : Prop :=
  ∀ c ∈ s.merged, MergeOk E s c
def OrigClosed : Prop := ∀ (E : Env) (ops : List Op),
  ∀ c ∈ (run E full init ops).merged, MergeOk E (run E full init ops) c

def Claim : Prop :=
  (BackClosed ↔ ∀ E ops, BackAt E (run E full init ops)) ∧
  (OrigClosed ↔ ∀ E ops, OrigAt E (run E full init ops)) ∧
  (∀ E s, BackAt E s ↔ OrigAt E s)

def Witness : Prop :=
  let s := run E0 full init [.propose 1 0 7 [5] [5], .review 2 0 false, .runCI 0, .merge 0]
  s.merged = [⟨0, 1, 7, [5], [5]⟩] ∧ s.reviews ≠ [] ∧ s.ci ≠ []

end PL_bg3n1_1
