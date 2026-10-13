namespace PL_bg2n1_7
open ControlStack.SC10

def Back_sc10_safe : Prop :=
  ∀ (E : Env), E.h E.pinned = E.pinnedDigest →
    ∀ (ops : List Op), Good E (run E full init ops)

def EnglishOk (E : Env) (s : St) : Prop :=
  (∀ d ∈ s.decisions, ∃ i w, d.ver = some i ∧
    s.versions[i]? = some (d.val, w) ∧ w ∈ E.admins ∧ i + 1 = d.curLen) ∧
  (∀ b ∈ s.builds, E.h b = E.pinnedDigest)
def BackAt (E : Env) (ops : List Op) : Prop := Good E (run E full init ops)
def OrigAt (E : Env) (ops : List Op) : Prop := Good E (run E full init ops)
def Claim : Prop :=
  (Back_sc10_safe = (∀ E, E.h E.pinned = E.pinnedDigest → ∀ ops, BackAt E ops)) ∧
  (∀ E, E.h E.pinned = E.pinnedDigest → ∀ ops, BackAt E ops ↔ OrigAt E ops) ∧
  (∀ E s, EnglishOk E s ↔ Good E s)
def Witness : Prop :=
  E0.h E0.pinned = E0.pinnedDigest ∧ init.versions = [] ∧
  init.decisions = [] ∧ init.builds = [] ∧ init.halted = false ∧
  let s := run E0 full init [.writePolicy 9 5, .decide 1, .writePath 666, .build]
  s.decisions = [⟨1, some 0, 5, 1⟩] ∧ s.builds = [40] ∧ s.pathTool = 666

end PL_bg2n1_7
