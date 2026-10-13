namespace PL_bg2n1_8
open ControlStack.SC10

def Back_policy_admin_only : Prop :=
  ∀ (E : Env), E.h E.pinned = E.pinnedDigest →
    ∀ (ops : List Op),
      ∀ pv ∈ (run E full init ops).versions, pv.2 ∈ E.admins

def BackAt (E : Env) (ops : List Op) : Prop :=
  ∀ pv ∈ (run E full init ops).versions, pv.2 ∈ E.admins
def OrigAt (E : Env) (ops : List Op) : Prop :=
  ∀ pv ∈ (run E full init ops).versions, pv.2 ∈ E.admins
def Claim : Prop :=
  (Back_policy_admin_only = (∀ E, E.h E.pinned = E.pinnedDigest → ∀ ops, BackAt E ops)) ∧
  (∀ E, E.h E.pinned = E.pinnedDigest → ∀ ops, BackAt E ops ↔ OrigAt E ops)
def Witness : Prop :=
  E0.h E0.pinned = E0.pinnedDigest ∧ init.versions = [] ∧
  (run E0 full init [.writePolicy 1 999, .writePolicy 9 5, .writePolicy 9 6]).versions =
    [(5, 9), (6, 9)]

end PL_bg2n1_8
