namespace PL_bg6n2_8
open ControlStack.SC26
open ControlStack.SC26Authenticated ControlStack.Authenticated ControlStack.Gate

open ControlStack.SC26 ControlStack.Authenticated ControlStack.Gate

-- forged fixes all five issuers to 1; R0 fixes the roles to 1, 2, 3, 9.
def Back : Prop :=
  (0, tx1) ∈ ((raw R0 20).run init (forged.map Prod.snd)).bank ∧
  (∀ io ∈ forged, io.1 ∉ R0.approvers) ∧
  ((authed (raw R0 20) claim).run init forged).bank = []


def BackAt (b : List (ℕ × Tx)) (ops : List (ℕ × Op)) (guarded : List (ℕ × Tx)) : Prop :=
  (0, tx1) ∈ b ∧ (∀ io ∈ ops, io.1 ∉ R0.approvers) ∧ guarded = []
def OrigAt (b : List (ℕ × Tx)) (ops : List (ℕ × Op)) (guarded : List (ℕ × Tx)) : Prop :=
  b = [(0, tx1)] ∧ (¬ ∃ a ∈ R0.approvers, (a, Op.approve a 0 tx1) ∈ ops) ∧ guarded = []
def BackEnvelope : Prop := BackAt ((raw R0 20).run init (forged.map Prod.snd)).bank forged
    ((authed (raw R0 20) ControlStack.SC26Authenticated.claim).run init forged).bank
def OrigEnvelope : Prop := OrigAt ((authed (raw R0 20) (fun _ => none)).run init forged).bank forged
    ((authed (raw R0 20) ControlStack.SC26Authenticated.claim).run init forged).bank
def Claim : Prop := (Back ↔ BackEnvelope) ∧
  (OrigEnvelope → Back) ∧
  (∀ (b : List (ℕ × Tx)) (guarded : List (ℕ × Tx)),
    OrigAt b forged guarded → BackAt b forged guarded) ∧
  (∃ (b : List (ℕ × Tx)) (guarded : List (ℕ × Tx)),
    BackAt b forged guarded ∧ ¬ OrigAt b forged guarded) ∧
  (∃ (ops : List (ℕ × Op)),
    OrigAt [(0, tx1)] ops [] ∧ ¬ BackAt [(0, tx1)] ops [])
def Witness : Prop := forged.length = 5 ∧ R0.agents = [1] ∧ R0.approvers = [2] ∧
  tx1.amount = 10 ∧
  ((raw R0 20).run init (forged.map Prod.snd)).bank = [(0, tx1)] ∧
  ((authed (raw R0 20) ControlStack.SC26Authenticated.claim).run init forged).bank = []
end PL_bg6n2_8
