namespace PL_bg6n2_2
open ControlStack.SC26

def Back : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops : List Op),
    (∀ a ∈ R.approvers, a ∉ R.agents) →
    (∀ o ∈ ops, legal R o) →
    let s := run R cap full init ops
    ∀ e ∈ s.bank,
      ∃ (r : Req) (a : ℕ),
        reqOf s e.1 = some r ∧
        r.tx = e.2 ∧
        (e.1, a, e.2) ∈ s.approvals ∧
        a ∈ R.approvers ∧
        a ∉ R.agents ∧
        a ≠ r.requester


def BackAt (R : Roles) (s : St) : Prop :=
  ∀ e ∈ s.bank, ∃ (r : Req) (a : ℕ),
    reqOf s e.1 = some r ∧ r.tx = e.2 ∧ (e.1, a, e.2) ∈ s.approvals ∧
    a ∈ R.approvers ∧ a ∉ R.agents ∧ a ≠ r.requester
def OrigAt (R : Roles) (s : St) : Prop :=
  ∀ e ∈ s.bank, ∃ (r : Req) (a : ℕ),
    reqOf s e.1 = some r ∧ r.tx = e.2 ∧ (e.1, a, e.2) ∈ s.approvals ∧
    a ∈ R.approvers ∧ a ∉ R.agents ∧ a ≠ r.requester
def BackEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (ops : List Op), (∀ a ∈ R.approvers, a ∉ R.agents) → (∀ o ∈ ops, legal R o) →
    BackAt R (run R cap full init ops)
def OrigEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (ops : List Op), (∀ a ∈ R.approvers, a ∉ R.agents) → (∀ o ∈ ops, legal R o) →
    OrigAt R (run R cap full init ops)
def Claim : Prop := (Back ↔ BackEnvelope) ∧ (∀ (R : Roles) (s : St), BackAt R s ↔ OrigAt R s)
def honestOps : List Op := [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .arrive 0]
def Witness : Prop := (∀ a ∈ R0.approvers, a ∉ R0.agents) ∧ (∀ o ∈ honestOps, legal R0 o) ∧
  (run R0 20 full init honestOps).bank = [(0, tx1)]
end PL_bg6n2_2
