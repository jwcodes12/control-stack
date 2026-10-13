namespace PL_bg3n1_10

open ControlStack
open ControlStack.SC16 ControlStack.AuthInstances ControlStack.AuthenticatedLog

def BackClosed : Prop :=
  ∀ (R : SC16.Roles) (h : ℕ → ℕ) (U : List ℕ)
    (ops : List (ℕ × SC16.Op)),
    (∀ c ∈ U, c ∉ R.reviewers ∧ c ∉ R.approvers) →
    let s := AuthenticatedLog.authRun (SC16.step R h SC16.full) claim16 SC16.init ops
    SC16.Good R h s ∧
    (∀ rv ∈ s.reviews,
      (rv.reviewer, SC16.Op.review rv.reviewer rv.d) ∈ ops ∧
      rv.reviewer ∉ U ∧ rv.reviewer ∈ R.reviewers) ∧
    (∀ ap ∈ s.approvals,
      (ap.approver, SC16.Op.approve ap.approver ap.n ap.d ap.target ap.slot) ∈ ops ∧
      ap.approver ∉ U ∧ ap.approver ∈ R.approvers)

def HypBack (R : Roles) (U : List ℕ) : Prop := ∀ c ∈ U, c ∉ R.reviewers ∧ c ∉ R.approvers
def HRev (R : Roles) (U : List ℕ) : Prop := ∀ c ∈ U, c ∉ R.reviewers
def HApp (R : Roles) (U : List ℕ) : Prop := ∀ c ∈ U, c ∉ R.approvers
def BackAt (R : Roles) (h : ℕ → ℕ) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good R h s ∧
  (∀ rv ∈ s.reviews, (rv.reviewer, Op.review rv.reviewer rv.d) ∈ ops ∧
    rv.reviewer ∉ U ∧ rv.reviewer ∈ R.reviewers) ∧
  (∀ ap ∈ s.approvals, (ap.approver, Op.approve ap.approver ap.n ap.d ap.target ap.slot) ∈ ops ∧
    ap.approver ∉ U ∧ ap.approver ∈ R.approvers)
def OrigAt (R : Roles) (h : ℕ → ℕ) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good R h s ∧
  (∀ rv ∈ s.reviews, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
    (o = .review c rv.d ∧ c = rv.reviewer ∧ c ∈ R.reviewers)) ∧
  (∀ ap ∈ s.approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
    (o = .approve c ap.n ap.d ap.target ap.slot ∧ c = ap.approver ∧ c ∈ R.approvers))
def OrigClosed : Prop := ∀ (R : Roles) (h : ℕ → ℕ) (U : List ℕ) (ops : List (ℕ × Op)),
  HRev R U → HApp R U → OrigAt R h U ops (authRun (step R h full) claim16 init ops)

def Claim : Prop :=
  (BackClosed ↔ ∀ R h U ops, HypBack R U → BackAt R h U ops (authRun (step R h full) claim16 init ops)) ∧
  (∀ R U, HypBack R U ↔ (HRev R U ∧ HApp R U)) ∧
  (∀ R h U ops s, BackAt R h U ops s ↔ OrigAt R h U ops s)

def Witness : Prop :=
  HypBack R0 [1] ∧
  let s := authRun (step R0 id full) claim16 init [(1, .stage 1 7), (2, .review 2 7), (3, .approve 3 0 7 5 0), (1, .deploy 1 0 5 7)]
  s.deployed = [⟨0, 5, 7⟩] ∧ s.reviews ≠ [] ∧ s.approvals ≠ []

end PL_bg3n1_10
