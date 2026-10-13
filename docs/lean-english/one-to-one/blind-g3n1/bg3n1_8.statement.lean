namespace PL_bg3n1_8

open ControlStack
open ControlStack.SC16 ControlStack.SC16Disjoint

def BackClosed : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (ops : List Op),
    (∀ c ∈ R.reviewers, c ∉ R.agents) →
    (∀ c ∈ R.approvers, c ∉ R.agents) →
    let s := run R h full init ops
    let contents := s.deployed.map Dep.content ++ s.reviews.map Review.content
    (∀ (x y : ℕ), x ∈ contents → y ∈ contents → h x = h y → x = y) →
    ∀ e ∈ s.deployed,
      (∃ rv ∈ s.reviews,
        rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧
        rv.reviewer ∉ R.agents ∧ rv.reviewer ≠ rv.stager) ∧
      (∃ ap ∈ s.approvals,
        ap.n = e.n ∧ ap.target = e.target ∧
        ap.approver ∈ R.approvers ∧ ap.approver ∉ R.agents)

def Contents (s : St) : List ℕ := s.deployed.map Dep.content ++ s.reviews.map Review.content
def HypBack (h : ℕ → ℕ) (s : St) : Prop :=
  ∀ x y, x ∈ Contents s → y ∈ Contents s → h x = h y → x = y
def HypOrig (h : ℕ → ℕ) (s : St) : Prop :=
  Set.InjOn h {c | (∃ e ∈ s.deployed, e.content = c) ∨ ∃ rv ∈ s.reviews, rv.content = c}
def HRev (R : Roles) : Prop := ∀ c ∈ R.reviewers, c ∉ R.agents
def HApp (R : Roles) : Prop := ∀ c ∈ R.approvers, c ∉ R.agents
def BackAt (R : Roles) (s : St) : Prop :=
  ∀ e ∈ s.deployed,
    (∃ rv ∈ s.reviews, rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧
      rv.reviewer ∉ R.agents ∧ rv.reviewer ≠ rv.stager) ∧
    (∃ ap ∈ s.approvals, ap.n = e.n ∧ ap.target = e.target ∧
      ap.approver ∈ R.approvers ∧ ap.approver ∉ R.agents)
def OrigAt (R : Roles) (s : St) : Prop :=
  ∀ e ∈ s.deployed,
    (∃ rv ∈ s.reviews, rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧
      rv.reviewer ∉ R.agents ∧ rv.reviewer ≠ rv.stager) ∧
    (∃ ap ∈ s.approvals, ap.n = e.n ∧ ap.target = e.target ∧
      ap.approver ∈ R.approvers ∧ ap.approver ∉ R.agents)
def OrigClosed : Prop := ∀ (R : Roles) (h : ℕ → ℕ) (ops : List Op),
  HRev R → HApp R → HypOrig h (run R h full init ops) → OrigAt R (run R h full init ops)

def Claim : Prop :=
  (BackClosed ↔ ∀ R h ops, HRev R → HApp R → HypBack h (run R h full init ops) → BackAt R (run R h full init ops)) ∧
  (∀ h s, HypBack h s ↔ HypOrig h s) ∧
  (∀ R s, BackAt R s ↔ OrigAt R s)

def Witness : Prop :=
  HRev R0 ∧ HApp R0 ∧
  let s := run R0 id full init [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]
  HypBack id s ∧ s.deployed = [⟨0, 5, 7⟩] ∧ s.reviews ≠ [] ∧ s.approvals ≠ []

end PL_bg3n1_8
