namespace PL_bg3n2_3
open ControlStack.SC16Refinement ControlStack
open ControlStack.SC16

def BackClosed : Prop :=
  ∀ (R : SC16.Roles) (h : ℕ → ℕ) (ops : List COp),
    let s := α (runC R h false cinit ops)
    let contents := s.deployed.map SC16.Dep.content ++
      s.reviews.map SC16.Review.content
    (∀ x ∈ contents, ∀ y ∈ contents, h x = h y → x = y) →
      ∀ e ∈ s.deployed,
        ∃ rv ∈ s.reviews,
          e.content = rv.content ∧
          rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager

def BackHyp (h : ℕ → ℕ) (s : SC16.St) : Prop :=
  ∀ x ∈ s.deployed.map SC16.Dep.content ++ s.reviews.map SC16.Review.content,
    ∀ y ∈ s.deployed.map SC16.Dep.content ++ s.reviews.map SC16.Review.content,
      h x = h y → x = y
def OrigHyp (h : ℕ → ℕ) (s : SC16.St) : Prop :=
  Set.InjOn h {c | (∃ e ∈ s.deployed, e.content = c) ∨ ∃ rv ∈ s.reviews, rv.content = c}
def BackAt (R : Roles) (s : SC16.St) : Prop :=
  ∀ e ∈ s.deployed, ∃ rv ∈ s.reviews,
    e.content = rv.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager
def OrigAt (R : Roles) (s : SC16.St) : Prop :=
  ∀ e ∈ s.deployed, ∃ rv ∈ s.reviews,
    rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager

def OrigClosed : Prop := ∀ R h ops, OrigHyp h (α (runC R h false cinit ops)) → OrigAt R (α (runC R h false cinit ops))
def OriginalDeclaration : OrigClosed := @ControlStack.SC16Refinement.concrete_reviewed_content

def Claim : Prop :=
  (BackClosed ↔ ∀ R h ops,
    BackHyp h (α (runC R h false cinit ops)) → BackAt R (α (runC R h false cinit ops))) ∧
  (∀ h s, BackHyp h s ↔ OrigHyp h s) ∧
  (∀ R s, BackAt R s ↔ OrigAt R s)

def Witness : Prop :=
  let s := α (runC R0 id false cinit [.put 1 7, .review 2 7 5, .approve 3 0 7 5 0, .deploy 1 0 5])
  BackHyp id s ∧ s.deployed ≠ [] ∧ s.reviews ≠ []

end PL_bg3n2_3
