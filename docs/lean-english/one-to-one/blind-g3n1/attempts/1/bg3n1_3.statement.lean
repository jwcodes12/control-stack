namespace PL_bg3n1_3

open ControlStack.SC15 ControlStack.AuthInstances ControlStack.AuthenticatedLog

def BackClosed : Prop :=
  ∀ (E : SC15.Env) (U : List ℕ) (ops : List (ℕ × SC15.Op)),
    (∀ c ∈ U, c ∉ E.reviewers ∧ c ∉ E.security) →
    let s := AuthenticatedLog.authRun (SC15.step E SC15.full) claim15 SC15.init ops
    (∀ c ∈ s.merged, SC15.MergeOk E s c) ∧
    (∀ r ∈ s.reviews,
      (r.reviewer, SC15.Op.review r.reviewer r.id r.sec) ∈ ops ∧
      r.reviewer ∉ U ∧ SC15.roleOk E r.sec r.reviewer = true)

def HypBack (E : Env) (U : List ℕ) : Prop := ∀ c ∈ U, c ∉ E.reviewers ∧ c ∉ E.security
def HypOrig (E : Env) (U : List ℕ) : Prop := ∀ c ∈ U, c ∉ E.reviewers ++ E.security
def BackAt (E : Env) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  (∀ c ∈ s.merged, MergeOk E s c) ∧
  (∀ r ∈ s.reviews, (r.reviewer, Op.review r.reviewer r.id r.sec) ∈ ops ∧
    r.reviewer ∉ U ∧ roleOk E r.sec r.reviewer = true)
def OrigAt (E : Env) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  (∀ c ∈ s.merged, MergeOk E s c) ∧
  (∀ r ∈ s.reviews, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
    (o = .review c r.id r.sec ∧ c = r.reviewer ∧ roleOk E r.sec c = true))
def OrigClosed : Prop := ∀ (E : Env) (U : List ℕ) (ops : List (ℕ × Op)),
  HypOrig E U → OrigAt E U ops (authRun (step E full) claim15 init ops)

def Claim : Prop :=
  (BackClosed ↔ ∀ E U ops, HypBack E U → BackAt E U ops (authRun (step E full) claim15 init ops)) ∧
  (∀ E U, HypBack E U ↔ HypOrig E U) ∧
  (∀ E U ops s, BackAt E U ops s ↔ OrigAt E U ops s)

def Witness : Prop :=
  HypBack E0 [1] ∧
  let s := authRun (step E0 full) claim15 init [(1, .propose 1 0 7 [5] [5]), (2, .review 2 0 false), (1, .runCI 0), (1, .merge 0)]
  s.merged = [⟨0, 1, 7, [5], [5]⟩] ∧ s.reviews ≠ []

end PL_bg3n1_3
