namespace PL_bg3n2_9
open ControlStack.AuthInstances ControlStack
open ControlStack.AuthenticatedLog

def BackClosed : Prop :=
  ∀ (E : SC17.Env) (U : Set ℕ) (g0 : List SC17.G)
    (ops : List (ℕ × SC17.Op)),
    (∀ c ∈ U, c ∉ E.reviewers) →
      let s := authRun (SC17.step E SC17.full) claim17 (SC17.init g0) ops
      SC17.Good E s ∧
      (∀ a ∈ s.approvals,
        (a.reviewer, SC17.Op.approve a.reviewer a.id) ∈ ops ∧
        a.reviewer ∈ E.reviewers ∧ a.reviewer ∉ U) ∧
      (∀ p ∈ s.props,
        (p.author, SC17.Op.propose p.author p.id p.diff) ∈ ops ∨
        (p.author, SC17.Op.amend p.author p.id p.diff) ∈ ops)

def BackHyp (E : SC17.Env) (U : Set ℕ) : Prop :=
  ∀ c ∈ U, c ∉ E.reviewers
def OrigHyp (E : SC17.Env) (U : List ℕ) : Prop :=
  ∀ c ∈ U, c ∉ E.reviewers
def BackAt (E : SC17.Env) (U : Set ℕ) (s : SC17.St) (ops : List (ℕ × SC17.Op)) : Prop :=
  SC17.Good E s ∧
  (∀ a ∈ s.approvals,
    (a.reviewer, SC17.Op.approve a.reviewer a.id) ∈ ops ∧
    a.reviewer ∈ E.reviewers ∧ a.reviewer ∉ U) ∧
  (∀ p ∈ s.props,
    (p.author, SC17.Op.propose p.author p.id p.diff) ∈ ops ∨
    (p.author, SC17.Op.amend p.author p.id p.diff) ∈ ops)
def OrigAt (E : SC17.Env) (U : List ℕ) (s : SC17.St) (ops : List (ℕ × SC17.Op)) : Prop :=
  SC17.Good E s ∧
  (∀ a ∈ s.approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
    (o = SC17.Op.approve c a.id ∧ c = a.reviewer ∧ c ∈ E.reviewers)) ∧
  (∀ p ∈ s.props, ∃ c o, (c, o) ∈ ops ∧
    (c = p.author ∧ (o = SC17.Op.propose c p.id p.diff ∨ o = SC17.Op.amend c p.id p.diff)))

def OrigClosed : Prop := ∀ E g0 U ops, OrigHyp E U → OrigAt E U (authRun (SC17.step E SC17.full) claim17 (SC17.init g0) ops) ops
def OriginalDeclaration : OrigClosed := @ControlStack.AuthInstances.sc17_safe_authenticated

def Claim : Prop :=
  (BackClosed ↔ ∀ E U g0 ops, BackHyp E U →
    BackAt E U (authRun (SC17.step E SC17.full) claim17 (SC17.init g0) ops) ops) ∧
  (∀ E (UL : List ℕ), BackHyp E {c | c ∈ UL} ↔ OrigHyp E UL) ∧
  (∀ E (US : Set ℕ) (UL : List ℕ) s ops,
    BackHyp E US → OrigHyp E UL → (BackAt E US s ops ↔ OrigAt E UL s ops))

def Witness : Prop :=
  OrigHyp SC17.E0 [1] ∧ BackHyp SC17.E0 {c | c ∈ ([1] : List ℕ)} ∧
  let s := authRun (SC17.step SC17.E0 SC17.full) claim17 (SC17.init [])
    [(1, .propose 1 0 SC17.dA), (2, .approve 2 0), (1, .apply 0)]
  s.approvals.map SC17.Ap.reviewer = [2] ∧
  s.props.map SC17.Pr.author = [1] ∧ s.applied.map SC17.AppRec.id = [0]

end PL_bg3n2_9
