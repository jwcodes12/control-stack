namespace PL_bg6n1_6

open ControlStack.SC25 ControlStack.AuthInstances ControlStack.AuthenticatedLog

 def FrozenBack : Prop :=
  ∀ (R : ControlStack.SC25.Roles) (h : ℕ → ℕ) (cls : ℕ → Bool)
    (U : List ℕ) (ops : List (ℕ × ControlStack.SC25.Op)),
    (∀ u ∈ U, u ∉ R.auditors) →
    (∀ u ∈ U, u ∉ R.approvers) →
    let s := authRun (ControlStack.SC25.step R h cls ControlStack.SC25.full)
      claim25 ControlStack.SC25.init ops
    ControlStack.SC25.Good R h cls s ∧
      (∀ v ∈ s.verdicts,
        ∃ (a : ℕ) (before after : List (ℕ × ControlStack.SC25.Op)),
          v.by_ = some a ∧ a ∈ R.auditors ∧ a ∉ U ∧
          ops = before ++ ((a, .audit a v.id v.pass) :: after) ∧
          (let t := authRun
             (ControlStack.SC25.step R h cls ControlStack.SC25.full)
             claim25 ControlStack.SC25.init before
           (ControlStack.SC25.step R h cls ControlStack.SC25.full t
             (.audit a v.id v.pass)).verdicts = t.verdicts ++ [v])) ∧
      (∀ ap ∈ s.approvals,
        ∃ (before after : List (ℕ × ControlStack.SC25.Op)),
          ap.approver ∈ R.approvers ∧ ap.approver ∉ U ∧
          ops = before ++ ((ap.approver, .approve ap.approver ap.id) :: after) ∧
          (let t := authRun
             (ControlStack.SC25.step R h cls ControlStack.SC25.full)
             claim25 ControlStack.SC25.init before
           (ControlStack.SC25.step R h cls ControlStack.SC25.full t
             (.approve ap.approver ap.id)).approvals = t.approvals ++ [ap]))

def Back (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (U : List ℕ) (ops : List (ℕ × Op)) : Prop :=
  let s := authRun (ControlStack.SC25.step R h cls ControlStack.SC25.full)
    claim25 ControlStack.SC25.init ops
  ControlStack.SC25.Good R h cls s ∧
    (∀ v ∈ s.verdicts,
      ∃ (a : ℕ) (before after : List (ℕ × ControlStack.SC25.Op)),
        v.by_ = some a ∧ a ∈ R.auditors ∧ a ∉ U ∧
        ops = before ++ ((a, .audit a v.id v.pass) :: after) ∧
        (let t := authRun
           (ControlStack.SC25.step R h cls ControlStack.SC25.full)
           claim25 ControlStack.SC25.init before
         (ControlStack.SC25.step R h cls ControlStack.SC25.full t
           (.audit a v.id v.pass)).verdicts = t.verdicts ++ [v])) ∧
    (∀ ap ∈ s.approvals,
      ∃ (before after : List (ℕ × ControlStack.SC25.Op)),
        ap.approver ∈ R.approvers ∧ ap.approver ∉ U ∧
        ops = before ++ ((ap.approver, .approve ap.approver ap.id) :: after) ∧
        (let t := authRun
           (ControlStack.SC25.step R h cls ControlStack.SC25.full)
           claim25 ControlStack.SC25.init before
         (ControlStack.SC25.step R h cls ControlStack.SC25.full t
           (.approve ap.approver ap.id)).approvals = t.approvals ++ [ap]))

def Orig (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (U : List ℕ) (ops : List (ℕ × Op)) : Prop :=
  let s := authRun (step R h cls full) claim25 init ops
  Good R h cls s ∧
    (∀ v ∈ s.verdicts, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .audit c v.id v.pass ∧ v.by_ = some c ∧ c ∈ R.auditors)) ∧
    (∀ ap ∈ s.approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .approve c ap.id ∧ c = ap.approver ∧ c ∈ R.approvers))

def Claim : Prop :=
  (FrozenBack = (∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool)
    (U : List ℕ) (ops : List (ℕ × Op)),
    (∀ u ∈ U, u ∉ R.auditors) → (∀ u ∈ U, u ∉ R.approvers) → Back R h cls U ops)) ∧
  (∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool)
    (U : List ℕ) (ops : List (ℕ × Op)),
    (∀ u ∈ U, u ∉ R.auditors) → (∀ u ∈ U, u ∉ R.approvers) →
    (Back R h cls U ops ↔ Orig R h cls U ops))

def Witness : Prop :=
  let ops : List (ℕ × Op) := [(1, .submit 1 0 100 true), (1, .audit 2 0 true),
    (2, .audit 2 0 true), (3, .approve 3 0), (1, .check 0), (1, .fire 0)]
  (∀ u ∈ [1], u ∉ R0.auditors) ∧ (∀ u ∈ [1], u ∉ R0.approvers) ∧
    (authRun (step R0 id cls0 full) claim25 init ops).executed.map Exec.content = [100] ∧
    (authRun (step R0 id cls0 full) claim25 init ops).verdicts = [⟨0, 100, true, some 2⟩] ∧
    (authRun (step R0 id cls0 full) claim25 init ops).approvals = [⟨0, 100, 3⟩]

end PL_bg6n1_6
