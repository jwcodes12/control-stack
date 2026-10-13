import ControlStack.Scenarios.AuthInstancesA

namespace ControlStack.AuthInstances

open ControlStack.AuthenticatedLog

def Back_sc25_safe_authenticated : Prop :=
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

end ControlStack.AuthInstances
