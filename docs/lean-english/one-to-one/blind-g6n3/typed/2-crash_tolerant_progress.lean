import ControlStack.Scenarios.SC26Liveness

namespace ControlStack.SC26Liveness.Concrete

open ControlStack.SC26 ControlStack.SC26Refinement

def Back_crash_tolerant_progress : Prop :=
  ∀ (R : Roles) (cap k : ℕ) (ops₀ pre mid post : List COp),
    (∀ o ∈ ops₀, legalC R o) →
    let start := runC R cap true cinit ops₀
    (∃ d ∈ start.delivery, d.id = k) →
    (∀ o ∈ pre ++ mid ++ post, legalC R o) →
    (runC R cap true start pre).halted = false →
    let final := runC R cap true start
      (pre ++ [.recover] ++ mid ++ [.bankProcess k] ++ post)
    (final.bank.map Prod.fst).count k = 1

end ControlStack.SC26Liveness.Concrete
