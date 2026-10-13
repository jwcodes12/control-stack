import ControlStack.Scenarios.SC26Liveness

namespace ControlStack.SC26Liveness

open ControlStack.SC26

def Back_progress_interleaved : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req)
    (pre mid₁ mid₂ post : List Op),
    Inv R cap s →
    reqOf s k = some r →
    Approved R s k r →
    (∀ o ∈ pre ++ mid₁ ++ mid₂ ++ post, legal R o) →
    let beforeExecute := run R cap full s pre
    let final := run R cap full s
      (pre ++ [.execute r.requester k] ++ mid₁ ++ [.deliver k] ++
        mid₂ ++ [.arrive k] ++ post)
    final.halted = true ∨
      (k, r.tx) ∈ final.bank ∨
      (k ∉ beforeExecute.reserved ∧ cap < beforeExecute.spent + r.tx.amount)

end ControlStack.SC26Liveness
