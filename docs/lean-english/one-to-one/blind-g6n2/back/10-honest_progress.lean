namespace ControlStack.SC26Liveness

open ControlStack.SC26

def Back_honest_progress : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req) (caller : ℕ),
    Inv R cap s →
    s.halted = false →
    reqOf s k = some r →
    Approved R s k r →
    k ∉ s.reserved →
    s.spent + r.tx.amount ≤ cap →
    (k, r.tx) ∈
      (run R cap full s
        [Op.execute caller k, Op.deliver k, Op.arrive k]).bank

end ControlStack.SC26Liveness
