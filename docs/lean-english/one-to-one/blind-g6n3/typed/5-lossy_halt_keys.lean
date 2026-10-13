import ControlStack.Scenarios.SC26LossyHalt

namespace ControlStack.SC26LossyHalt

open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26LossyLiveness

def Back_lossy_halt_keys : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp),
    s.halted = true →
    (∀ o ∈ ops, legalL R o) →
    ∀ k ∈ (runLH R cap true s ops).bank.map Prod.fst,
      k ∈ s.bank.map Prod.fst ∨ k ∈ s.wire.map Prod.fst

end ControlStack.SC26LossyHalt
