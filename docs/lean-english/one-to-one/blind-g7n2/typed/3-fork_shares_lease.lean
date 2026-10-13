import ControlStack.Scenarios.SC28Budget

namespace ControlStack.SC28

def Back_fork_shares_lease : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St)
    (caller parent child newLid lid : ℕ),
    s.halted = false →
    leaseOf s parent = some lid →
    leaseOf s child = none →
    leaseOf (step admins G full s (.fork caller parent child newLid)) child =
      some lid

end ControlStack.SC28
