import ControlStack.Scenarios.SC18Logging

namespace ControlStack.SC18

-- The saved log length identifies the trusted-log prefix at each release.
def Back_sc18_safe : Prop :=
  ∀ (admins : List ℕ) (trusted T : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal admins trusted o) →
    Good T (run admins trusted T full (init trusted) ops)

end ControlStack.SC18
