import ControlStack.Scenarios.SC18Logging

namespace ControlStack.SC18

def Back_config_untampered : Prop :=
  ∀ (admins : List ℕ) (trusted T : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal admins trusted o) →
    (run admins trusted T full (init trusted) ops).cfg = trusted

end ControlStack.SC18
