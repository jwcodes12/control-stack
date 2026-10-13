import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace ControlStack.TrustedBroker

def Back_halted_absorbing : Prop :=
  ∀ (roles : ControlStack.TrustedBroker.Roles)
    (s t : ControlStack.TrustedBroker.State),
    s.halted = true → ControlStack.TrustedBroker.Step roles s t →
    t.halted = true ∧ t.releases = s.releases

end ControlStack.TrustedBroker
