import ControlStack.Deployment.TranscriptReplay

namespace ControlStack.Deployment.TranscriptReplay

def Back_replay_was_not_allowed : Prop :=
  ∀ (now : Nat) (a' : ControlStack.TrustedBroker.Approval)
    (l' : ControlStack.TrustedBroker.Lease),
    ¬ ControlStack.TrustedBroker.Allowed R s8 now q8 a' l'

end ControlStack.Deployment.TranscriptReplay
