import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace ControlStack.Deployment

-- NOTE: Uses the real ControlStack.Deployment.Accepted predicate.
def Back_exclusive_sink : Prop :=
  ∀ (d : IR) (e : Edge),
    ControlStack.Deployment.Accepted d →
    e ∈ d.edges → e.authority = true → e.target = d.sink →
    e.source = d.receiver

end ControlStack.Deployment
