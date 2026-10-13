import ControlStack.Deployment.TranscriptReplay

namespace ControlStack.Deployment.TranscriptReplay

def Back_omitted_tail_is_accepted : Prop :=
  ControlStack.CheckedTrace.verified table.step 0 withoutLastRelease = true

end ControlStack.Deployment.TranscriptReplay
