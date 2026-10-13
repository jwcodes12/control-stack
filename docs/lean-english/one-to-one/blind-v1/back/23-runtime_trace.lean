namespace ControlStack.Deployment.TranscriptReplay

-- NOTE: This asserts only the concrete model Trace; the ten receipts and
-- correspondence with a real runtime log are not additional conclusions.
def Back_runtime_trace : Prop :=
  ControlStack.TrustedBroker.Trace
    ControlStack.Deployment.TranscriptReplay.R
    (ControlStack.TrustedBroker.initial 2)
    ControlStack.Deployment.TranscriptReplay.s10

end ControlStack.Deployment.TranscriptReplay
