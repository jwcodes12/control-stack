namespace PL_b1_23
open ControlStack.Deployment.TranscriptReplay

-- NOTE: This asserts only the concrete model Trace; the ten receipts and
-- correspondence with a real runtime log are not additional conclusions.
def Back_runtime_trace : Prop :=
  ControlStack.TrustedBroker.Trace
    ControlStack.Deployment.TranscriptReplay.R
    (ControlStack.TrustedBroker.initial 2)
    ControlStack.Deployment.TranscriptReplay.s10



def OrigConclusion  : Prop := ControlStack.TrustedBroker.Trace R (ControlStack.TrustedBroker.initial 2) s10

def BackConclusion  : Prop := ControlStack.TrustedBroker.Trace R (ControlStack.TrustedBroker.initial 2) s10

-- Shape records the blind quantifiers and hypotheses before comparing conclusions.
def Shape : Prop := Back_runtime_trace ↔ BackConclusion

def Claim : Prop := Shape ∧ (BackConclusion ↔ OrigConclusion)

def Witness : Prop := s10.cap = 2 ∧ s10.releases = 2
end PL_b1_23
