namespace PL_b1_20
open ControlStack.TrustedBroker

def Back_halted_absorbing : Prop :=
  ∀ (roles : ControlStack.TrustedBroker.Roles)
    (s t : ControlStack.TrustedBroker.State),
    s.halted = true → ControlStack.TrustedBroker.Step roles s t →
    t.halted = true ∧ t.releases = s.releases



def OrigConclusion (roles : Roles) (s t : State) : Prop := t.halted = true ∧ t.releases = s.releases

def BackConclusion (roles : Roles) (s t : State) : Prop := t.halted = true ∧ t.releases = s.releases

-- Shape records the blind quantifiers and hypotheses before comparing conclusions.
def Shape : Prop := Back_halted_absorbing ↔ ∀ (roles : Roles) (s t : State), s.halted = true → Step roles s t →BackConclusion roles s t

def Claim : Prop := Shape ∧ ∀ (roles : Roles) (s t : State), s.halted = true → Step roles s t →(BackConclusion roles s t ↔ OrigConclusion roles s t)

def Witness : Prop := let s := { initial 1 with halted := true }; s.halted = true ∧ Step ControlStack.Deployment.Witnesses.R s s ∧ s.cap = 1
end PL_b1_20
