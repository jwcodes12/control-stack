namespace PL_g0_16
open ControlStack.Deployment
def Back : Prop := ∀ (d : IR) (r : Node) (R : ControlStack.TrustedBroker.Roles) (cap : Nat) (t : ControlStack.TrustedBroker.State) (actual : List Edge) (sinkNonces : List Nat), Accepted d → ExtractionFaithful d r actual → BrokerProtocolRefinement d R cap t sinkNonces → sinkNonces.length < cap
 def Claim : Prop := ¬ Back
 def Witness : Prop := Accepted clean
end PL_g0_16
