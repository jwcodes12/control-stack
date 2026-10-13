theorem original_type : ∀ (d : IR) (r : Node) (actualEdges : List Edge) (R : ControlStack.TrustedBroker.Roles) (cap : Nat) (t : ControlStack.TrustedBroker.State) (sinkNonces : List Nat), Accepted d → ExtractionFaithful d r actualEdges → BrokerProtocolRefinement d R cap t sinkNonces →OrigConclusion d r actualEdges R cap t sinkNonces := by
  intro d r actualEdges R cap t sinkNonces h he hr
  exact ControlStack.Deployment.deployment_broker_safe d r R cap t actualEdges sinkNonces h he hr

theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · intro d r actualEdges R cap t sinkNonces h he hr
    exact Iff.rfl

theorem witness : Witness := by exact ⟨clean_accepted, Witnesses.extracted, Witnesses.refined⟩
