open ControlStack ControlStack.Deployment

theorem original_signature : Orig := @gate_contract

theorem claim : Claim := by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨[⟨.request 23701 payload, by trivial⟩, ⟨.approve 23703 0 payload, by trivial⟩, ⟨.execute 23701 0, by trivial⟩, ⟨.deliver 0, by trivial⟩, ⟨.arrive 0, by trivial⟩], rfl, ?_⟩
  decide
