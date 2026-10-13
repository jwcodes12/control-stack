open ControlStack ControlStack.AuthInstances
example : FrozenBack = BackAt Unguarded Guarded := rfl
example : OrigAt Unguarded Guarded := forged12_spawns_without_auth

theorem claim : Claim := by
  constructor
  · intro unguarded guarded h
    refine ⟨h.1, ?_⟩
    rw [h.2]
    rfl
  · refine ⟨⟨[5], [], [⟨5, 5, 5, false, true⟩, ⟨6, 5, 5, true, true⟩], [], false⟩,
      { SC12.init with halted := true }, ?_⟩
    decide

theorem witness : Witness := by
  decide
