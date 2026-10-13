theorem claim : Claim := by
  have originalSignature : ∀ (p : Policy) (s : State) (a : Action) (_h : Invariant p s), OrigAt p s a := @ControlStack.EgressGate.step_safe
  exact ⟨rfl, by intros; exact Iff.rfl⟩

theorem witness : Witness := by
  constructor
  · simp [Witness, Invariant, start, topology, safe]
  · rfl
