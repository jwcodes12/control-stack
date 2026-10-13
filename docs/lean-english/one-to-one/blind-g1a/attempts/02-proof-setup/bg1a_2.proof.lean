theorem claim : Claim := by
  have originalSignature : ∀ (p : Policy) (s : State) (actions : List Action) (_h : Invariant p s), OrigAt p s actions := @ControlStack.EgressGate.trace_safe
  exact ⟨rfl, by intros; exact Iff.rfl⟩

theorem witness : Witness := by
  constructor
  · simp [Witness, Invariant, start, topology, safe]
  · rfl
