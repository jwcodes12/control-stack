open ControlStack.AntiRollback
open ControlStack.Gate

theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · intros
    exact Iff.rfl

theorem witness : Witness := by
  unfold Witness
  let G : System (List ℕ) ℕ ℕ := ⟨fun s o => s ++ [o], id⟩
  let S : Spec G := {
    Inv := fun _ => True
    ok := fun s e => e ∈ s
    step_inv := fun _ _ _ => True.intro
    log_prefix := fun s o => List.prefix_append s [o]
    inv_ok := fun _ _ _ he => he }
  refine ⟨G, S, True.intro, ?_, ?_⟩ <;> decide
