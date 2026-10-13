open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness ControlStack.SC26Liveness.Concrete ControlStack.SC26LossyLiveness ControlStack.SC26LossyHalt

theorem execute_identity (R : Roles) (cap : ℕ) (s : St) (c c' k : ℕ) :
    step R cap full s (.execute c k) = step R cap full s (.execute c' k) := rfl

theorem pointwise : Pointwise := by
  intro R cap s c k r pre mid₁ mid₂ post _ _ _ _
  unfold BackAt OrigAt
  simp only [List.append_assoc, List.cons_append, List.nil_append,
    ControlStack.SC26Refinement.run_append, ControlStack.SC26.run_cons]
  rfl


theorem witness : Witness := by
  have hl : ∀ o ∈ setup, legal R0 o := by simp [setup, legal]
  refine ⟨run_inv R0 10 sound_full init setup hl (inv_init R0 10), by decide, ?_, hl, by simp, by decide⟩
  exact ⟨2, by decide, by decide, by decide⟩


theorem claim : Claim := ⟨pointwise, Iff.rfl, Iff.rfl⟩
