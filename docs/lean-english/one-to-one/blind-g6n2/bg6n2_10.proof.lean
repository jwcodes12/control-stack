open ControlStack.SC26
open ControlStack.SC26Liveness
theorem original_signature : OrigEnvelope := by
  intro R cap s k r c hi hh hr ha hk hc
  exact honest_progress R cap s hi c k r hh hr ha hk hc
theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_⟩
  intro R cap s k r caller
  exact Iff.rfl
theorem witness : Witness := by
  unfold Witness
  refine ⟨?_, by decide, by decide, ?_, by decide, by decide, by decide⟩
  · constructor <;> simp [ready, reqOf, Approved, amt, tx1, R0]
  · exact ⟨2, by decide, by decide, by decide⟩
