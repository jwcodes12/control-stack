open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
open scoped BigOperators

theorem original_type (N B k : ℕ) (rep truth : Fin N → ℕ) (h : HOrig N B k rep truth) : OrigAt N B k rep truth :=
  by exact sc22_unreplicated_misreport rep truth h

theorem claim : Claim := by
  refine ⟨by simp only [Back_sc22_unreplicated_misreport, HBack, BackAt, and_imp, true_implies], ?_, ?_⟩
  · exact by intros; rfl
  · exact by intros; rfl

theorem witness : Witness := by
  unfold Witness
  refine ⟨by decide, by decide, ?_⟩
  exact ⟨{0}, by decide⟩
