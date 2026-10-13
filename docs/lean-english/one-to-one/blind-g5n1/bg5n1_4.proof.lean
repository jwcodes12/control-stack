open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
open scoped BigOperators

theorem original_type (N B k : ℕ) (S : Finset (Fin N)) (h : HOrig N B k S) : OrigAt N B k S :=
  by exact observable_sample_nogo S h.1 h.2

theorem claim : Claim := by
  refine ⟨by simp only [Back_observable_sample_nogo, HBack, BackAt, and_imp, true_implies], ?_, ?_⟩
  · exact by intros; rfl
  · exact by intros; rfl

theorem witness : Witness := by
  refine ⟨by decide, by decide, {1}, by decide, by decide⟩
