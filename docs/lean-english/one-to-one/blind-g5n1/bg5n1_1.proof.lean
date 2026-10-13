open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
open scoped BigOperators

theorem original_type (E : Env) (ops : List Op) (h : HOrig E ops) : OrigAt E ops :=
  by exact sc21_safe E ops

theorem claim : Claim := by
  refine ⟨by simp only [Back_sc21_safe, HBack, BackAt, and_imp, true_implies], ?_, ?_⟩
  · exact by intros; rfl
  · exact by intros; rfl

theorem witness : Witness := by unfold Witness; decide
