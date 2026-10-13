open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
open scoped BigOperators

theorem original_type (N B k : ℕ) (rep truth : Fin N → ℕ) (h : HOrig N B k rep truth) : OrigAt N B k rep truth :=
  by exact sc21_undetected_le_pow rep truth h.1 h.2.1 h.2.2

theorem claim : Claim := by
  refine ⟨by simp only [Back_sc21_undetected_le_pow, HBack, BackAt, and_imp, true_implies], ?_, ?_⟩
  · exact by intros; rfl
  · exact by
      intro N B k rep truth h
      unfold BackAt OrigAt
      rw [Nat.cast_sub h.2.1]

theorem witness : Witness := by
  unfold Witness
  refine ⟨by decide, by decide, by decide, ?_⟩
  exact ⟨{0}, by decide⟩
