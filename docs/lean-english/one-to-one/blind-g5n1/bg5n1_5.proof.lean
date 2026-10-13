open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
open scoped BigOperators

theorem original_type (N B k : ℕ) (σ : List (AOut Unit) → Bool → ℝ) (h : HOrig N B k σ) : OrigAt N B k σ :=
  by exact sc21_adaptive k B h.1 σ h.2

theorem claim : Claim := by
  refine ⟨by simp only [Back_sc21_adaptive, HBack, BackAt, and_imp, true_implies], ?_, ?_⟩
  · exact by intros; rfl
  · exact by
      intro N B k σ h
      classical
      unfold BackAt OrigAt
      
      simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]

theorem witness : Witness := by
  norm_num [Witness, HBack, wSigma, IsDist, Fintype.sum_bool]
