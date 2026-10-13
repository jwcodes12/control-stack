open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
open scoped BigOperators

theorem original_type (N B k : ℕ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (h : HOrig N B k Y K σ) : OrigAt N B k Y K σ :=
  by exact sc21_adaptive_content k B h.1 K σ h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem claim : Claim := by
  refine ⟨by simp only [Back_sc21_adaptive_content, HBack, BackAt, and_imp, true_implies], ?_, ?_⟩
  · exact by intros; simp only [HBack, HOrig, Fintype.sum_prod_type]
  · exact by
      intro N B k Y inst K σ h
      classical
      unfold BackAt OrigAt
      unfold pU
      simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]

theorem witness : Witness := by
  norm_num [Witness, HBack, wKernel, wSigma, IsDist, AOut, Fintype.sum_prod_type, Fintype.sum_bool]
