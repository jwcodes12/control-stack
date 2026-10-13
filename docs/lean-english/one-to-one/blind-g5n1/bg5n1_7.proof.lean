open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
open scoped BigOperators

theorem original_type (N B k : ℕ) (r : ℝ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (h : HOrig N B k r Y K σ) : OrigAt N B k r Y K σ := by exact sc21_adaptive_recall k B h.1 r h.2.1 h.2.2.1 K σ h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2

theorem scope_inclusion : ∀ (N B k : ℕ) (r : ℝ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ), HBack N B k r Y K σ → HOrig N B k r Y K σ := by
    intro N B k r Y inst K σ h
    rcases h with ⟨hB, hr0, hr1, hσ, h0, h1, hmarg, hrec⟩
    exact ⟨hB, hr0, hr1, hσ, h0, by simpa only [Fintype.sum_prod_type] using h1, hrec⟩
theorem conclusion_iff : ∀ (N B k : ℕ) (r : ℝ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ), HBack N B k r Y K σ → (BackAt N B k r Y K σ ↔ OrigAt N B k r Y K σ) := by
    intro N B k r Y inst K σ h
    classical
    unfold BackAt OrigAt
    unfold pU
    simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]

theorem strict_scope : StrictScope := by
  constructor
  · simp only [HOrig, cKernel, cSigma, IsDist, AOut, Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num
  · intro h
    have hm := h.2.2.2.2.2.2.1 ({0} : Finset (Fin 2)) (by decide) [] true
    norm_num [cKernel, cSigma, Fintype.sum_bool] at hm

theorem claim : Claim := by
  refine ⟨by simp only [Back_sc21_adaptive_recall, HBack, BackAt, and_imp, true_implies], scope_inclusion, conclusion_iff, ?_, strict_scope⟩
  intro N B k r Y inst K σ law h
  exact (conclusion_iff N B k r Y K σ h).mpr (law (scope_inclusion N B k r Y K σ h))

theorem witness : Witness := by
  unfold Witness HBack
  norm_num [wKernel, wSigma, IsDist, AOut, Fintype.sum_prod_type, Fintype.sum_bool]
  intro S hS h
  split_ifs <;> norm_num
