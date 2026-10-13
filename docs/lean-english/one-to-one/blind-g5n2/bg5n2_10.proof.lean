open Finset ControlStack.MonitorCollusion ControlStack.Covert ControlStack.Leakage
theorem claim : Claim := by
  refine ⟨rfl, ?_⟩
  intro V _ P Q monitor _ _ _
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
    Bool.true_eq_false, mul_zero, mul_one, zero_add, add_zero]
  unfold passRate
  ring_nf

theorem witness : Witness := by
  unfold Witness
  norm_num [IsDist, stegoReal, stegoHoney, passRate, Fintype.sum_bool]
  all_goals intro v; cases v <;> norm_num
