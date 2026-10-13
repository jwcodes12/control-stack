open Finset ControlStack.MonitorCollusion ControlStack.Covert ControlStack.Leakage
theorem claim : Claim := by
  refine ⟨rfl, ?_⟩
  intro V _ P Q β _ _ _
  rw [abs_sub_comm (passRate P β) (passRate Q β)]

theorem witness : Witness := by
  unfold Witness
  norm_num [IsDist, stegoReal, stegoHoney, stegoMonitor, passRate, tv]
  all_goals intro v; cases v <;> norm_num
