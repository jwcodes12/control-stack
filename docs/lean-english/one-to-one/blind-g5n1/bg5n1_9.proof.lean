open ControlStack.SC23
open scoped BigOperators

theorem original_type (P : Policy) (ops : List Op) (h : HOrig P ops) : OrigAt P ops :=
  by exact sc23_safe P ops

theorem claim : Claim := by
  refine ⟨by simp only [Back_sc23_safe, HBack, BackAt, and_imp, true_implies], ?_, ?_⟩
  · exact by intros; rfl
  · exact by intros; rfl

theorem witness : Witness := by unfold Witness; decide
