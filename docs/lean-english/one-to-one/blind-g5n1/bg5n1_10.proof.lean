open ControlStack.SC23
open scoped BigOperators

theorem original_type (P : Policy) (s : St) (ops : List Op) (h : HOrig P s ops) : OrigAt P s ops :=
  by exact halt_freezes P s ops h

theorem claim : Claim := by
  refine ⟨by simp only [Back_halt_freezes, HBack, BackAt, and_imp, true_implies], ?_, ?_⟩
  · exact by intros; rfl
  · exact by intros; rfl

theorem witness : Witness := by unfold Witness; decide
