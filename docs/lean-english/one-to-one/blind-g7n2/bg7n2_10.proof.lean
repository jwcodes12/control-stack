open ControlStack
open ControlStack.AntiRollback
#check (ControlStack.AntiRollback.sc28_rollback_safe : OrigFull)

theorem claim : Claim :=
by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  have erun : ∀ (admins : List ℕ) (G : ℕ) (l : List {o : SC28.Op // SC28.legal o}) (s : SC28.St),
      (SC28.sys admins G).run s l = SC28.run admins G SC28.full s (l.map Subtype.val) := by
    intro admins G l
    induction l with
    | nil => intro s; rfl
    | cons o l ih => intro s; exact ih _
  intro admins G t
  unfold BackResult OrigResult
  rw [erun]

theorem witness : Witness :=
by
  unfold Witness
  set_option maxRecDepth 4096 in
    decide
