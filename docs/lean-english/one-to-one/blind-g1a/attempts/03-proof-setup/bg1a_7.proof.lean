open ControlStack.SC06

theorem claim : Claim := by
  have originalSignature : ∀ (P : Policy) (s : St) (ops : List Op) (_hh : s.halted = true), OrigAt P s ops := @ControlStack.SC06.halt_freezes
  exact ⟨rfl, by intros; exact Iff.rfl⟩

theorem witness : Witness := by
  decide
