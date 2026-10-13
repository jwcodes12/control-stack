open ControlStack.SC06

theorem claim : Claim := by
  have originalSignature : ∀ (P : Policy) (ops : List Op), OrigAt P ops := @ControlStack.SC06.sc06_safe
  exact ⟨rfl, by intros; exact Iff.rfl⟩

theorem witness : Witness := by
  unfold Witness
  decide
