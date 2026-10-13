open ControlStack.SC08

theorem claim : Claim := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h E C files ops hC
    exact h E C files false ops hC
  · intro E C files halted ops _ hh
    subst halted
    exact Iff.rfl
  · intro C halted h
    exact h.1
  · refine ⟨full, true, sound_full, ?_⟩
    intro h
    cases h.2
  · intro Q h C halted hO
    exact h C halted hO.1
  · intro h
    have hB : BackCoverage OrigDomain := h OrigDomain (fun _ _ hO => hO)
    have ht := hB full true sound_full
    cases ht.2
  · intros
    exact Iff.rfl

theorem witness : Witness := by
  unfold Witness BackDomain OrigDomain
  refine ⟨sound_full, rfl, rfl, ?_, sound_full, ?_, ?_⟩
  · decide
  · intro h
    cases h.2
  · decide
