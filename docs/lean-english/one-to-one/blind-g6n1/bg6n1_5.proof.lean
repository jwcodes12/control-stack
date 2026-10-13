open ControlStack.SC25Content ControlStack.SC25

theorem singleton_bridge (es : List Exec) (g : List ARec) (hl : es.length = 1) : Back es g ↔ Orig es g := by
  obtain ⟨e, rfl⟩ := List.length_eq_one_iff.mp hl
  simp [Back, Orig]

theorem claim : Claim := by
  refine ⟨rfl, singleton_bridge, ?_, ?_⟩
  · decide
  · rw [grun_fst]
    exact singleton_bridge _ _ (by decide)

theorem witness : Witness := by
  unfold Witness
  decide
