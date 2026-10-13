theorem witness : Witness := by
  unfold Witness
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    subst a
    decide
  · intro io hio hni
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hio
    rcases hio with hio | hio | hio | hio | hio
    all_goals subst io
    all_goals simp_all [ControlStack.SC18.legal]
  · decide
  · decide
