theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · intro admins trusted T s i a0 a1 a2 a3
    simp only [BackAt, OrigAt, ControlStack.SC18.run, List.foldl_append, List.foldl_cons, List.foldl_nil]
