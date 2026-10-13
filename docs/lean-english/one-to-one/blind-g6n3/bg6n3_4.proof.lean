open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness ControlStack.SC26Liveness.Concrete ControlStack.SC26LossyLiveness ControlStack.SC26LossyHalt

theorem legal_rounds (R : Roles) (rounds : List (List LOp × List LOp)) :
    BackLegal R rounds ↔ OrigLegal R rounds := by
  unfold BackLegal OrigLegal
  constructor
  · intro h r hr o ho
    apply h o
    apply List.mem_flatten.mpr
    refine ⟨roundOps r, List.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    simp only [roundOps, List.mem_append, List.mem_cons] at *
    rcases ho with ho | ho
    · exact Or.inl ho
    · exact Or.inr (Or.inr ho)
  · intro h o ho
    obtain ⟨l, hl, ho⟩ := List.mem_flatten.mp ho
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    simp only [roundOps, List.mem_append, List.mem_cons] at ho
    rcases ho with ho | ho | ho
    · exact h r hr o (List.mem_append_left _ ho)
    · subst o; trivial
    · exact h r hr o (List.mem_append_right _ ho)

theorem fair_rounds (k : ℕ) (rounds : List (List LOp × List LOp)) :
    BackFair k rounds ↔ OrigFair k rounds := by
  constructor
  · rintro ⟨r, hr, hd⟩
    obtain ⟨j, hj, he⟩ := List.getElem_of_mem hr
    exact ⟨j, hj, he.symm ▸ hd⟩
  · rintro ⟨j, hj, hd⟩
    exact ⟨rounds[j], List.getElem_mem hj, hd⟩

theorem pointwise : Pointwise := by
  refine ⟨legal_rounds, fair_rounds, ?_⟩
  intro R cap k ops₀ d rounds post _ _ _ _ _ _ _
  unfold BackAt OrigAt
  rw [runL_append]


theorem witness : Witness := by
  refine ⟨?_, by decide, ?_, ?_, by decide, ?_, ?_⟩
  · simp [setupOps, legalL, legalC]
  · simp [BackLegal, rounds, roundOps, legalL, legalC]
  · refine ⟨([], [.base (.bankProcess 0)]), by simp [rounds], [], [], rfl, ?_⟩
    simp [DropFree]
  · simp [legalL]
  · constructor <;> decide


theorem projection : Projection := by
  intro R cap k ops₀ rounds
  constructor
  · rintro ⟨hm, hc⟩ post hp
    exact ⟨hm, hc post hp⟩
  · intro h
    exact ⟨(h [] (by simp)).1, fun post hp => (h post hp).2⟩

theorem claim : Claim := ⟨pointwise, Iff.rfl, Iff.rfl, projection⟩
