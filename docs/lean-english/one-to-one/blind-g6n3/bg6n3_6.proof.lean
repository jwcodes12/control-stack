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

theorem fair_rounds (R : Roles) (cap k : ℕ) (start : TSt)
    (rounds : List (List LOp × List LOp)) :
    BackFair R cap k start rounds ↔ OrigFair R cap k start rounds := by
  constructor
  · rintro ⟨before, r, after, hs, hd⟩
    subst rounds
    refine ⟨before.length, by simp, ?_⟩
    simpa using hd
  · rintro ⟨j, hj, hd⟩
    refine ⟨rounds.take j, rounds[j], rounds.drop (j + 1), ?_, hd⟩
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]

theorem pointwise : Pointwise := by
  refine ⟨legal_rounds, fair_rounds, ?_⟩
  intro R cap k ops₀ rounds post _ _ _ _
  unfold BackAt OrigAt
  rw [runT_append]


theorem nonvacuity : Nonvacuity := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [setupOps, legalL, legalC]
  · simp [BackLegal, pcRound, roundOps, legalL, legalC]
  · refine ⟨[], pcRound, [], rfl, ?_⟩
    have hs : runT R0 10 tinit setupOps = tLogged := by decide
    change DeliversT R0 10 0 (runT R0 10 tinit setupOps) pcRound
    rw [hs]
    exact per_copy_weaker.2.1
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

theorem fairness_audit : FairnessAudit := by
  refine ⟨per_copy_weaker.1, ?_, by decide, ?_, ?_⟩
  · simp [ackOps, setupOps, legalL, legalC]
  · refine ⟨[], [], rfl, ?_⟩
    simp [DropFree]
  · have hb : batch R0 10 ackStart (.base .recover) = [] := by decide
    unfold DeliversT
    change ¬ ∃ e ∈ batch R0 10 ackStart (.base .recover), e.2.1 = 0 ∧ _
    rw [hb]
    simp

theorem witness : Witness := ⟨nonvacuity, fairness_audit⟩
