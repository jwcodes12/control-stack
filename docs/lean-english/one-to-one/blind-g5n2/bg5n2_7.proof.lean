open ControlStack ControlStack.AuthInstances ControlStack.AuthenticatedLog
theorem claim : Claim := by
  refine ⟨rfl, ?_⟩
  intro P U ops _
  constructor
  · rintro ⟨hg, hc⟩
    refine ⟨hg, ?_⟩
    intro cf hcf
    obtain ⟨c, hu, hn, he, hm⟩ := hc cf hcf
    exact ⟨c, SC23.Op.confirm c cf.n cf.tool cf.vals, hm, hn, rfl, he, hu⟩
  · rintro ⟨hg, hc⟩
    refine ⟨hg, ?_⟩
    intro cf hcf
    obtain ⟨c, o, hm, hn, ho, he, hu⟩ := hc cf hcf
    subst o
    exact ⟨c, hu, hn, he, hm⟩

theorem witness : Witness := by
  unfold Witness
  constructor
  · simp [SC23.P0]
  · decide
