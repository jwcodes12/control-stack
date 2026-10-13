open ControlStack
open ControlStack.SC16Refinement

theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_, ?_⟩
  · intro h s
    have mem_iff (c : ℕ) :
        c ∈ s.deployed.map SC16.Dep.content ++ s.reviews.map SC16.Review.content ↔
        (∃ e ∈ s.deployed, e.content = c) ∨ ∃ rv ∈ s.reviews, rv.content = c := by
      simp [List.mem_map, eq_comm]
    constructor
    · intro hb x hx y hy hxy
      exact hb x ((mem_iff x).mpr hx) y ((mem_iff y).mpr hy) hxy
    · intro ho x hx y hy hxy
      exact ho ((mem_iff x).mp hx) ((mem_iff y).mp hy) hxy
  · intro R s
    constructor
    · intro hb e he
      obtain ⟨rv, hr, heq, hrole, hneq⟩ := hb e he
      exact ⟨rv, hr, heq.symm, hrole, hneq⟩
    · intro ho e he
      obtain ⟨rv, hr, heq, hrole, hneq⟩ := ho e he
      exact ⟨rv, hr, heq.symm, hrole, hneq⟩

theorem witness : Witness := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy heq
    exact heq
  · decide
