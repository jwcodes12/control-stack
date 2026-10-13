theorem original_type : OrigClosed := @ControlStack.SC16Disjoint.sc16_safe_disjoint

theorem hypotheses_iff (h : ℕ → ℕ) (s : St) : HypBack h s ↔ HypOrig h s := by
  have members (c : ℕ) : c ∈ Contents s ↔
      (∃ e ∈ s.deployed, e.content = c) ∨ ∃ rv ∈ s.reviews, rv.content = c := by
    simp [Contents, List.mem_map]
  unfold HypBack HypOrig Set.InjOn
  constructor
  · intro hb x hx y hy hxy
    exact hb x y ((members x).mpr hx) ((members y).mpr hy) hxy
  · intro ho x y hx hy hxy
    exact ho ((members x).mp hx) ((members y).mp hy) hxy
theorem claim : Claim := ⟨Iff.rfl, hypotheses_iff, fun _ _ => Iff.rfl⟩
theorem witness : Witness := by
  refine ⟨?_, ?_, (fun _ _ _ _ h => h), ?_⟩
  · simp [HRev, R0]
  · simp [HApp, R0]
  · decide
