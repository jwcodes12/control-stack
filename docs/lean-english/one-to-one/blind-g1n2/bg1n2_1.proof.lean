lemma ledger_hyp (L : Type) [DecidableEq L] (tr : List (ControlStack.LifetimeLedger.Ev L)) :
    LedgerHyp L tr ↔ OrigLedgerHyp L tr := by
  constructor
  · rintro ⟨hr, hc⟩
    refine ⟨hr, ?_⟩
    intro e he ell k hk
    subst e
    exact hc ell k he
  · rintro ⟨hr, hc⟩
    exact ⟨hr, fun ell k hk => hc _ hk ell k rfl⟩

theorem claim : Claim := by
  unfold Claim
  refine ⟨?_, ?_, Iff.rfl, ?_, ?_⟩
  · intros
    constructor
    · unfold SideHyp OrigSideHyp
      tauto
    · exact Iff.rfl
  · intro p; exact ⟨Iff.rfl, Iff.rfl⟩
  · intro L _ tr
    exact ⟨ledger_hyp L tr, fun ell => Iff.rfl⟩
  · constructor
    · rintro ⟨hs, hg, ha, hv, hl⟩
      refine ⟨?_, hg, ha, hv, ?_⟩
      · intro Ω S O _ _ _ rho W c hc hc0 hmass enc dec hr he hd
        exact hs Ω S O rho W enc dec c hr he hd hc0 hc hmass
      · intro L _ tr hr hc ell
        exact hl L tr hr (fun ell k hk => hc _ hk ell k rfl) ell
    · rintro ⟨hs, hg, ha, hv, hl⟩
      refine ⟨?_, hg, ha, hv, ?_⟩
      · intro Ω S O _ _ _ rho W enc dec c hr he hd hc0 hc hmass
        exact hs rho W c hc hc0 hmass enc dec hr he hd
      · intro L _ tr hr hc ell
        apply hl tr hr _ ell
        intro e he ell k hk
        subst e
        exact hc ell k he
