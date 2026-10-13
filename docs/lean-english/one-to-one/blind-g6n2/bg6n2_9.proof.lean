open ControlStack.SC26
open ControlStack.SC26Authenticated ControlStack.Authenticated ControlStack.Gate
open ControlStack.AuthenticatedAdv
theorem original_signature : OrigEnvelope := by
  intro R cap U hon ops ha hu hg hh
  exact sc26_consent_from_honest_script R cap U hon ops ha hu hg hh
theorem hypotheses_agree : HypAgreement := by
  intro R U ops
  constructor
  · constructor
    · intro h u hu ha; exact h u ha hu
    · intro h a ha hu; exact h a hu ha
  · constructor
    · intro h io hio c k tx heq
      have hi := h io hio
      rw [heq] at hi
      exact hi
    · intro h io hio
      cases ho : io.2 with
      | bankCall c k tx => exact h io hio c k tx ho
      | _ => trivial
theorem claim : Claim := by
  refine ⟨Iff.rfl, ⟨?_, hypotheses_agree⟩⟩
  intro R cap hon s
  exact Iff.rfl
theorem witness : Witness := by
  unfold Witness
  refine ⟨?_, by simp [R0], by simp [R0], by simp [BankHyp, honScript], by decide⟩
  refine ⟨advScript, by decide, ?_⟩
  exact .right _ (.left _ (.right _ (.right _ (.right _ .nil))))
