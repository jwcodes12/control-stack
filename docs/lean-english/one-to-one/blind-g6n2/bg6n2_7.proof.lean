open ControlStack.SC26
open ControlStack.SC26Authenticated ControlStack.Authenticated ControlStack.Gate
open ControlStack.AuthenticatedAdv
theorem original_signature : OrigEnvelope := by
  intro R cap U ops hu hg
  exact sc26_safe_authenticated R cap U ops hu hg
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
  intro R cap U ops s
  exact Iff.rfl
theorem witness : Witness := by
  unfold Witness
  exact ⟨by simp [R0], by simp [BankHyp, honestTrace], by decide⟩
