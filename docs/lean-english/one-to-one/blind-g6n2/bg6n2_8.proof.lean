open ControlStack.SC26
open ControlStack.SC26Authenticated ControlStack.Authenticated ControlStack.Gate
theorem original_signature : OrigEnvelope := forged_approval_pays_without_auth
theorem raw_none_same (R : Roles) (cap : ℕ) (s : St) (ops : List (ℕ × Op)) :
    (authed (raw R cap) (fun _ => none)).run s ops = (raw R cap).run s (ops.map Prod.snd) := by
  induction ops generalizing s with
  | nil => rfl
  | cons io ops ih =>
    change (authed (raw R cap) (fun _ => none)).run ((raw R cap).step s io.2) ops =
      (raw R cap).run ((raw R cap).step s io.2) (ops.map Prod.snd)
    exact ih _
theorem original_to_back : OrigEnvelope → Back := by
  intro h
  change OrigAt _ _ _ at h
  unfold Back
  rw [← raw_none_same]
  exact ⟨by rw [h.1]; simp, by decide, h.2.2⟩
theorem claim : Claim := by
  refine ⟨Iff.rfl, original_to_back, ?_, ?_, ?_⟩
  · intro b guarded h
    exact ⟨by rw [h.1]; simp, by decide, h.2.2⟩
  · exact ⟨[(0, tx1), (0, tx1)], [], by simp [BackAt, forged, R0], by simp [OrigAt]⟩
  · exact ⟨[(2, Op.deliver 0)], by simp [OrigAt, R0], by simp [BackAt, R0]⟩
theorem witness : Witness := by
  unfold Witness
  decide
