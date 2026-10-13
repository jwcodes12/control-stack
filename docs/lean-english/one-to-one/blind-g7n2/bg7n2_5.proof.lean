open ControlStack
open ControlStack.AuthInstances
open ControlStack ControlStack.SC28
open ControlStack.AuthenticatedLog
#check (ControlStack.AuthInstances.sc28_safe_authenticated : OrigFull)

theorem claim : Claim :=
by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intro admins G Uset Ulist ops s hs hl
  have excl : ∀ c ∈ admins, c ∉ Ulist := by
    intro c hc hu
    exact hl c hu hc
  constructor
  · rintro ⟨good, leases, revoked⟩
    refine ⟨good, ?_, ?_⟩
    · intro l hm
      obtain ⟨c, hc, _, hop⟩ := leases l hm
      exact ⟨c, .issue c l.1 l.2, hop, excl c hc, rfl, hc⟩
    · intro lid hm
      obtain ⟨c, hc, _, hop⟩ := revoked lid hm
      exact ⟨c, .revoke c lid, hop, excl c hc, rfl, hc⟩
  · rintro ⟨good, leases, revoked⟩
    refine ⟨good, ?_, ?_⟩
    · intro l hm
      obtain ⟨c, o, hop, _, he, hc⟩ := leases l hm
      exact ⟨c, hc, hs c hc, he ▸ hop⟩
    · intro lid hm
      obtain ⟨c, o, hop, _, he, hc⟩ := revoked lid hm
      exact ⟨c, hc, hs c hc, he ▸ hop⟩

theorem witness : Witness :=
by
  unfold Witness
  dsimp
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp [legal]
  decide
