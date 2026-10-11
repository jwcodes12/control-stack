open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 constructor
 · intro d h
   exact ⟨h.basic,h.roles,fun a ha b hb ne eq => (h.identities a ha b hb ne).mp eq,h.runtime,h.writers,h.bypass⟩
 · exact ⟨by unfold Back IdentityEnglish; decide,by decide⟩
theorem witness : Witness := clean_accepted
