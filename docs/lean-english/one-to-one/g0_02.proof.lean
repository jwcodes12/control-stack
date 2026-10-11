open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 constructor
 · intro d e h
   exact Or.inl h
 · exact ⟨clean,⟨2,4,true,false,true⟩,Or.inr rfl,by decide⟩
theorem witness : Witness := clean_accepted
