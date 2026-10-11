open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 constructor
 · intro d e h
   exact Or.inl h
 · exact ⟨clean,⟨2,4,true,false,true⟩,Or.inr rfl,by unfold Orig; decide⟩
theorem witness : Witness := clean_accepted

theorem equivalent_on_accepted (d : IR) (e : Edge) (h : Accepted d) (member : e ∈ d.edges) (authority : e.authority = true) (sink : e.target = d.sink) : Back d e ↔ Orig d e := ⟨fun _ => exclusive_sink d h e member authority sink,Or.inl⟩
