open ControlStack.Deployment
theorem claim : Claim := by
 intro d e h member authority sink
 exact ⟨fun _ => exclusive_sink d h e member authority sink,Or.inl⟩
theorem witness : Witness := clean_accepted
