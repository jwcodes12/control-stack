open ControlStack.AuthInstances ControlStack.SC25 ControlStack.AuthenticatedLog

theorem singleton_bridge (ids : List ℕ) (guarded : List Exec) (hl : ids.length = 1) : Back ids guarded ↔ Orig ids guarded := by
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hl
  simp [Back, Orig, eq_comm]

theorem no_guard (ops : List (ℕ × Op)) (s : St) :
    authRun (step R0 id cls0 full) (fun _ => none) s ops = run R0 id cls0 full s (ops.map Prod.snd) := by
  rw [authRun_eq]
  simp [ControlStack.Authenticated.applied, ControlStack.Authenticated.Authentic, run]

theorem claim : Claim := by
  refine ⟨rfl, singleton_bridge, ?_, ?_⟩
  · decide
  · rw [no_guard]
    exact singleton_bridge _ _ (by decide)

theorem witness : Witness := by
  unfold Witness
  decide
