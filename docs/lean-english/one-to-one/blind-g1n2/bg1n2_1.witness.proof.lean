lemma delta_dist {A : Type} [Fintype A] [DecidableEq A] (a : A) : IsDist (delta a) := by
  constructor
  · intro x; unfold delta; split_ifs <;> norm_num
  · simp [delta]

theorem witness : Witness := by
  unfold Witness
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · refine ⟨delta (), (fun _ _ => delta ((fun _ => none), ())), (fun _ _ => delta 0), ?_⟩
    refine ⟨delta_dist (), fun _ _ => delta_dist _, fun _ _ => delta_dist _, ?_, ?_, ?_⟩
    · intros; norm_num
    · intros; norm_num
    · norm_num
  · constructor
    · intro e he
      have he' : e = ControlStack.LifetimeLedger.Ev.charge () 9 := by simpa using he
      rw [he']; simp [ControlStack.LifetimeLedger.Ev.isRestore]
    · intro ell k hk
      have he : ControlStack.LifetimeLedger.Ev.charge ell k = .charge () 9 := by simpa using hk
      cases he; rfl
  · norm_num [List.replicate, ControlStack.LifetimeLedger.run, ControlStack.LifetimeLedger.step,
      Function.update]
