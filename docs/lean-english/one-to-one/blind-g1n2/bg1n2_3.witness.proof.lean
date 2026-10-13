lemma delta_dist {A : Type} [Fintype A] [DecidableEq A] (a : A) : IsDist (delta a) := by
  constructor
  · intro x; unfold delta; split_ifs <;> norm_num
  · simp [delta]

theorem witness : Witness := by
  unfold Witness
  refine ⟨delta (), (fun _ _ => delta (fun _ => 0)), (fun _ _ => delta 0), ?_⟩
  exact ⟨delta_dist (), fun _ _ => delta_dist _, fun _ _ => delta_dist _⟩
