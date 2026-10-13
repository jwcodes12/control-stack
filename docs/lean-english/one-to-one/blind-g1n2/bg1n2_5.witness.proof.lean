lemma delta_dist {A : Type} [Fintype A] [DecidableEq A] (a : A) : IsDist (delta a) := by
  constructor
  · intro x; unfold delta; split_ifs <;> norm_num
  · simp [delta]

theorem witness : Witness := by
  unfold Witness
  refine ⟨delta (), (fun _ _ _ _ => 1 / 2), (fun _ _ => delta 0), ?_⟩
  refine ⟨by norm_num, delta_dist (), fun _ _ => delta_dist _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; norm_num
  · intros; norm_num
  · norm_num
  · intros; intro h o; simp
  · intros; simp
  · intros; simp
