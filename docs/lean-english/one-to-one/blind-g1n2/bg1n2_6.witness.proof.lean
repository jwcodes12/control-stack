lemma delta_dist {A : Type} [Fintype A] [DecidableEq A] (a : A) : IsDist (delta a) := by
  constructor
  · intro x; unfold delta; split_ifs <;> norm_num
  · simp [delta]

theorem witness : Witness := by
  unfold Witness
  refine ⟨delta (), (fun _ _ _ _ => 1 / 4), (fun _ _ => delta 0), ?_⟩
  refine ⟨delta_dist (), fun _ _ => delta_dist _, ?_, ?_⟩
  · intros; norm_num
  · intros; norm_num [Finset.sum_const, Fintype.card_prod, Fintype.card_fun]
