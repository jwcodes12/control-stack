lemma delta_dist {A : Type} [Fintype A] [DecidableEq A] (a : A) : IsDist (delta a) := by
  constructor
  · intro x; unfold delta; split_ifs <;> norm_num
  · simp [delta]

theorem witness : Witness := by
  unfold Witness
  constructor
  ·
    refine ⟨delta (), (fun _ _ _ _ => 1 / 2), (fun _ _ => delta 0), ?_⟩
    refine ⟨delta_dist (), fun _ _ => delta_dist _, ?_, ?_, ?_, ?_, ?_⟩
    · intros; norm_num
    · intros; norm_num
    · intros; norm_num
    · intros; intro h o; simp; norm_num
    · intro g; simp
  · constructor
    · refine ⟨?_, fun _ _ => delta_dist _, ?_, ?_, ?_, ?_, ?_⟩
      · constructor <;> simp
      · intros; norm_num
      · intros; norm_num
      · intros; norm_num
      · intros; intro h o; simp
      · intro g; simp
    · norm_num [ControlStack.Leakage.val, delta, Fin.sum_univ_two]
