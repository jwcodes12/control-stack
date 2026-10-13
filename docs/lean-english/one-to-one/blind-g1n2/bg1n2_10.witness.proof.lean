lemma delta_dist {A : Type} [Fintype A] [DecidableEq A] (a : A) : IsDist (delta a) := by
  constructor
  · intro x; unfold delta; split_ifs <;> norm_num
  · simp [delta]

theorem witness : Witness := by
  unfold Witness
  have hb : BackHyp 2 1 1 1 (1 / 2) Unit sigmaSub (testK sigmaSub) := by
    refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
    · intros; norm_num [sigmaSub]
    · intros; norm_num [sigmaSub, Fintype.sum_bool]
    · intro sched hs h z
      unfold testK sigmaSub
      split_ifs <;> norm_num
    · intro sched hs h
      simp only [testK, sigmaSub, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.univ_unit, Finset.sum_singleton]
      by_cases hm : memN sched h.length <;> norm_num [hm]
    · intro sched hs h a
      simp only [testK, sigmaSub, Fintype.univ_unit, Finset.sum_singleton]
      norm_num
  have hn : OrigHyp 2 1 1 1 (1 / 2) Unit sigmaNorm (testK sigmaNorm) := by
    refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
    · intros; norm_num [sigmaNorm, IsDist, Fintype.sum_bool]
    · intro sched hs h z
      unfold testK sigmaNorm
      split_ifs <;> norm_num
    · intro sched hs h
      simp only [testK, sigmaNorm, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.univ_unit, Finset.sum_singleton]
      by_cases hm : memN sched h.length <;> norm_num [hm]
    · intro sched hs h a
      simp only [testK, sigmaNorm, Fintype.univ_unit, Finset.sum_singleton]
      norm_num
  refine ⟨hb, ?_, by norm_num [sigmaSub], by norm_num [sigmaSub, Fintype.sum_bool], hn⟩
  intro ho
  have hs := ho.2.2.2.1 []
  have he := hs.2
  norm_num [sigmaSub, Fintype.sum_bool] at he
