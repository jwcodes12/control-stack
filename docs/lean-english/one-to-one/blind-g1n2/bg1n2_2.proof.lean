theorem componentwise : ComponentwiseClaim := by
  unfold ComponentwiseClaim
  classical
  intro C L Ω M R S _ _ _ _ _ _ slots valid rho enc dec
  refine ⟨Iff.rfl, ?_⟩
  unfold BackConclusion OrigConclusion successProb ControlStack.GatewayModel.push
  have hp : ∀ omega m,
      (∑ v, (∑ tr, if finalView (runG valid (init (S := S) (slots := slots)) (List.ofFn tr)) = v
        then enc omega m tr else 0) * dec omega v m) =
      ∑ tr, enc omega m tr * dec omega (finalView (runG valid (init (S := S) (slots := slots)) (List.ofFn tr))) m := by
    intro omega m
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro tr _
    simp
  simp_rw [hp]

lemma back_shape : FrozenBack ↔ BackSchema := by
  constructor
  · intro hf
    intro C L Ω M R S _ _ _ _ _ _ slots valid rho enc dec
    rintro ⟨hr, he, hd⟩
    exact hf C L Ω M R S slots valid rho enc dec hr he hd
  · intro hf
    intro C L Ω M R S _ _ _ _ _ _ slots valid rho enc dec hr he hd
    exact hf C L Ω M R S slots valid rho enc dec ⟨hr, he, hd⟩

lemma original_shape : Original ↔ OrigSchema := by
  classical
  constructor
  · intro hf
    intro C L Ω M R S _ _ _ _ _ _ slots valid rho enc dec
    rintro ⟨hr, he, hd⟩
    exact hf valid L rho enc dec hr he hd
  · intro hf
    intro C R S slots Ω M _ _ _ _ _ _ _ valid L rho enc dec hr he hd
    exact hf C L Ω M R S slots valid rho enc dec ⟨hr, he, hd⟩

theorem pointwise : PointwiseClaim := by
  refine ⟨componentwise, ?_⟩
  intro C L Ω M R S _ _ _ _ _ _ slots valid rho enc dec
  obtain ⟨hh, hc⟩ := componentwise C L Ω M R S slots valid rho enc dec
  exact ⟨fun hb ho => hc.mp (hb (hh.mpr ho)), fun ho hb => hc.mpr (ho (hh.mp hb))⟩

theorem claim : Claim := ⟨back_shape, original_shape, pointwise⟩
