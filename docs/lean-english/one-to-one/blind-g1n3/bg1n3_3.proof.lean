open ControlStack.SC07Exfil

theorem original_signature : ∀ (b : List ℕ) (c : ℕ → ℝ), 800000000000 ≤ (capped 8000000000 b).sum → (∀ i, (5 / 100 : ℝ) ≤ c i ∧ c i ≤ 1) → OriginalAt b c := by
  intro b c hS hc
  exact datacenter_example c (by norm_num at hc ⊢; exact hc) b hS

theorem claim : Claim := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro h b c hS hc
      exact ⟨h.1, h.2 b c hS hc⟩
    · intro h
      refine ⟨by norm_num [ceilDiv], ?_⟩
      intro b c hS hc
      exact (h b c hS hc).2
  · intro b c hS hc
    norm_num [BackAt, OriginalAt]

theorem witness : Witness := by norm_num [Witness, capped, List.sum_replicate]
