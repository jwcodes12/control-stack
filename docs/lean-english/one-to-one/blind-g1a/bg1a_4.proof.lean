open ControlStack.SC05

theorem claim : Claim := by
  have originalSignature : ∀ (Ω M V : Type) [Fintype Ω] [Fintype M] [Fintype V] (ρ : Ω → ℝ) (out : Ω → V → ℝ) (dec : Ω → V → M → ℝ) (_hρ : ControlStack.Covert.IsDist ρ) (_ho : ∀ ω, ControlStack.Covert.IsDist (out ω)) (_hd : ∀ ω v, ControlStack.Covert.IsDist (dec ω v)), OrigAt Ω M V ρ out dec := @ControlStack.SC05.zero_dependence_is_blind
  exact ⟨rfl, by intros; exact Iff.rfl⟩

theorem witness : Witness := by
  norm_num [Witness, ControlStack.Covert.IsDist, ControlStack.Covert.successProb, Fintype.sum_bool]
