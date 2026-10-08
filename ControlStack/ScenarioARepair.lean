import ControlStack.CovertChannel

/-! Exact-recovery design point for the five-episode repair catalog.
Runtime observation, lineage and refinement obligations remain separate. -/
namespace ControlStack.ScenarioARepair
open ControlStack.Covert

abbrev View := Option (Fin 8)
abbrev Transcript := Fin 5 → View

theorem transcript_card : Fintype.card Transcript = 59049 := by
  norm_num [Transcript, View, Fintype.card_fun, Fintype.card_option, Fintype.card_fin]

theorem repair_recovery {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ)
    (enc : Ω → Fin (2 ^ 32) → Transcript → ℝ)
    (dec : Ω → Transcript → Fin (2 ^ 32) → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) :
    successProb ρ enc dec ≤ (59049 : ℝ) / 2 ^ 32 := by
  have h := covert_bound_schema (S := View) 5 ρ enc dec hρ henc hdec
  norm_num [View, Fintype.card_option, Fintype.card_fin] at h ⊢
  exact h

theorem repair_target {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ)
    (enc : Ω → Fin (2 ^ 32) → Transcript → ℝ)
    (dec : Ω → Transcript → Fin (2 ^ 32) → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) :
    successProb ρ enc dec ≤ 1 / 2 ^ 16 := by
  calc
    successProb ρ enc dec ≤ (59049 : ℝ) / 2 ^ 32 := repair_recovery ρ enc dec hρ henc hdec
    _ ≤ 1 / 2 ^ 16 := by norm_num

#print axioms transcript_card
#print axioms repair_recovery
#print axioms repair_target
end ControlStack.ScenarioARepair
