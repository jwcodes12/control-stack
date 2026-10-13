open Finset ControlStack.MonitorCollusion ControlStack.Covert ControlStack.Leakage
theorem seed_eq {M V : Type} [Fintype M] [Fintype V] [DecidableEq M]
    (K : ℕ) (canon : V → Fin K) (enc : M → V → ℝ) (dec : Fin K → M → ℝ) :
    BackSeed K canon enc dec = OrigSeed K canon enc dec := by
  simp [BackSeed, OrigSeed, Finset.mul_sum]

theorem claim : Claim := by
  classical
  constructor
  · intro M V _ _ _ K canon enc dec
    rw [seed_eq, div_eq_mul_inv]
  · constructor
    · intro hb M V _ _ _ _ K canon enc he dec hd
      have h := hb Unit M V K canon (fun _ => 1) (fun _ => enc) (fun _ => dec)
        (by norm_num [IsDist]) (fun _ => he) (fun _ => hd)
      simp only [successProb, Fintype.univ_unit, Finset.sum_singleton, one_mul] at h
      change BackSeed K canon enc dec ≤ (K:ℝ)/(Fintype.card M:ℝ) at h
      simpa only [seed_eq, div_eq_mul_inv] using h
    · intro ho Ω M V _ _ _ _ K canon ρ enc dec hρ he hd
      change (∑ ω, ρ ω * BackSeed K canon (enc ω) (dec ω)) ≤ (K:ℝ)/(Fintype.card M:ℝ)
      calc
        _ ≤ ∑ ω, ρ ω * ((K:ℝ)*(Fintype.card M:ℝ)⁻¹) := by
          apply Finset.sum_le_sum
          intro ω _
          apply mul_le_mul_of_nonneg_left _ (hρ.1 ω)
          rw [seed_eq]
          exact ho M V K canon (enc ω) (he ω) (dec ω) (hd ω)
        _ = _ := by rw [← Finset.sum_mul, hρ.2, one_mul, div_eq_mul_inv]

theorem witness : Witness := by
  unfold Witness
  norm_num [IsDist, successProb, Fintype.sum_bool]
