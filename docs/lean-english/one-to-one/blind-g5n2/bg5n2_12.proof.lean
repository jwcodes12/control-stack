open Finset ControlStack.MonitorCollusion ControlStack.Covert ControlStack.Leakage
theorem pointwise {Y O : Type} [Fintype Y] [Fintype O]
    (K : Bool → List (Y × O) → Y × O → ℝ) (L : ℝ)
    (guess : List O → Bool → ℝ) (m : ℕ) :
    (val (K false) (fun t => guess t false) m [] +
      val (K true) (fun t => guess t true) m []) / 2 ≤ L^m/2 ↔
    (∑ φ : Bool, (1/2:ℝ)*val (K φ) (fun t => guess t φ) m []) ≤ (1/2)*L^m := by
  simp only [Fintype.sum_bool]
  ring_nf

theorem claim : Claim := by
  classical
  refine ⟨fun _ _ _ _ K L guess m => pointwise K L guess m, ?_⟩
  constructor
  · intro hb Y O _ _ K c L hK hd _ hL hm guess hg m
    exact (pointwise K L guess m).1 (hb Y O K c L guess m hK hd hL hm hg)
  · intro ho Y O _ _ K c L guess m hK hd hL hm hg
    rcases isEmpty_or_nonempty Y with he | hn
    · letI := he
      cases m with
      | zero =>
        change (guess [] false + guess [] true)/2 ≤ L^0/2
        have hs := (hg []).2
        simp only [Fintype.sum_bool] at hs
        norm_num
        linarith
      | succ m =>
        simp only [ControlStack.Leakage.val, Finset.univ_eq_empty, Finset.sum_empty, zero_add, zero_div]
        exact div_nonneg (pow_nonneg hL _) (by norm_num)
    · letI := hn
      let y : Y := Classical.choice hn
      have hc : ∀ g o, 0 ≤ c g o := by
        intro g o
        have h := hd false (g.map (fun a => (y,a))) o
        have hz : 0 ≤ ∑ y', K false (g.map (fun a => (y,a))) (y',o) :=
          Finset.sum_nonneg (fun y' _ => hK false _ (y',o))
        have := hz.trans h
        simpa [List.map_map, Function.comp_def] using this
      exact (pointwise K L guess m).2 (ho Y O K c L hK hd hc hL hm guess hg m)

theorem basicWitness : BasicWitness := by
  unfold BasicWitness
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro φ h z
    unfold bscK
    split_ifs <;> norm_num
  · intro φ h o
    simp only [Dominated, Fintype.univ_unit, Finset.sum_singleton, bscK]
    split_ifs <;> norm_num
  · intro g
    norm_num [Fintype.sum_bool]
  · intro t
    norm_num [IsDist, Fintype.sum_bool]
  · norm_num


theorem witness : Witness := by
  refine ⟨basicWitness, ?_⟩
  unfold LimitWitness
  norm_num [HeavyK, HeavyC, HalfGuess, Dominated, IsDist,
    ControlStack.Leakage.val, Fintype.sum_bool]
