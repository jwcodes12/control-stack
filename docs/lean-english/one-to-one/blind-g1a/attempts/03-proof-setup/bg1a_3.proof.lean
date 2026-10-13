theorem point_rows (send : Bool → Fin 65536) (decode : Fin 65536 → Bool) :
    (∀ m, ControlStack.Covert.IsDist (pointEnc send m)) ∧
    (∀ t, ControlStack.Covert.IsDist (pointDec decode t)) := by
  constructor
  · intro m
    constructor
    · intro t; simp only [pointEnc]; split_ifs <;> norm_num
    · change (∑ t : Fin 65536, if t = send m then (1 : ℝ) else 0) = 1
      rw [Finset.sum_eq_single (send m)]
      · simp
      · intro t _ ht; simp [ht]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
  · intro t
    constructor
    · intro m; simp only [pointDec]; split_ifs <;> norm_num
    · simp [pointDec, eq_comm]

theorem recovery_success (send : Bool → Fin 65536) (decode : Fin 65536 → Bool)
    (h : ∀ m, decode (send m) = m) : BackAt send decode := by
  have term : ∀ m, (∑ t, pointEnc send m t * pointDec decode t m) = 1 := by
    intro m
    rw [Finset.sum_eq_single (send m)]
    · simp [pointEnc, pointDec, h m]
    · intro t _ ht; simp [pointEnc, ht]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  unfold BackAt ControlStack.CovertNoGo.successView
  simp only [id_eq, term]
  norm_num

theorem extract_perfect (enc : Bool → Fin 65536 → ℝ) (dec : Fin 65536 → Bool → ℝ)
    (ho : OrigAt enc dec) :
    ∃ send decode,
      (∀ m, 0 < enc m (send m) ∧ dec (send m) m = 1) ∧
      (∀ m, decode (send m) = m) ∧ BackAt send decode := by
  classical
  obtain ⟨he, hd, hs⟩ := ho
  have dle : ∀ t m, dec t m ≤ 1 := by
    intro t m
    calc dec t m ≤ ∑ b, dec t b :=
           Finset.single_le_sum (fun b _ => (hd t).1 b) (Finset.mem_univ m)
         _ = 1 := (hd t).2
  have rowle : ∀ m, (∑ t, enc m t * dec t m) ≤ 1 := by
    intro m
    calc (∑ t, enc m t * dec t m) ≤ ∑ t, enc m t := by
           apply Finset.sum_le_sum
           intro t _
           exact mul_le_of_le_one_right ((he m).1 t) (dle t m)
         _ = 1 := (he m).2
  have roweq : ∀ m, (∑ t, enc m t * dec t m) = 1 := by
    have htotal : (∑ t, enc false t * dec t false) + (∑ t, enc true t * dec t true) = 2 := by
      simp only [ControlStack.CovertNoGo.successView, Fintype.card_bool,
        Nat.cast_ofNat, Fintype.sum_bool, id_eq] at hs
      linarith
    intro m
    cases m <;> linarith [rowle false, rowle true]
  have support : ∀ m, ∃ t, 0 < enc m t ∧ dec t m = 1 := by
    intro m
    have positive : ∃ t, 0 < enc m t := by
      by_contra h
      push Not at h
      have hn : (∑ t, enc m t) ≤ 0 := Finset.sum_nonpos (fun t _ => h t)
      linarith [(he m).2]
    obtain ⟨t, ht⟩ := positive
    have zero : (∑ v, enc m v * (1 - dec v m)) = 0 := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib, (he m).2, roweq m]
      ring
    have nonneg : ∀ v ∈ (Finset.univ : Finset (Fin 65536)), 0 ≤ enc m v * (1 - dec v m) :=
      fun v _ => mul_nonneg ((he m).1 v) (sub_nonneg.mpr (dle v m))
    have product : enc m t * (1 - dec t m) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg nonneg).mp zero t (Finset.mem_univ t)
    have dz : 1 - dec t m = 0 := (mul_eq_zero.mp product).resolve_left (ne_of_gt ht)
    exact ⟨t, ht, by linarith⟩
  let send : Bool → Fin 65536 := fun m => Classical.choose (support m)
  have properties : ∀ m, 0 < enc m (send m) ∧ dec (send m) m = 1 :=
    fun m => Classical.choose_spec (support m)
  have different : send false ≠ send true := by
    intro same
    have hf := (properties false).2
    have ht := (properties true).2
    rw [← same] at ht
    have norm := (hd (send false)).2
    simp only [Fintype.sum_bool] at norm
    linarith
  let decode : Fin 65536 → Bool := fun t => decide (t = send true)
  have recover : ∀ m, decode (send m) = m := by
    intro m; cases m <;> simp [decode, different]
  exact ⟨send, decode, properties, recover, recovery_success send decode recover⟩

theorem claim : Claim := by
  have originalSignature : Original := ControlStack.SC05.cap_does_not_prevent
  have embed : ∀ send decode, BackAt send decode ↔ OrigAt (pointEnc send) (pointDec decode) := by
    intro send decode
    constructor
    · intro hs
      exact ⟨(point_rows send decode).1, (point_rows send decode).2, hs⟩
    · intro ho; exact ho.2.2
  refine ⟨rfl, embed, extract_perfect, ?_⟩
  constructor
  · rintro ⟨send, decode, h⟩
    exact ⟨pointEnc send, pointDec decode, (embed send decode).mp h⟩
  · rintro ⟨enc, dec, ho⟩
    obtain ⟨send, decode, _, _, hb⟩ := extract_perfect enc dec ho
    exact ⟨send, decode, hb⟩

theorem witness : Witness := by
  have hr : ∀ m, decode01 (send01 m) = m := by
    intro m; cases m <;> decide
  exact ⟨by decide, hr, recovery_success send01 decode01 hr⟩
