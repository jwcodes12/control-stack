theorem foldl_add_eq {m : ℕ} (f : Fin m → ℚ) : ∀ (l : List (Fin m)) (acc : ℚ),
    l.foldl (fun acc i => acc + f i) acc = acc + (l.map f).sum := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons a l ih => intro acc; simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; ring

theorem sumQ_eq (m : ℕ) (f : Fin m → ℚ) : sumQ m f = ∑ i, f i := by
  rw [sumQ, foldl_add_eq, Fin.sum_univ_def, zero_add]

theorem checkUseQ_spec {N m t : ℕ}
    {rew : Fin t → Fin N → Fin m → ℚ}
    {K : Fin t → Fin N → Fin m → Fin m → ℚ}
    {adm : Fin t → Fin N → Fin m → Bool}
    {W : Fin (N + 1) → Fin m → ℚ} {s₀ : Fin m} {floor : ℚ}
    (hc : checkUseQ N m t rew K adm W s₀ floor = true) :
    0 < t ∧ floor ≤ W (Fin.last N) s₀ ∧
      (∀ s, W 0 s ≤ 0) ∧
      (∀ i s, ∃ th, adm th i s = true) ∧
      (∀ th i s, adm th i s = true → W i.succ s ≤ rew th i s +
        ∑ s', K th i s s' * W i.castSucc s') := by
  simp only [checkUseQ, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_finRange,
    forall_const, decide_eq_true_eq, sumQ_eq, Bool.ite_eq_true_distrib, Bool.true_eq,
    true_and] at hc
  rcases hc with ⟨⟨⟨⟨ht, hfloor⟩, hzero⟩, hany⟩, hrows⟩
  exact ⟨ht, hfloor, hzero, hany, fun th i s ha => by simpa [ha] using hrows th i s⟩

/-- An accepted certificate admits at least one admissible selector, so soundness is never vacuous. -/
theorem selector_exists {N m t : ℕ}
    (rew : Fin t → Fin N → Fin m → ℚ)
    (K : Fin t → Fin N → Fin m → Fin m → ℚ)
    (adm : Fin t → Fin N → Fin m → Bool)
    (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ)
    (hc : checkUseQ N m t rew K adm W s₀ floor = true) :
    ∃ θ : ℕ → List (Fin m) → Fin m → Fin t,
      ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true := by
  obtain ⟨ht, -, -, hany, -⟩ := checkUseQ_spec hc
  classical
  refine ⟨fun n _ s => if hn : n < N then Classical.choose (hany ⟨n, hn⟩ s) else ⟨0, ht⟩, ?_⟩
  intro n hn h s
  simp only [hn, dite_true]
  exact Classical.choose_spec (hany ⟨n, hn⟩ s)

/-- A passing usefulness certificate lower-bounds the expected honest reward for every admissible selector. -/
theorem checkUseQ_sound {N m t : ℕ}
    (rew : Fin t → Fin N → Fin m → ℚ)
    (K : Fin t → Fin N → Fin m → Fin m → ℚ)
    (adm : Fin t → Fin N → Fin m → Bool)
    (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ)
    (θ : ℕ → List (Fin m) → Fin m → Fin t)
    (hc : checkUseQ N m t rew K adm W s₀ floor = true)
    (hK : ∀ th i s, adm th i s = true → ∀ s', 0 ≤ K th i s s')
    (hθ : ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true) :
    (floor : ℝ) ≤ PL_TMCERTUSF1.honestValue rew K θ N s₀ [] := by
  let cert := checkUseQ_spec hc
  have hmain : ∀ n (hn : n ≤ N) s h,
      (W ⟨n, by omega⟩ s : ℝ) ≤ PL_TMCERTUSF1.honestValue rew K θ n s h := by
    intro n
    induction n with
    | zero =>
        intro hn s h
        have hz := cert.2.2.1 s
        have hzR : (W 0 s : ℝ) ≤ 0 := by exact_mod_cast hz
        simpa [PL_TMCERTUSF1.honestValue] using hzR
    | succ n ih =>
        intro hn s h
        have hlt : n < N := by omega
        let i : Fin N := ⟨n, hlt⟩
        have ha := hθ n hlt h s
        have hrow := cert.2.2.2.2 (θ n h s) i s ha
        have hrowR : (W i.succ s : ℝ) ≤ (rew (θ n h s) i s : ℝ) +
            ∑ s', (K (θ n h s) i s s' : ℝ) * (W i.castSucc s' : ℝ) := by
          exact_mod_cast hrow
        have hcont : (∑ s', (K (θ n h s) i s s' : ℝ) * (W i.castSucc s' : ℝ)) ≤
            ∑ s', (K (θ n h s) i s s' : ℝ) * PL_TMCERTUSF1.honestValue rew K θ n s' (h ++ [s]) := by
          apply Finset.sum_le_sum
          intro s' _
          apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hK (θ n h s) i s ha s')
          have hi : i.castSucc = ⟨n, by omega⟩ := by ext; rfl
          rw [hi]
          exact ih (by omega) s' (h ++ [s])
        have hstep := add_le_add_left hcont (rew (θ n h s) i s : ℝ)
        have hstep' : (rew (θ n h s) i s : ℝ) +
            ∑ s', (K (θ n h s) i s s' : ℝ) * (W i.castSucc s' : ℝ) ≤
            (rew (θ n h s) i s : ℝ) +
            ∑ s', (K (θ n h s) i s s' : ℝ) * PL_TMCERTUSF1.honestValue rew K θ n s' (h ++ [s]) := by
          simpa [add_comm] using hstep
        have hidx : i.succ = ⟨n + 1, by omega⟩ := by ext; rfl
        rw [hidx] at hrowR
        simpa [PL_TMCERTUSF1.honestValue, hlt, i] using hrowR.trans hstep'
  have hN := hmain N (le_refl N) s₀ []
  have hfloor := cert.2.1
  have hfloorR : (floor : ℝ) ≤ (W (Fin.last N) s₀ : ℝ) := by exact_mod_cast hfloor
  have hidx : (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) = Fin.last N := by ext; rfl
  rw [hidx] at hN
  exact hfloorR.trans hN

theorem claim : PL_TMCERTUSF1.Claim := ⟨@checkUseQ_spec, @selector_exists, @checkUseQ_sound⟩

theorem witness : PL_TMCERTUSF1.Witness := by
  unfold PL_TMCERTUSF1.Witness
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [PL_TMCERTUSF1.checkUseQ, PL_TMCERTUSF1.sumQ, List.finRange_succ, PL_TMCERTUSF1.wRew,
      PL_TMCERTUSF1.wK, PL_TMCERTUSF1.wAdm, PL_TMCERTUSF1.wW, Fin.succ, Fin.castSucc]
    norm_num
  · decide
  · simp [PL_TMCERTUSF1.sumQ, List.finRange_succ, PL_TMCERTUSF1.wK, PL_TMCERTUSF1.wAdm,
      Fin.forall_fin_two]
  · decide
  · refine ⟨by simp [PL_TMCERTUSF1.wRew], by decide, by decide⟩
