/- A rational lower-bound checker for finite-horizon honest usefulness. -/
import ControlStack.RefinementProof

namespace ControlStack.UseQ

def sumQ (m : ℕ) (f : Fin m → ℚ) : ℚ :=
  (List.finRange m).foldl (fun acc i => acc + f i) 0

def checkUseQ (N m t : ℕ)
    (rew : Fin t → Fin N → Fin m → ℚ)
    (K : Fin t → Fin N → Fin m → Fin m → ℚ)
    (adm : Fin t → Fin N → Fin m → Bool)
    (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ) : Bool :=
  decide (0 < t) && decide (floor ≤ W (Fin.last N) s₀) &&
  (List.finRange m).all (fun s => decide (W 0 s ≤ 0)) &&
  (List.finRange t).all (fun th => (List.finRange N).all (fun i =>
    (List.finRange m).all (fun s =>
      if adm th i s then decide (W i.succ s ≤ rew th i s +
        sumQ m (fun s' => K th i s s' * W i.castSucc s')) else true)))

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
      (∀ th i s, adm th i s = true → W i.succ s ≤ rew th i s +
        ∑ s', K th i s s' * W i.castSucc s') := by
  simp only [checkUseQ, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const, decide_eq_true_eq, sumQ_eq, Bool.ite_eq_true_distrib] at hc
  rcases hc with ⟨⟨⟨ht, hfloor⟩, hzero⟩, hrows⟩
  exact ⟨ht, hfloor, hzero, fun th i s ha => by simpa [ha] using hrows th i s⟩

noncomputable def honestValue {N m t : ℕ}
    (rew : Fin t → Fin N → Fin m → ℚ)
    (K : Fin t → Fin N → Fin m → Fin m → ℚ)
    (θ : ℕ → List (Fin m) → Fin m → Fin t) : ℕ → Fin m → List (Fin m) → ℝ
  | 0, _, _ => 0
  | n + 1, s, h => if hn : n < N then
      (rew (θ n h s) ⟨n, hn⟩ s : ℝ) +
        ∑ s', (K (θ n h s) ⟨n, hn⟩ s s' : ℝ) * honestValue rew K θ n s' (h ++ [s])
    else 0

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
    (floor : ℝ) ≤ honestValue rew K θ N s₀ [] := by
  let cert := checkUseQ_spec hc
  have hmain : ∀ n (hn : n ≤ N) s h,
      (W ⟨n, by omega⟩ s : ℝ) ≤ honestValue rew K θ n s h := by
    intro n
    induction n with
    | zero =>
        intro hn s h
        have hz := cert.2.2.1 s
        have hzR : (W 0 s : ℝ) ≤ 0 := by exact_mod_cast hz
        simpa [honestValue] using hzR
    | succ n ih =>
        intro hn s h
        have hlt : n < N := by omega
        let i : Fin N := ⟨n, hlt⟩
        have ha := hθ n hlt h s
        have hrow := cert.2.2.2 (θ n h s) i s ha
        have hrowR : (W i.succ s : ℝ) ≤ (rew (θ n h s) i s : ℝ) +
            ∑ s', (K (θ n h s) i s s' : ℝ) * (W i.castSucc s' : ℝ) := by
          exact_mod_cast hrow
        have hcont : (∑ s', (K (θ n h s) i s s' : ℝ) * (W i.castSucc s' : ℝ)) ≤
            ∑ s', (K (θ n h s) i s s' : ℝ) * honestValue rew K θ n s' (h ++ [s]) := by
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
            ∑ s', (K (θ n h s) i s s' : ℝ) * honestValue rew K θ n s' (h ++ [s]) := by
          simpa [add_comm] using hstep
        have hidx : i.succ = ⟨n + 1, by omega⟩ := by ext; rfl
        rw [hidx] at hrowR
        simpa [honestValue, hlt, i] using hrowR.trans hstep'
  have hN := hmain N (le_refl N) s₀ []
  have hfloor := cert.2.1
  have hfloorR : (floor : ℝ) ≤ (W (Fin.last N) s₀ : ℝ) := by exact_mod_cast hfloor
  have hidx : (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) = Fin.last N := by ext; rfl
  rw [hidx] at hN
  exact hfloorR.trans hN

def Claim : Prop :=
  (∀ {N m t : ℕ} {rew : Fin t → Fin N → Fin m → ℚ}
    {K : Fin t → Fin N → Fin m → Fin m → ℚ}
    {adm : Fin t → Fin N → Fin m → Bool}
    {W : Fin (N + 1) → Fin m → ℚ} {s₀ : Fin m} {floor : ℚ},
    checkUseQ N m t rew K adm W s₀ floor = true →
      0 < t ∧ floor ≤ W (Fin.last N) s₀ ∧ (∀ s, W 0 s ≤ 0) ∧
        (∀ th i s, adm th i s = true → W i.succ s ≤ rew th i s +
          ∑ s', K th i s s' * W i.castSucc s')) ∧
  (∀ {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ)
    (K : Fin t → Fin N → Fin m → Fin m → ℚ)
    (adm : Fin t → Fin N → Fin m → Bool)
    (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ)
    (θ : ℕ → List (Fin m) → Fin m → Fin t),
    checkUseQ N m t rew K adm W s₀ floor = true →
    (∀ th i s, adm th i s = true → ∀ s', 0 ≤ K th i s s') →
    (∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true) →
      (floor : ℝ) ≤ honestValue rew K θ N s₀ [])

theorem claim : Claim := ⟨@checkUseQ_spec, @checkUseQ_sound⟩

def Witness : Prop :=
  checkUseQ 1 1 1 (fun _ _ _ => (1 : ℚ)) (fun _ _ _ _ => 0)
    (fun _ _ _ => true) (fun i _ => if i.val = 0 then 0 else 1)
    ⟨0, by omega⟩ 1 = true

theorem witness : Witness := by
  change checkUseQ 1 1 1 (fun _ _ _ => (1 : ℚ)) (fun _ _ _ _ => 0)
    (fun _ _ _ => true) (fun i _ => if i.val = 0 then 0 else 1)
    ⟨0, by omega⟩ 1 = true
  norm_num [checkUseQ, sumQ, List.finRange, Fin.cases, Fin.last]

#print axioms claim
#print axioms witness

end ControlStack.UseQ
