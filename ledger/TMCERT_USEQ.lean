namespace PL_TMCERTUSF1

def sumQ (m : ℕ) (f : Fin m → ℚ) : ℚ :=
  (List.finRange m).foldl (fun acc i => acc + f i) 0

def checkUseQ (N m t : ℕ)
    (rew : Fin t → Fin N → Fin m → ℚ)
    (K : Fin t → Fin N → Fin m → Fin m → ℚ)
    (adm : Fin t → Fin N → Fin m → Bool)
    (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ) : Bool :=
  decide (0 < t) && decide (floor ≤ W (Fin.last N) s₀) &&
  (List.finRange m).all (fun s => decide (W 0 s ≤ 0)) &&
  (List.finRange N).all (fun i => (List.finRange m).all (fun s =>
    (List.finRange t).any (fun th => adm th i s))) &&
  (List.finRange t).all (fun th => (List.finRange N).all (fun i =>
    (List.finRange m).all (fun s =>
      if adm th i s then decide (W i.succ s ≤ rew th i s +
        sumQ m (fun s' => K th i s s' * W i.castSucc s')) else true)))

noncomputable def honestValue {N m t : ℕ}
    (rew : Fin t → Fin N → Fin m → ℚ)
    (K : Fin t → Fin N → Fin m → Fin m → ℚ)
    (θ : ℕ → List (Fin m) → Fin m → Fin t) : ℕ → Fin m → List (Fin m) → ℝ
  | 0, _, _ => 0
  | n + 1, s, h => if hn : n < N then
      (rew (θ n h s) ⟨n, hn⟩ s : ℝ) +
        ∑ s', (K (θ n h s) ⟨n, hn⟩ s s' : ℝ) * honestValue rew K θ n s' (h ++ [s])
    else 0

def Claim : Prop :=
  (∀ {N m t : ℕ} {rew : Fin t → Fin N → Fin m → ℚ}
    {K : Fin t → Fin N → Fin m → Fin m → ℚ}
    {adm : Fin t → Fin N → Fin m → Bool}
    {W : Fin (N + 1) → Fin m → ℚ} {s₀ : Fin m} {floor : ℚ},
    checkUseQ N m t rew K adm W s₀ floor = true →
      0 < t ∧ floor ≤ W (Fin.last N) s₀ ∧ (∀ s, W 0 s ≤ 0) ∧
        (∀ i s, ∃ th, adm th i s = true) ∧
        (∀ th i s, adm th i s = true → W i.succ s ≤ rew th i s +
          ∑ s', K th i s s' * W i.castSucc s')) ∧
  (∀ {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ)
    (K : Fin t → Fin N → Fin m → Fin m → ℚ)
    (adm : Fin t → Fin N → Fin m → Bool)
    (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ),
    checkUseQ N m t rew K adm W s₀ floor = true →
      ∃ θ : ℕ → List (Fin m) → Fin m → Fin t,
        ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true) ∧
  (∀ {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ)
    (K : Fin t → Fin N → Fin m → Fin m → ℚ)
    (adm : Fin t → Fin N → Fin m → Bool)
    (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ)
    (θ : ℕ → List (Fin m) → Fin m → Fin t),
    checkUseQ N m t rew K adm W s₀ floor = true →
    (∀ th i s, adm th i s = true → ∀ s', 0 ≤ K th i s s') →
    (∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true) →
      (floor : ℝ) ≤ honestValue rew K θ N s₀ [])

def wRew : Fin 2 → Fin 2 → Fin 2 → ℚ :=
  fun th _ s => if s.val = 0 then (if th.val = 0 then 2 else 3) else 0

def wK : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℚ :=
  fun th _ s s' => if s.val = 0 ∧ th.val = 0 then (if s'.val = 0 then 1 else 0)
    else (if s'.val = 1 then 1 else 0)

def wAdm : Fin 2 → Fin 2 → Fin 2 → Bool :=
  fun th _ s => decide (th.val = 0 ∨ s.val = 0)

def wW : Fin 3 → Fin 2 → ℚ :=
  fun i s => if s.val = 0 then (if i.val = 0 then 0 else if i.val = 1 then 2 else 3) else 0

def Witness : Prop :=
  checkUseQ 2 2 2 wRew wK wAdm wW ⟨0, by omega⟩ 3 = true ∧
  (∀ th i s, wAdm th i s = true → ∀ s', 0 ≤ wK th i s s') ∧
  (∀ th i s, wAdm th i s = true → sumQ 2 (wK th i s) = 1) ∧
  (∀ i s, wAdm 0 i s = true) ∧
  (0 < wRew 1 0 0 ∧ wAdm 1 0 0 = true ∧ wAdm 1 0 1 = false)

end PL_TMCERTUSF1
