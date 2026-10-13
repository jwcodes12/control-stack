Original signatures inspected only after typed/HASHES.json was saved.

Claim 1: `ControlStack/Scenarios/EvalIntegrity.lean`:218

```lean
theorem sc21_safe (E : Env) (ops : List Op) : ∀ p ∈ (run E full init ops).published, PubOk E p
```

Claim 2: `ControlStack/Scenarios/EvalIntegrity.lean`:314

```lean
theorem sc21_undetected_prob (rep truth : Fin N → ℕ) {B k : ℕ} (hk : (corrupt rep truth).card = k) :
    survival (randomSchedules N B) (corrupt rep truth) = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
```

Claim 3: `ControlStack/Scenarios/EvalIntegrity.lean`:318

```lean
theorem sc21_undetected_le_pow (rep truth : Fin N → ℕ) {B k : ℕ} (hN : 0 < N) (hB : B ≤ N)
    (hk : (corrupt rep truth).card = k) :
    survival (randomSchedules N B) (corrupt rep truth) ≤ (((N : ℝ) - B) / N) ^ k
```

Claim 4: `ControlStack/Scenarios/EvalIntegrity.lean`:330

```lean
theorem observable_sample_nogo {B k : ℕ} (S : Finset (Fin N)) (hS : S.card = B) (hk : k ≤ N - B) :
    ∃ A : Finset (Fin N), A.card = k ∧ Disjoint S A ∧ survival {S} A = 1
```

Claim 5: `ControlStack/Scenarios/EvalIntegrityAdaptive.lean`:47

```lean
theorem sc21_adaptive (k B : ℕ) (hB : B ≤ N) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) :
    ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) *
      val (hiddenK σ S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
```

Claim 6: `ControlStack/Scenarios/EvalIntegrityAdaptive.lean`:55

```lean
theorem sc21_adaptive_content {Y : Type} [Fintype Y] (k B : ℕ) (hB : B ≤ N)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z)
    (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1)
    (hmarg : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h (a : Bool),
      ∑ y, ∑ c : Bool, K S h (y, (a, (), c)) ≤ σ (h.map Prod.snd) a) :
    ∑ S : Finset (Fin N), pU N B S * val (K S) (successInd k S) N []
      ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
```

Claim 7: `ControlStack/Scenarios/EvalIntegrityAdaptive.lean`:68

```lean
theorem sc21_adaptive_recall {Y : Type} [Fintype Y] (k B : ℕ) (hB : B ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z)
    (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1)
    (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h (a : Bool),
      ∑ y, K S h (y, (a, (), false)) ≤
        σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) :
    ∑ S : Finset (Fin N), pU N B S * val (K S) (recallSucc (N := N) k) N [] ≤ hypMiss N B k r
```

Claim 8: `ControlStack/Scenarios/EvalIntegrity.lean`:337

```lean
theorem sc22_unreplicated_misreport (rep truth : Fin N → ℕ) {B k : ℕ} (hk : (corrupt rep truth).card = k) :
    survival (randomSchedules N B) (corrupt rep truth) = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
```

Claim 9: `ControlStack/Scenarios/SC23Injection.lean`:300

```lean
theorem sc23_safe (P : Policy) (ops : List Op) : Good P (run P full init ops)
```

Claim 10: `ControlStack/Scenarios/SC23Injection.lean`:315

```lean
theorem halt_freezes (P : Policy) (s : St) (ops : List Op) (hh : s.halted = true) : run P full s ops = s
```
