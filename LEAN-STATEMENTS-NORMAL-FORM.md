# All Lean statements — source-normalized review catalog

Every indexed theorem and lemma is listed with its source statement, registry metadata and source location; no proof bodies. This is NOT kernel-elaborated normal form: inherited section variables, typeclasses, namespace elaboration, coercions and definitions can hide important premises. Run Lean #print and #print axioms for authoritative statements. No deployment assurance is implied.

Indexed declarations: 2151; UNKNOWN adversary: 2076; SOURCE_ONLY: 2110.

## ControlStack/AdaptiveBalance.lean

### 1. slope_mono

Source: ControlStack/AdaptiveBalance.lean:11 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
private lemma slope_mono (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : ∀ {n k : ℕ}, n ≤ k → slope b n ≤ slope b k
~~~

### 2. tangent_step

Source: ControlStack/AdaptiveBalance.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
private lemma tangent_step (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (m q : ℕ) (hmq : m ≤ q) : b ^ (q + 1) + ((m : ℝ) - ((q + 1 : ℕ) : ℝ)) * slope b (q + 1) ≤ b ^ q + ((m : ℝ) - (q : ℝ)) * slope b q
~~~

### 3. balanced_bound

Source: ControlStack/AdaptiveBalance.lean:39 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem balanced_bound (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (m q : ℕ) : b ^ m ≥ b ^ q + ((m : ℝ) - (q : ℝ)) * (b ^ (q + 1) - b ^ q)
~~~

### 4. aggregate_balanced_budget

Source: ControlStack/AdaptiveBalance.lean:67 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem aggregate_balanced_budget (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k q a : ℕ) (_hk : 0 < k) (ha : a < k) (counts : Fin k → ℕ) (hcounts : ∑ i : Fin k, counts i ≤ k * q + a) : ∑ i : Fin k, b ^ (counts i) ≥ ((k - a : ℕ) : ℝ) * b ^ q + (a : ℝ) * b ^ (q + 1)
~~~

### 5. aggregate_balanced_exact

Source: ControlStack/AdaptiveBalance.lean:108 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem aggregate_balanced_exact (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k n : ℕ) (hk : 0 < k) (counts : Fin k → ℕ) (hcounts : ∑ i : Fin k, counts i = n) : ∑ i : Fin k, b ^ (counts i) ≥ ((k - n % k : ℕ) : ℝ) * b ^ (n / k) + ((n % k : ℕ) : ℝ) * b ^ (n / k + 1)
~~~

## ControlStack/AdaptiveGeneric.lean

### 6. classCount_append_flag

Source: ControlStack/AdaptiveGeneric.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classCount_append_flag {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (h : Hist X Z) (x : X) (z : Z) (ω : Fin k) : classCount g (h ++ [(x, z, false)]) ω = classCount g h ω + (if g z = some ω then 1 else 0)
~~~

### 7. flagFactor

Source: ControlStack/AdaptiveGeneric.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem flagFactor {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (b : ℝ) (ω : Fin k) (z : Z) : 1 - passProb g (1-b) ω z = if g z = some ω then b else 1
~~~

### 8. passProb_bounds

Source: ControlStack/AdaptiveGeneric.lean:39 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem passProb_bounds {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ω : Fin k) (z : Z) : 0 ≤ passProb g t ω z ∧ passProb g t ω z ≤ 1
~~~

### 9. fullSurv_nonneg

Source: ControlStack/AdaptiveGeneric.lean:46 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fullSurv_nonneg {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) : ∀ n h ω, 0 ≤ fullSurv T M g t keep ω n h
~~~

### 10. fullSurv_ge_flagOnly

Source: ControlStack/AdaptiveGeneric.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fullSurv_ge_flagOnly {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) : ∀ n h ω, flagOnly T M g t keep ω n h ≤ fullSurv T M g t keep ω n h
~~~

### 11. refSurv_eq_fullSurv_zero

Source: ControlStack/AdaptiveGeneric.lean:123 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refSurv_eq_fullSurv_zero {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (keep : Hist X Z → ℝ) : ∀ n h ω, refSurv T M keep n h = fullSurv T M g 0 keep ω n h
~~~

### 12. classPower_append_flag

Source: ControlStack/AdaptiveGeneric.lean:149 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classPower_append_flag {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (b : ℝ) (h : Hist X Z) (x : X) (z : Z) (ω : Fin k) : b ^ classCount g h ω * (if g z = some ω then b else 1) = b ^ classCount g (h ++ [(x,z,false)]) ω
~~~

### 13. weightedFactor_append

Source: ControlStack/AdaptiveGeneric.lean:156 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
private theorem weightedFactor_append {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (b : ℝ) (h : Hist X Z) (x : X) (z : Z) (ω : Fin k) (f : ℝ) : b ^ classCount g (h ++ [(x,z,false)]) ω * f = b ^ classCount g h ω * ((1 - passProb g (1-b) ω z) * f)
~~~

### 14. weighted_double_sum

Source: ControlStack/AdaptiveGeneric.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem weighted_double_sum {α β : Type} [Fintype α] [Fintype β] (a : α → ℝ) (c : β → ℝ) (f : α → β → ℝ) : (∑ i, a i * ∑ j, c j * f i j) = ∑ j, c j * ∑ i, a i * f i j
~~~

### 15. weightedFlag_succ

Source: ControlStack/AdaptiveGeneric.lean:192 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem weightedFlag_succ {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (b : ℝ) (keep : Hist X Z → ℝ) (n : ℕ) (h : Hist X Z) : weightedFlag T M g b keep (n+1) h = ∑ x, T h x * ∑ z, M x z * weightedFlag T M g b keep n (h ++ [(x,z,false)])
~~~

### 16. count_sum_le

Source: ControlStack/AdaptiveGeneric.lean:279 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem count_sum_le {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (h : Hist X Z) : (∑ ω : Fin k, classCount g h ω) ≤ h.length
~~~

### 17. weightedFlag_lower

Source: ControlStack/AdaptiveGeneric.lean:321 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem weightedFlag_lower {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (N : ℕ) : ∀ n h, h.length + n = N → balancedTarget k N b * refSurv T M keep n h ≤ weightedFlag T M g b keep n h
~~~

### 18. sharp_survival

Source: ControlStack/AdaptiveGeneric.lean:385 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_survival {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : refSurv T M keep n [] = 1) : balancedTarget k n (1-t) ≤ ∑ ω : Fin k, fullSurv T M g t keep ω n []
~~~

### 19. sharp_uniform_cat

Source: ControlStack/AdaptiveGeneric.lean:415 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_uniform_cat {k : ℕ} (hkpos : 0 < k) (t : ℝ) (ht0 : 0 ≤ t) (n : ℕ) (surv cat : Fin k → ℝ) (hsurv : ∀ i, 0 ≤ surv i) (hcat : ∀ i, t ≤ cat i) (hsum : balancedTarget k n (1-t) ≤ ∑ i : Fin k, surv i) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ (1 / (k : ℝ)) * ∑ i : Fin k, surv i * cat i
~~~

### 20. seedDecoder_eq_some_iff

Source: ControlStack/AdaptiveGeneric.lean:451 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seedDecoder_eq_some_iff {X C Z : Type} [DecidableEq C] {k : ℕ} (seed : Fin k → X) (c : X → C) (g : Z → C) (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (z : Z) (i : Fin k) : seedDecoder seed c g z = some i ↔ g z = c (seed i)
~~~

### 21. seedDecoder_pass_eq

Source: ControlStack/AdaptiveGeneric.lean:481 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seedDecoder_pass_eq {X C Z : Type} [DecidableEq C] {k : ℕ} (seed : Fin k → X) (c : X → C) (g : Z → C) (t : ℝ) (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (i : Fin k) (z : Z) : passProb (seedDecoder seed c g) t i z = classPass c g t (seed i) z
~~~

### 22. refSurv_eq_passSurv_zero

Source: ControlStack/AdaptiveGeneric.lean:502 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refSurv_eq_passSurv_zero {X : Type} {Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) : ∀ n h, refSurv T M keep n h = passSurv T M (fun _ => 0) keep n h
~~~

### 23. fullSurv_eq_passSurv_seed

Source: ControlStack/AdaptiveGeneric.lean:519 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fullSurv_eq_passSurv_seed {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (seed : Fin k → X) (c : X → C) (g : Z → C) (t : ℝ) (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (keep : Hist X Z → ℝ) (i : Fin k) : ∀ n h, fullSurv T M (seedDecoder seed c g) t keep i n h = passSurv T M (classPass c g t (seed i)) keep n h
~~~

### 24. sharp_seedset_survival

Source: ControlStack/AdaptiveGeneric.lean:541 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_seedset_survival {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : refSurv T M keep n [] = 1) : balancedTarget k n (1-t) ≤ ∑ i : Fin k, passSurv T M (classPass c g t ((e i).val)) keep n []
~~~

### 25. sharp_seedset_catRisk

Source: ControlStack/AdaptiveGeneric.lean:570 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_seedset_catRisk {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : refSurv T M keep n [] = 1) (cat : Fin k → ℝ) (hcat : ∀ i, t ≤ cat i) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ (1 / (k : ℝ)) * ∑ i : Fin k, passSurv T M (classPass c g t ((e i).val)) keep n [] * cat i
~~~

## ControlStack/AdaptiveSharp.lean

### 26. weighted_path_balanced

Source: ControlStack/AdaptiveSharp.lean:17 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem weighted_path_balanced {P : Type} [Fintype P] (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k n : ℕ) (hk : 0 < k) (mass keep : P → ℝ) (counts : P → Fin k → ℕ) (hmass : ∀ p, 0 ≤ mass p) (hkeep0 : ∀ p, 0 ≤ keep p) (hbudget : ∀ p, ∑ i : Fin k, counts p i ≤ n) (haccept : ∑ p : P, mass p * keep p = 1) : ((k - n % k : ℕ) : ℝ) * b ^ (n / k) + ((n % k : ℕ) : ℝ) * b ^ (n / k + 1) ≤ ∑ p : P, mass p * keep p * ∑ i : Fin k, b ^ (counts p i)
~~~

### 27. uniform_seed_risk_balanced

Source: ControlStack/AdaptiveSharp.lean:58 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem uniform_seed_risk_balanced {P : Type} [Fintype P] (t : ℝ) (ht : 0 ≤ t) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k n : ℕ) (hk : 0 < k) (mass keep : P → ℝ) (counts : P → Fin k → ℕ) (hmass : ∀ p, 0 ≤ mass p) (hkeep0 : ∀ p, 0 ≤ keep p) (hbudget : ∀ p, ∑ i : Fin k, counts p i ≤ n) (haccept : ∑ p : P, mass p * keep p = 1) : (t / (k : ℝ)) * (((k - n % k : ℕ) : ℝ) * b ^ (n / k) + ((n % k : ℕ) : ℝ) * b ^ (n / k + 1)) ≤ (t / (k : ℝ)) * ∑ p : P, mass p * keep p * ∑ i : Fin k, b ^ (counts p i)
~~~

## ControlStack/AdaptiveUMADAPT.lean

### 28. adSurv_reference_eq

Source: ControlStack/AdaptiveUMADAPT.lean:21 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_reference_eq {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) : ∀ n h, refSurv T M keep n h = adSurv T M (fun _ => 0) keep n h
~~~

### 29. accepts_all_flag_reference

Source: ControlStack/AdaptiveUMADAPT.lean:27 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem accepts_all_flag_reference {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ) (hacc : adSurv T M (fun _ => 0) keep n [] = 1) : refSurv T M keep n [] = 1
~~~

### 30. sharp_uniform_seed_risk

Source: ControlStack/AdaptiveUMADAPT.lean:37 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_uniform_seed_risk {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : adSurv T M (fun _ => 0) keep n [] = 1) (cat : Fin k → ℝ) (hcat : ∀ i, t ≤ cat i) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ (1 / (k : ℝ)) * ∑ i : Fin k, adSurv T M (classRule c g t ((e i).val)) keep n [] * cat i
~~~

### 31. protocolCatModel_eq

Source: ControlStack/AdaptiveUMADAPT.lean:68 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem protocolCatModel_eq {X : Type} [Fintype X] [DecidableEq X] (S : Finset X) (surv cat : X → ℝ) : protocolCatModel S surv cat = (1 / (S.card : ℝ)) * ∑ x : {x // x ∈ S}, surv x.val * cat x.val
~~~

### 32. sum_finEquiv_eq_sum_seed

Source: ControlStack/AdaptiveUMADAPT.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_finEquiv_eq_sum_seed {X : Type} {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (f : {x // x ∈ S} → ℝ) : (∑ i : Fin k, f (e i)) = ∑ x : {x // x ∈ S}, f x
~~~

### 33. sharp_uniform_adProtocolCatModel

Source: ControlStack/AdaptiveUMADAPT.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_uniform_adProtocolCatModel {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] [DecidableEq X] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : adSurv T M (fun _ => 0) keep n [] = 1) (cat : X → ℝ) (hcat : ∀ x ∈ S, t ≤ cat x) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ protocolCatModel S (fun x => adSurv T M (classRule c g t x) keep n []) cat
~~~

## ControlStack/AuditBudget.lean

### 34. filter_disjoint_eq

Source: ControlStack/AuditBudget.lean:51 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem filter_disjoint_eq {N : ℕ} (B : ℕ) (A : Finset (Fin N)) : (randomSchedules N B).filter (fun S => Disjoint S A) = powersetCard B Aᶜ
~~~

### 35. random_subset_survival

Source: ControlStack/AuditBudget.lean:57 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem random_subset_survival {N B k : ℕ} (A : Finset (Fin N)) (hA : A.card = k) : ((randomSchedules N B).filter (fun S => Disjoint S A)).card = Nat.choose (N - k) B ∧ survival (randomSchedules N B) A = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

### 36. choose_mul_le

Source: ControlStack/AuditBudget.lean:69 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_mul_le {N B n : ℕ} (hB : B ≤ N) (hn : n + 1 ≤ N) : (Nat.choose n B : ℝ) * N ≤ (Nat.choose (n + 1) B : ℝ) * ((N : ℝ) - B)
~~~

### 37. choose_mul_pow_le

Source: ControlStack/AuditBudget.lean:99 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_mul_pow_le {N B : ℕ} (hB : B ≤ N) : ∀ k : ℕ, k ≤ N → (Nat.choose (N - k) B : ℝ) * (N : ℝ) ^ k ≤ (Nat.choose N B : ℝ) * ((N : ℝ) - B) ^ k
~~~

### 38. survival_le_pow

Source: ControlStack/AuditBudget.lean:124 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_le_pow {N B k : ℕ} (hN : 0 < N) (hk : k ≤ N) (hB : B ≤ N) : (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) ≤ (((N : ℝ) - B) / N) ^ k
~~~

### 39. random_survival_le_pow

Source: ControlStack/AuditBudget.lean:133 | Family: F6 | Adversary: NON_ADAPTIVE | Status: SOURCE_ONLY

~~~lean
theorem random_survival_le_pow {N B k : ℕ} (hN : 0 < N) (hk : k ≤ N) (hB : B ≤ N) (A : Finset (Fin N)) (hA : A.card = k) : survival (randomSchedules N B) A ≤ (((N : ℝ) - B) / N) ^ k
~~~

### 40. observable_schedule_nogo

Source: ControlStack/AuditBudget.lean:140 | Family: F6 | Adversary: NON_ADAPTIVE | Status: SOURCE_ONLY

~~~lean
theorem observable_schedule_nogo {N B k : ℕ} (S : Finset (Fin N)) (hS : S.card = B) (hk : k ≤ N - B) : ∃ A : Finset (Fin N), A.card = k ∧ Disjoint S A ∧ survival {S} A = 1
~~~

### 41. choose_100_10

Source: ControlStack/AuditBudget.lean:153 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_100_10 : Nat.choose 100 10 = 17310309456440
~~~

### 42. choose_95_10

Source: ControlStack/AuditBudget.lean:156 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_95_10 : Nat.choose 95 10 = 10104934117421
~~~

### 43. budget_example

Source: ControlStack/AuditBudget.lean:160 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem budget_example (A : Finset (Fin 100)) (hA : A.card = 5) : survival (randomSchedules 100 10) A = (10104934117421 : ℝ) / 17310309456440 ∧ survival (randomSchedules 100 10) A ≤ 0.59049 ∧ (0.58 : ℝ) ≤ survival (randomSchedules 100 10) A
~~~

### 44. budget_example_observable

Source: ControlStack/AuditBudget.lean:174 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem budget_example_observable (S : Finset (Fin 100)) (hS : S.card = 10) : ∃ A : Finset (Fin 100), A.card = 5 ∧ survival {S} A = 1
~~~

## ControlStack/AuditDispatch.lean

### 45. step_inv

Source: ControlStack/AuditDispatch.lean:49 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (s : St) (o : Op) (h : Inv s) : Inv (step s o)
~~~

### 46. step_audit_mono

Source: ControlStack/AuditDispatch.lean:71 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_audit_mono (s : St) (o : Op) : s.audits <+: (step s o).audits
~~~

### 47. dispatch_audit_first

Source: ControlStack/AuditDispatch.lean:75 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem dispatch_audit_first (s : St) (id : ℕ) (h : id ∈ s.requests ∧ id ∉ s.effects) : (step s (.dispatch id)).audits = s.audits ++ [id] ∧ (step s (.dispatch id)).effects = s.effects ++ [id]
~~~

### 48. trace_safe

Source: ControlStack/AuditDispatch.lean:82 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem trace_safe (s : St) (ops : List Op) (h : Inv s) : Inv (run s ops) ∧ s.audits <+: (run s ops).audits
~~~

### 49. app_cannot_effect

Source: ControlStack/AuditDispatch.lean:91 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem app_cannot_effect (s : St) (o : Op) (happ : ∀ id, o ≠ .dispatch id) : (step s o).effects = s.effects
~~~

## ControlStack/AuditGate.lean

### 50. step_inv

Source: ControlStack/AuditGate.lean:46 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (s : St) (o : Op) (h : Inv s) : Inv (step s o)
~~~

### 51. step_mono

Source: ControlStack/AuditGate.lean:62 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_mono (s : St) (o : Op) : ∀ a ∈ s.audits, a ∈ (step s o).audits
~~~

### 52. invariant_preserved

Source: ControlStack/AuditGate.lean:66 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem invariant_preserved (s : St) (ops : List Op) (h : Inv s) : Inv (run s ops) ∧ ∀ a ∈ s.audits, a ∈ (run s ops).audits
~~~

## ControlStack/ComposeAvg.lean

### 53. composedJ_factorization

Source: ControlStack/ComposeAvg.lean:33 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem composedJ_factorization {X Y Z Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp Y) (M : Y → ProbComp Z) (J : X → ProbComp (Z × Bool)) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X (Z × Bool) → ProbComp X) (A : Hist X (Z × Bool) → X → Z × Bool → ProbComp Bool) (nh ns b N : ℕ) : (Pr[= true | composedGameJ Bad ρ H M J D π A nh ns b N]).toReal = ∑ ω, (Pr[= ω | ρ]).toReal * binCDF nh ns (Pr[= true | H >>= M >>= D ω]).toReal * (Pr[= true | deploy Bad (π ω) J (jointPass (D ω)) A b N 0 []]).toReal
~~~

### 54. composedJ_end

Source: ControlStack/ComposeAvg.lean:57 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem composedJ_end {X Y Z Ω : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp Y) (M : Y → ProbComp Z) (J : X → ProbComp (Z × Bool)) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X (Z × Bool) → ProbComp X) (A : Hist X (Z × Bool) → X → Z × Bool → ProbComp Bool) (nh ns b N : ℕ) (r K : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hK : 0 ≤ K) (hrec : ∀ h x v, Bad x → r ≤ (Pr[= true | A h x v]).toReal) (hJ : ∀ ω x, Bad x → ∑ v, (Pr[= v | J x]).toReal * (Pr[= true | jointPass (D ω) v]).toReal ≤ K * (Pr[= true | H >>= M >>= D ω]).toReal) : (Pr[= true | composedGameJ Bad ρ H M J D π A nh ns b N]).toReal ≤ (1 - r) + r * (K * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)))
~~~

### 55. untrusted_pass_le

Source: ControlStack/ComposeAvg.lean:125 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem untrusted_pass_le {X Z : Type} [Fintype Z] (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (L : ℝ) (x : X) (hdom : ∀ z, (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) : ∑ z, (Pr[= z | M x]).toReal * (Pr[= true | D z]).toReal ≤ L * (Pr[= true | H >>= M >>= D]).toReal
~~~

### 56. composedPop_end

Source: ControlStack/ComposeAvg.lean:145 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem composedPop_end {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (T : X → ProbComp Bool) (Apop : ProbComp X) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist (Option X) (Z × Bool) → ProbComp (Option X)) (A : Hist (Option X) (Z × Bool) → Option X → Z × Bool → ProbComp Bool) (nh ns b N : ℕ) (r L : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hrec : ∀ h v, r ≤ (Pr[= true | A h none v]).toReal) (hsupp : ∀ x, Pr[= x | Apop] ≠ 0 → Bad x) (hdom : ∀ x, Bad x → ∀ z, (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) : (Pr[= true | composedGameJ popBad ρ H M (popJ M T Apop) D π A nh ns b N]).toReal ≤ (1 - r) + r * (((Pr[= true | Apop >>= T]).toReal * L) * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)))
~~~

## ControlStack/ComposeBlindSpot.lean

### 57. pop_avg_miss

Source: ControlStack/ComposeBlindSpot.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pop_avg_miss : Pr[= true | popA >>= blindT] = 1 / 1000
~~~

### 58. blind_spot_risk

Source: ControlStack/ComposeBlindSpot.lean:39 | Family: F6 | Adversary: CONTENT_ADAPTIVE | Status: PROVED_RECORDED

~~~lean
theorem blind_spot_risk : Pr[= true | composedGame (fun _ : Fin 2 => True) (pure ()) (pure (1 : Fin 2)) (fun x => pure x) blindT (fun _ _ => pure true) (fun _ _ => pure (1 : Fin 2)) (fun _ _ _ => pure true) 0 0 1 1] = 1
~~~

## ControlStack/ComposeCoverage.lean

### 59. coverage_transfer

Source: ControlStack/ComposeCoverage.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem coverage_transfer {X : Type} [Fintype X] (a q τ e : X → ℝ) (K ε : ℝ) (hτ0 : ∀ x, 0 ≤ τ x) (hτ1 : ∀ x, τ x ≤ 1) (he0 : ∀ x, 0 ≤ e x) (heps : ∑ x, e x ≤ ε) (hcov : ∀ x, a x ≤ K * q x + e x) (ha0 : ∀ x, 0 ≤ a x) : ∑ x, a x * τ x ≤ K * ∑ x, q x * τ x + ε
~~~

### 60. tight_K

Source: ControlStack/ComposeCoverage.lean:40 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tight_K (K t : ℝ) (hK : 1 ≤ K) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hKt : K * t ≤ 1) : let q : Bool → ℝ
~~~

### 61. tight_eps

Source: ControlStack/ComposeCoverage.lean:57 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tight_eps (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : let q : Bool → ℝ
~~~

### 62. coverage_miss

Source: ControlStack/ComposeCoverage.lean:73 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem coverage_miss {X : Type} [Fintype X] (Apop Cal : ProbComp X) (T : X → ProbComp Bool) (K ε : ℝ) (e : X → ℝ) (he0 : ∀ x, 0 ≤ e x) (heps : ∑ x, e x ≤ ε) (hcov : ∀ x, (Pr[= x | Apop]).toReal ≤ K * (Pr[= x | Cal]).toReal + e x) : (Pr[= true | Apop >>= T]).toReal ≤ K * (Pr[= true | Cal >>= T]).toReal + ε
~~~

### 63. composedCov_end

Source: ControlStack/ComposeCoverage.lean:89 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem composedCov_end {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (T : X → ProbComp Bool) (Apop Cal : ProbComp X) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist (Option X) (Z × Bool) → ProbComp (Option X)) (A : Hist (Option X) (Z × Bool) → Option X → Z × Bool → ProbComp Bool) (nh ns b N : ℕ) (r L K ε : ℝ) (e : X → ℝ) (he0 : ∀ x, 0 ≤ e x) (heps : ∑ x, e x ≤ ε) (hcov : ∀ x, (Pr[= x | Apop]).toReal ≤ K * (Pr[= x | Cal]).toReal + e x) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hrec : ∀ h v, r ≤ (Pr[= true | A h none v]).toReal) (hsupp : ∀ x, Pr[= x | Apop] ≠ 0 → Bad x) (hdom : ∀ x, Bad x → ∀ z, (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) : (Pr[= true | composedGameJ popBad ρ H M (popJ M T Apop) D π A nh ns b N]).toReal ≤ (1 - r) + r * (((K * (Pr[= true | Cal >>= T]).toReal + ε) * L) * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)))
~~~

## ControlStack/ComposeGame.lean

### 64. composed_factorization

Source: ControlStack/ComposeGame.lean:46 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem composed_factorization {X Z Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (T : X → ProbComp Bool) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X (Z × Bool) → ProbComp X) (A : Hist X (Z × Bool) → X → Z × Bool → ProbComp Bool) (nh ns b N : ℕ) : (Pr[= true | composedGame Bad ρ H M T D π A nh ns b N]).toReal = ∑ ω, (Pr[= ω | ρ]).toReal * binCDF nh ns (Pr[= true | H >>= M >>= D ω]).toReal * (Pr[= true | deploy Bad (π ω) (jointView M T) (jointPass (D ω)) A b N 0 []]).toReal
~~~

### 65. joint_pass_prob

Source: ControlStack/ComposeGame.lean:70 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem joint_pass_prob {X Z : Type} [Fintype Z] (M : X → ProbComp Z) (T : X → ProbComp Bool) (D : Z → ProbComp Bool) (x : X) : ∑ v, (Pr[= v | jointView M T x]).toReal * (Pr[= true | jointPass D v]).toReal = (Pr[= true | T x]).toReal * ∑ z, (Pr[= z | M x]).toReal * (Pr[= true | D z]).toReal
~~~

### 66. composedEndToEnd

Source: ControlStack/ComposeGame.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem composedEndToEnd {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (T : X → ProbComp Bool) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X (Z × Bool) → ProbComp X) (A : Hist X (Z × Bool) → X → Z × Bool → ProbComp Bool) (nh ns b N : ℕ) (r L τ : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hτ0 : 0 ≤ τ) (hrec : ∀ h x v, Bad x → r ≤ (Pr[= true | A h x v]).toReal) (htm : ∀ x, Bad x → (Pr[= true | T x]).toReal ≤ τ) (hdom : ∀ x, Bad x → ∀ z, (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) : (Pr[= true | composedGame Bad ρ H M T D π A nh ns b N]).toReal ≤ (1 - r) + r * ((τ * L) * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)))
~~~

### 67. composed_tight

Source: ControlStack/ComposeGame.lean:174 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem composed_tight : (Pr[= true | composedGame (fun x : Bool => x = true) (pure ()) (pure true) (fun x => pure x) (fun _ => (fun k : Fin 2 => decide (k = 0)) <$> $[0..1]) (fun _ _ => pure true) (fun _ _ => pure true) (fun _ _ _ => (fun k : Fin 2 => decide (k = 0)) <$> $[0..1]) 0 0 1 1]).toReal = 3 / 4 ∧ (3 / 4 : ℝ) = (1 - 1 / 2) + 1 / 2 * ((1 / 2 * 1) * (((0 : ℝ) + 1) / ((0 : ℝ) + 1)))
~~~

## ControlStack/Core/AntiRollback.lean

### 68. rinv_init

Source: ControlStack/Core/AntiRollback.lean:134 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rinv_init (G : System St Op Eff) (S : Spec G) (init : St) (h : S.Inv init) : RInv G S init (rinit G init)
~~~

### 69. run_append_one

Source: ControlStack/Core/AntiRollback.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_append_one (G : System St Op Eff) (init : St) (l : List Op) (o : Op) : G.run init (l ++ [o]) = G.step (G.run init l) o
~~~

### 70. commit_inv

Source: ControlStack/Core/AntiRollback.lean:143 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem commit_inv (G : System St Op Eff) (S : Spec G) (init : St) (s : RSt St Op Eff) (h : RInv G S init s) (hn : IsNext s) : RInv G S init (commit G s)
~~~

### 71. stepR_inv

Source: ControlStack/Core/AntiRollback.lean:161 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stepR_inv (G : System St Op Eff) (S : Spec G) (init : St) (s : RSt St Op Eff) (o : ROp Op) (h : RInv G S init s) : RInv G S init (stepR G true s o)
~~~

### 72. runR_inv

Source: ControlStack/Core/AntiRollback.lean:195 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runR_inv (G : System St Op Eff) (S : Spec G) (init : St) (s : RSt St Op Eff) (ops : List (ROp Op)) (h : RInv G S init s) : RInv G S init (runR G true s ops)
~~~

### 73. rollback_transfer

Source: ControlStack/Core/AntiRollback.lean:205 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rollback_transfer (G : System St Op Eff) (S : Spec G) (init : St) (hinit : S.Inv init) (ops : List (ROp Op)) : let t
~~~

### 74. accepts_only_fresh

Source: ControlStack/Core/AntiRollback.lean:219 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem accepts_only_fresh (G : System St Op Eff) (s : RSt St Op Eff) (o : Op) (hw : (stepR G true s (.write o)).store ≠ s.store) : s.store = s.anchor ∧ s.halted = false
~~~

### 75. next_ne

Source: ControlStack/Core/AntiRollback.lean:231 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem next_ne (a : Rec St Op) (x y : St) (o : Option Op) : (⟨a.ver + 1, x, y, o⟩ : Rec St Op) ≠ a
~~~

### 76. honest_liveness

Source: ControlStack/Core/AntiRollback.lean:254 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_liveness (G : System St Op Eff) (s : RSt St Op Eff) (hf : s.store = s.anchor) (hh : s.halted = false) (items : List (HItem Op)) : let t
~~~

### 77. nonce_replay_without_anchor

Source: ControlStack/Core/AntiRollback.lean:295 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nonce_replay_without_anchor : (runR nonceGate false (rinit nonceGate []) replayTrace).released = [0, 0] ∧ (runR nonceGate true (rinit nonceGate []) replayTrace).released = [0] ∧ (runR nonceGate true (rinit nonceGate []) replayTrace).halted = true
~~~

### 78. rollback_without_anchor_double_spends

Source: ControlStack/Core/AntiRollback.lean:313 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rollback_without_anchor_double_spends : (runR G28 false (rinit G28 SC28.init) spendTrace).released = [(1, 0, 10), (1, 0, 10)] ∧ (runR G28 true (rinit G28 SC28.init) spendTrace).released = [(1, 0, 10)] ∧ (runR G28 true (rinit G28 SC28.init) spendTrace).halted = true
~~~

### 79. sc28_rollback_safe

Source: ControlStack/Core/AntiRollback.lean:322 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc28_rollback_safe (admins : List ℕ) (G : ℕ) (ops : List (ROp {o : SC28.Op // SC28.legal o})) : let t
~~~

### 80. crash_then_rollback_halts

Source: ControlStack/Core/AntiRollback.lean:342 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem crash_then_rollback_halts : let t
~~~

### 81. crash_recovery_commits

Source: ControlStack/Core/AntiRollback.lean:349 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem crash_recovery_commits : let t
~~~

## ControlStack/Core/Authenticated.lean

### 82. authed_run

Source: ControlStack/Core/Authenticated.lean:55 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem authed_run (G : System St Op Eff) (claim : Op → Option ℕ) (s : St) (ops : List (ℕ × Op)) : (authed G claim).run s ops = G.run s (applied claim ops)
~~~

### 83. claim_issued_by

Source: ControlStack/Core/Authenticated.lean:70 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_issued_by (claim : Op → Option ℕ) (ops : List (ℕ × Op)) (o : Op) (x : ℕ) (ho : o ∈ applied claim ops) (hc : claim o = some x) : (x, o) ∈ ops
~~~

### 84. trusted_claim_not_adversary

Source: ControlStack/Core/Authenticated.lean:81 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem trusted_claim_not_adversary (claim : Op → Option ℕ) (U : List ℕ) (ops : List (ℕ × Op)) (o : Op) (x : ℕ) (ho : o ∈ applied claim ops) (hc : claim o = some x) (hx : x ∉ U) : ∃ io ∈ ops, io.1 = x ∧ io.1 ∉ U ∧ io.2 = o
~~~

### 85. authed_trace_safe

Source: ControlStack/Core/Authenticated.lean:102 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem authed_trace_safe (G : System St Op Eff) (claim : Op → Option ℕ) (S : Spec G) (s : St) (ops : List (ℕ × Op)) (h : S.Inv s) : S.Inv ((authed G claim).run s ops) ∧ G.effects s <+: G.effects ((authed G claim).run s ops) ∧ ∀ e ∈ G.effects ((authed G claim).run s ops), S.ok ((authed G claim).run s ops) e
~~~

## ControlStack/Core/AuthenticatedAdv.lean

### 86. Shuffle.mem

Source: ControlStack/Core/AuthenticatedAdv.lean:43 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Shuffle.mem {α : Type} {l r m : List α} (h : Shuffle l r m) {x : α} (hx : x ∈ m) : x ∈ l ∨ x ∈ r
~~~

### 87. applied_trusted_claim_from_honest

Source: ControlStack/Core/AuthenticatedAdv.lean:65 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem applied_trusted_claim_from_honest {Op : Type} (claim : Op → Option ℕ) (U : List ℕ) (hon ops : List (ℕ × Op)) (hadv : AdvTrace U hon ops) (o : Op) (x : ℕ) (ho : o ∈ applied claim ops) (hc : claim o = some x) (hx : x ∉ U) : (x, o) ∈ hon
~~~

### 88. adversary_acts_only_as_U

Source: ControlStack/Core/AuthenticatedAdv.lean:75 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adversary_acts_only_as_U {Op : Type} (claim : Op → Option ℕ) (U : List ℕ) (adv : List (ℕ × Op)) (hU : ∀ io ∈ adv, io.1 ∈ U) (io : ℕ × Op) (hio : io ∈ adv) (ha : Authentic claim io) : claim io.2 = none ∨ ∃ x ∈ U, claim io.2 = some x
~~~

### 89. sc26_consent_from_honest_script

Source: ControlStack/Core/AuthenticatedAdv.lean:89 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc26_consent_from_honest_script (R : Roles) (cap : ℕ) (U : List ℕ) (hon ops : List (ℕ × Op)) (hadv : AdvTrace U hon ops) (hUa : ∀ u ∈ U, u ∉ R.approvers) (hUg : R.gate ∉ U) (hhon : ∀ io ∈ hon, ∀ c k tx, io.2 = .bankCall c k tx → io.1 ≠ R.gate) : Good R cap ((authed (raw R cap) claim).run init ops) ∧ ∀ e ∈ ((authed (raw R cap) claim).run init ops).bank, ∃ a, a ∈ R.approvers ∧ (a, Op.approve a e.1 e.2) ∈ hon
~~~

### 90. honest_payment_admissible

Source: ControlStack/Core/AuthenticatedAdv.lean:120 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_payment_admissible : AdvTrace [1] honScript honestTrace ∧ ((authed (raw R0 20) claim).run init honestTrace).bank = [(0, tx1)]
~~~

### 91. forged_claim_admissible_pays_nothing

Source: ControlStack/Core/AuthenticatedAdv.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forged_claim_admissible_pays_nothing : AdvTrace [1] [] forged ∧ ((authed (raw R0 20) claim).run init forged).bank = []
~~~

## ControlStack/Core/AuthenticatedLog.lean

### 92. authRun_eq

Source: ControlStack/Core/AuthenticatedLog.lean:34 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem authRun_eq (step : St → Op → St) (claim : Op → Option ℕ) (s : St) (ops : List (ℕ × Op)) : authRun step claim s ops = (applied claim ops).foldl step s
~~~

### 93. log_origin

Source: ControlStack/Core/AuthenticatedLog.lean:39 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem log_origin (step : St → Op → St) (rec : St → List R) (P : Op → R → Prop) (hstep : ∀ s o x, x ∈ rec (step s o) → x ∈ rec s ∨ P o x) : ∀ (L : List Op) (s : St) (x : R), x ∈ rec (L.foldl step s) → x ∈ rec s ∨ ∃ o ∈ L, P o x
~~~

### 94. issued_of_mem_log

Source: ControlStack/Core/AuthenticatedLog.lean:54 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem issued_of_mem_log (step : St → Op → St) (claim : Op → Option ℕ) (rec : St → List R) (P : ℕ → Op → R → Prop) (hstep : ∀ s o x, x ∈ rec (step s o) → x ∈ rec s ∨ ∃ c, claim o = some c ∧ P c o x) (s0 : St) (h0 : rec s0 = []) (ops : List (ℕ × Op)) : ∀ x ∈ rec (authRun step claim s0 ops), ∃ c o, (c, o) ∈ ops ∧ P c o x
~~~

### 95. issued_trusted

Source: ControlStack/Core/AuthenticatedLog.lean:66 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem issued_trusted (step : St → Op → St) (claim : Op → Option ℕ) (rec : St → List R) (P : ℕ → Op → R → Prop) (T U : List ℕ) (hstep : ∀ s o x, x ∈ rec (step s o) → x ∈ rec s ∨ ∃ c, claim o = some c ∧ P c o x) (hT : ∀ c o x, P c o x → c ∈ T) (hU : ∀ u ∈ U, u ∉ T) (s0 : St) (h0 : rec s0 = []) (ops : List (ℕ × Op)) : ∀ x ∈ rec (authRun step claim s0 ops), ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ P c o x
~~~

### 96. mem_of_applied

Source: ControlStack/Core/AuthenticatedLog.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mem_of_applied (claim : Op → Option ℕ) (ops : List (ℕ × Op)) (o : Op) (ho : o ∈ applied claim ops) : ∃ i, (i, o) ∈ ops
~~~

### 97. applied_claim

Source: ControlStack/Core/AuthenticatedLog.lean:84 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem applied_claim (claim : Op → Option ℕ) (ops : List (ℕ × Op)) (o : Op) (ho : o ∈ applied claim ops) : claim o = none ∨ ∃ i, claim o = some i ∧ (i, o) ∈ ops
~~~

## ControlStack/Core/Cert.lean

### 98. AllHold.append

Source: ControlStack/Core/Cert.lean:101 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem AllHold.append {ps qs : List Premise} (h : AllHold (ps ++ qs)) : AllHold ps ∧ AllHold qs
~~~

### 99. AllHold.cons

Source: ControlStack/Core/Cert.lean:104 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem AllHold.cons {p : Premise} {ps : List Premise} (h : AllHold (p :: ps)) : p.holds ∧ AllHold ps
~~~

### 100. prob_nonneg

Source: ControlStack/Core/Cert.lean:147 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prob_nonneg (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (A : Ω → Prop) : 0 ≤ prob μ A
~~~

### 101. prob_mono

Source: ControlStack/Core/Cert.lean:151 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prob_mono (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (A B : Ω → Prop) (h : ∀ ω, A ω → B ω) : prob μ A ≤ prob μ B
~~~

### 102. prob_or_le

Source: ControlStack/Core/Cert.lean:160 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prob_or_le (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (A B : Ω → Prop) : prob μ (fun ω => A ω ∨ B ω) ≤ prob μ A + prob μ B
~~~

### 103. prob_empty

Source: ControlStack/Core/Cert.lean:169 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prob_empty (μ : Ω → ℝ) (A : Ω → Prop) (h : ∀ ω, ¬A ω) : prob μ A = 0
~~~

### 104. product_needs_independence

Source: ControlStack/Core/Cert.lean:225 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem product_needs_independence : prob Necessity.scoreLaw (fun s => s = false) = 1 / 10 ∧ prob Necessity.scoreLaw (fun s => s = false ∧ s = false) = 1 / 10 ∧ (1 / 10 : ℝ) * (1 / 10) < prob Necessity.scoreLaw (fun s => s = false ∧ s = false) ∧ prob Necessity.scoreLaw (fun s => s = false ∧ s = false) ≠ prob Necessity.scoreLaw (fun s => s = false) * prob Necessity.scoreLaw (fun s => s = false)
~~~

### 105. f6_of

Source: ControlStack/Core/Cert.lean:315 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem f6_of (Bh : ℕ) (r : ℝ) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hp : AllHold (f6Premises Bh r K σ)) : (∀ g, IsDist (σ g)) ∧ (∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) ∧ (∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) ∧ (∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1))
~~~

### 106. sc26_paid_le_cap

Source: ControlStack/Core/Cert.lean:361 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc26_paid_le_cap (R : SC26.Roles) (cap : ℕ) (ops : List SC26.Op) (hops : ∀ o ∈ ops, SC26.legal R o) : paidTotal (SC26.run R cap SC26.full SC26.init ops) ≤ cap
~~~

### 107. payDamage_le_cap

Source: ControlStack/Core/Cert.lean:371 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem payDamage_le_cap (R : SC26.Roles) (cap : ℕ) (realize : List (AOut Unit) → List SC26.Op) (hreal : ∀ t, ∀ o ∈ realize t, SC26.legal R o) : ∀ t, payDamage R cap realize t ≤ cap
~~~

### 108. damageSC26_discharged

Source: ControlStack/Core/Cert.lean:411 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem damageSC26_discharged (Bh : ℕ) (r : ℝ) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (D F : ℝ) (R : SC26.Roles) (cap : ℕ) (realize : List (AOut Unit) → List SC26.Op) (hp : AllHold (damageSC26Open Bh r K σ D F R cap realize)) : (damageSC26Obligation R cap realize).holds
~~~

### 109. design_attack_rounds

Source: ControlStack/Core/Cert.lean:462 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem design_attack_rounds : ∑ j ∈ range 100, hypMiss 100 10 (j + 1) (1 / 2) ≤ 19
~~~

### 110. stack_sound

Source: ControlStack/Core/Cert.lean:488 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stack_sound (μ : Ω → ℝ) (R : SC26.Roles) (cap : ℕ) (C : SC26.Checks) (trace : Ω → List SC26.Op) (y0 : Y) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (D F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (realize : List (AOut Unit) → List SC26.Op) (T t0 e0 G' : ℕ) (e lat ep : ℕ → ℕ → ℕ) (hp : AllHold (stackExample μ R cap C trace y0 K σ D F hD hF realize T t0 e0 G' e lat ep).premises) : ∀ c ∈ (stackExample μ R cap C trace y0 K σ D F hD hF realize T t0 e0 G' e lat ep).claims, c.2
~~~

### 111. stack_claims

Source: ControlStack/Core/Cert.lean:497 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stack_claims (μ : Ω → ℝ) (R : SC26.Roles) (cap : ℕ) (C : SC26.Checks) (trace : Ω → List SC26.Op) (y0 : Y) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (D F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (realize : List (AOut Unit) → List SC26.Op) (T t0 e0 G' : ℕ) (e lat ep : ℕ → ℕ → ℕ) (hp : AllHold (stackExample μ R cap C trace y0 K σ D F hD hF realize T t0 e0 G' e lat ep).premises) : prob μ (fun ω => ¬ SC26.Good R cap (SC26.run R cap C SC26.init (trace ω))) ≤ 0 ∧ ∑ S : Finset (Fin 100), pU 100 10 S * val (K S) (fun t => (DamageBound.ucX 100 t : ℝ)) 100 [] ≤ 19 ∧ ∑ S : Finset (Fin 100), pU 100 10 S * val (K S) (payDamage R cap realize) 100 [] ≤ Min.min (cap : ℝ) (D * 19 + F) ∧ (((DistributedHalt.sinkRun true t0 1 e0 G' (DistributedHalt.stream 1000 T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) : ℕ) : ℝ) ≤ Min.min (G' : ℝ) 10000 ∧ (((DistributedHalt.sinkRun true t0 1 e0 G' (DistributedHalt.stream 1000 T e lat ep)).countP (fun ev => decide (t0 + 1 ≤ ev.1)) : ℕ) : ℝ) ≤ 0
~~~

### 112. stack_ledger_eq

Source: ControlStack/Core/Cert.lean:550 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stack_ledger_eq (μ : Ω → ℝ) (R : SC26.Roles) (cap : ℕ) (C : SC26.Checks) (trace : Ω → List SC26.Op) (y0 : Y) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (D F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (realize : List (AOut Unit) → List SC26.Op) (T t0 e0 G' : ℕ) (e lat ep : ℕ → ℕ → ℕ) : typedLedger (stackExample μ R cap C trace y0 K σ D F hD hF realize T t0 e0 G' e lat ep).premises = stackLedger
~~~

## ControlStack/Core/CertBest.lean

### 113. ProbCert.best_bound

Source: ControlStack/Core/CertBest.lean:28 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ProbCert.best_bound {μ : Ω → ℝ} {A : Ω → Prop} (c₁ c₂ : ProbCert μ A) : (ProbCert.best c₁ c₂).bound = Min.min c₁.bound c₂.bound
~~~

### 114. ProbCert.best_premises

Source: ControlStack/Core/CertBest.lean:35 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ProbCert.best_premises {μ : Ω → ℝ} {A : Ω → Prop} (c₁ c₂ : ProbCert μ A) : (ProbCert.best c₁ c₂).premises = if c₁.bound ≤ c₂.bound then c₁.premises else c₂.premises
~~~

### 115. ProbCert.best_premises_subset

Source: ControlStack/Core/CertBest.lean:40 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ProbCert.best_premises_subset {μ : Ω → ℝ} {A : Ω → Prop} (c₁ c₂ : ProbCert μ A) : (ProbCert.best c₁ c₂).premises ⊆ (ProbCert.min c₁ c₂).premises
~~~

### 116. ProbCert.best_sound

Source: ControlStack/Core/CertBest.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ProbCert.best_sound {μ : Ω → ℝ} {A : Ω → Prop} (c₁ c₂ : ProbCert μ A) (hp : AllHold (ProbCert.best c₁ c₂).premises) : prob μ A ≤ Min.min c₁.bound c₂.bound
~~~

### 117. QtyCert.best_bound

Source: ControlStack/Core/CertBest.lean:59 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem QtyCert.best_bound {q : ℝ} (c₁ c₂ : QtyCert q) : (QtyCert.best c₁ c₂).bound = Min.min c₁.bound c₂.bound
~~~

### 118. QtyCert.best_premises

Source: ControlStack/Core/CertBest.lean:65 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem QtyCert.best_premises {q : ℝ} (c₁ c₂ : QtyCert q) : (QtyCert.best c₁ c₂).premises = if c₁.bound ≤ c₂.bound then c₁.premises else c₂.premises
~~~

### 119. QtyCert.best_premises_subset

Source: ControlStack/Core/CertBest.lean:70 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem QtyCert.best_premises_subset {q : ℝ} (c₁ c₂ : QtyCert q) : (QtyCert.best c₁ c₂).premises ⊆ (QtyCert.min c₁ c₂).premises
~~~

### 120. QtyCert.best_sound

Source: ControlStack/Core/CertBest.lean:78 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem QtyCert.best_sound {q : ℝ} (c₁ c₂ : QtyCert q) (hp : AllHold (QtyCert.best c₁ c₂).premises) : q ≤ Min.min c₁.bound c₂.bound
~~~

### 121. best_needs_less

Source: ControlStack/Core/CertBest.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem best_needs_less : let c₁ : QtyCert 0
~~~

## ControlStack/Core/CheckedTrace.lean

### 122. verified_sound

Source: ControlStack/Core/CheckedTrace.lean:53 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem verified_sound [DecidableEq S] (step : S → O → S) (rs : List (Receipt S O)) : ∀ s, verified step s rs = true → recordedEnd s rs = (events rs).foldl step s
~~~

### 123. sc04_alphabet_card

Source: ControlStack/Core/CheckedTrace.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc04_alphabet_card (templates fields levels : ℕ) : Fintype.card (SC04Alphabet templates fields levels) = templates * levels ^ fields
~~~

### 124. sc06_receipts_sound

Source: ControlStack/Core/CheckedTrace.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc06_receipts_sound (P : SC06.Policy) (rs : List (Receipt SC06.St SC06.Op)) (h : verified (SC06.step P SC06.full) (SC06.init) rs = true) : SC06.Good P (recordedEnd SC06.init rs)
~~~

### 125. sc08_receipts_sound

Source: ControlStack/Core/CheckedTrace.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc08_receipts_sound (E : SC08.Env) (files : List (ℕ × ℕ)) (rs : List (Receipt SC08.St SC08.Op)) (h : verified (SC08.step E SC08.full) (⟨files, [], false⟩ : SC08.St) rs = true) : SC08.Good E (recordedEnd (⟨files, [], false⟩ : SC08.St) rs)
~~~

### 126. sc09_receipts_sound

Source: ControlStack/Core/CheckedTrace.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc09_receipts_sound (P : SC09.Policy) (rs : List (Receipt SC09.St SC09.Op)) (h : verified (SC09.step P SC09.full) (SC09.init) rs = true) : SC09.Good P (recordedEnd SC09.init rs)
~~~

### 127. sc10_receipts_sound

Source: ControlStack/Core/CheckedTrace.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc10_receipts_sound (E : SC10.Env) (hpin : E.h E.pinned = E.pinnedDigest) (rs : List (Receipt SC10.St SC10.Op)) (h : verified (SC10.step E SC10.full) (SC10.init) rs = true) : SC10.Good E (recordedEnd SC10.init rs)
~~~

### 128. sc14_receipts_sound

Source: ControlStack/Core/CheckedTrace.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc14_receipts_sound (E : SC14.Env) (exp : ℕ) (rs : List (Receipt SC14.St SC14.Op)) (hops : ∀ o ∈ events rs, SC14.legal o) (h : verified (SC14.step E SC14.full) (SC14.init exp) rs = true) : SC14.Good E (recordedEnd (SC14.init exp) rs)
~~~

### 129. sc15_receipts_sound

Source: ControlStack/Core/CheckedTrace.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc15_receipts_sound (E : SC15.Env) (rs : List (Receipt SC15.St SC15.Op)) (h : verified (SC15.step E SC15.full) (SC15.init) rs = true) : ∀ c ∈ (recordedEnd SC15.init rs).merged, SC15.MergeOk E (recordedEnd SC15.init rs) c
~~~

### 130. sc17_receipts_sound

Source: ControlStack/Core/CheckedTrace.lean:164 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc17_receipts_sound (E : SC17.Env) (g0 : List SC17.G) (rs : List (Receipt SC17.St SC17.Op)) (h : verified (SC17.step E SC17.full) (SC17.init g0) rs = true) : SC17.Good E (recordedEnd (SC17.init g0) rs)
~~~

### 131. sc19_receipts_sound

Source: ControlStack/Core/CheckedTrace.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc19_receipts_sound (E : SC19.Env) (rs : List (Receipt SC19.St SC19.Op)) (h : verified (SC19.step E SC19.full) (SC19.init) rs = true) : SC19.Good E (recordedEnd SC19.init rs)
~~~

### 132. sc20_receipts_sound

Source: ControlStack/Core/CheckedTrace.lean:182 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc20_receipts_sound (E : SC20.Env) (rs : List (Receipt SC20.St SC20.Op)) (h : verified (SC20.step E SC20.full) (SC20.init) rs = true) : SC20.Good E (recordedEnd SC20.init rs)
~~~

### 133. sc23_receipts_sound

Source: ControlStack/Core/CheckedTrace.lean:191 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc23_receipts_sound (P : SC23.Policy) (rs : List (Receipt SC23.St SC23.Op)) (h : verified (SC23.step P SC23.full) (SC23.init) rs = true) : SC23.Good P (recordedEnd SC23.init rs)
~~~

## ControlStack/Core/Compose.lean

### 134. lefts_append

Source: ControlStack/Core/Compose.lean:39 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem lefts_append (l m : List (Eff₁ ⊕ Eff₂)) : lefts (l ++ m) = lefts l ++ lefts m
~~~

### 135. rights_append

Source: ControlStack/Core/Compose.lean:42 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem rights_append (l m : List (Eff₁ ⊕ Eff₂)) : rights (l ++ m) = rights l ++ rights m
~~~

### 136. lefts_inl

Source: ControlStack/Core/Compose.lean:45 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem lefts_inl (l : List Eff₁) : lefts (l.map (Sum.inl : Eff₁ → Eff₁ ⊕ Eff₂)) = l
~~~

### 137. rights_inl

Source: ControlStack/Core/Compose.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem rights_inl (l : List Eff₁) : rights (l.map (Sum.inl : Eff₁ → Eff₁ ⊕ Eff₂)) = []
~~~

### 138. lefts_inr

Source: ControlStack/Core/Compose.lean:51 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem lefts_inr (l : List Eff₂) : lefts (l.map (Sum.inr : Eff₂ → Eff₁ ⊕ Eff₂)) = []
~~~

### 139. rights_inr

Source: ControlStack/Core/Compose.lean:54 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem rights_inr (l : List Eff₂) : rights (l.map (Sum.inr : Eff₂ → Eff₁ ⊕ Eff₂)) = l
~~~

### 140. append_newEffects

Source: ControlStack/Core/Compose.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem append_newEffects {St Op Eff : Type} (G : System St Op Eff) (s s' : St) (h : G.effects s <+: G.effects s') : G.effects s ++ newEffects G s s' = G.effects s'
~~~

### 141. prodInit_coherent

Source: ControlStack/Core/Compose.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prodInit_coherent (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (s₁ : St₁) (s₂ : St₂) : Coherent G₁ G₂ (prodInit G₁ G₂ s₁ s₂)
~~~

### 142. stepL_coherent

Source: ControlStack/Core/Compose.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stepL_coherent (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (p : PSt St₁ St₂ Eff₁ Eff₂) (s' : St₁) (hc : Coherent G₁ G₂ p) (hpre : G₁.effects p.s₁ <+: G₁.effects s') : Coherent G₁ G₂ (stepL G₁ p s')
~~~

### 143. stepR_coherent

Source: ControlStack/Core/Compose.lean:108 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stepR_coherent (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (p : PSt St₁ St₂ Eff₁ Eff₂) (s' : St₂) (hc : Coherent G₁ G₂ p) (hpre : G₂.effects p.s₂ <+: G₂.effects s') : Coherent G₁ G₂ (stepR G₂ p s')
~~~

### 144. tagOk_of_coherent

Source: ControlStack/Core/Compose.lean:121 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tagOk_of_coherent {G₁ : System St₁ Op₁ Eff₁} {G₂ : System St₂ Op₂ Eff₂} (S₁ : Spec G₁) (S₂ : Spec G₂) (p : PSt St₁ St₂ Eff₁ Eff₂) (h1 : S₁.Inv p.s₁) (h2 : S₂.Inv p.s₂) (hc : Coherent G₁ G₂ p) : ∀ e ∈ p.log, tagOk S₁ S₂ p e
~~~

### 145. prod_trace_safe

Source: ControlStack/Core/Compose.lean:153 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prod_trace_safe {G₁ : System St₁ Op₁ Eff₁} {G₂ : System St₂ Op₂ Eff₂} (S₁ : Spec G₁) (S₂ : Spec G₂) (s₁ : St₁) (s₂ : St₂) (h1 : S₁.Inv s₁) (h2 : S₂.Inv s₂) (ops : List (Op₁ ⊕ Op₂)) : let p
~~~

### 146. prod_halt_freezes

Source: ControlStack/Core/Compose.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prod_halt_freezes (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (p : PSt St₁ St₂ Eff₁ Eff₂) (ops : List (HOp (Op₁ ⊕ Op₂))) : let q
~~~

### 147. separate_halt_leaves_other_running

Source: ControlStack/Core/Compose.lean:189 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem separate_halt_leaves_other_running : let q
~~~

### 148. admissible_of_step

Source: ControlStack/Core/Compose.lean:238 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem admissible_of_step {G₁ : System St₁ Op₁ Eff₁} {G₂ : System St₂ Op₂ Eff₂} (S₁ : Spec G₁) (S₂ : Spec G₂) (b : St₁ → St₂ → St₂) (f : St₁ → St₂ → Op₂) (hb : ∀ s₁ s₂, b s₁ s₂ = G₂.step s₂ (f s₁ s₂)) : BridgeAdmissible S₁ S₂ b
~~~

### 149. bridge_breaks_joint

Source: ControlStack/Core/Compose.lean:275 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bridge_breaks_joint : let p
~~~

## ControlStack/Core/DatacenterRoots.lean

### 150. file_roots_table

Source: ControlStack/Core/DatacenterRoots.lean:162 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem file_roots_table : files.map (fun f => (f.1, fileRoots f.2)) = [("F2/GPUResidue", [.kernelMediation, .measuredRates, .implementationConformance]), ("F1/FabricIsolation", [.kernelMediation, .keyCustody, .measuredRates, .implementationConformance]), ("F4/AttestedKeyRelease", [.issuerAuthenticity, .kernelMediation, .collisionResistance, .keyCustody, .measuredRates, .orgConfiguration, .implementationConformance]), ("F5/EscrowBudgetMsg", [.issuerAuthenticity, .monotonicAnchor, .keyCustody, .measuredRates]), ("F3/DistributedHalt", [.issuerAuthenticity, .kernelMediation, .trustedMeter, .keyCustody, .measuredRates, .implementationConformance])]
~~~

### 151. layer_roots

Source: ControlStack/Core/DatacenterRoots.lean:174 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem layer_roots : layerRoots = [.issuerAuthenticity, .kernelMediation, .monotonicAnchor, .trustedMeter, .collisionResistance, .keyCustody, .measuredRates, .orgConfiguration, .implementationConformance]
~~~

### 152. layer_sharing

Source: ControlStack/Core/DatacenterRoots.lean:181 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem layer_sharing : allRoots.map layerCount = [3, 4, 1, 0, 1, 1, 4, 5, 0, 1, 4, 0]
~~~

### 153. layer_vs_portfolio

Source: ControlStack/Core/DatacenterRoots.lean:189 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem layer_vs_portfolio : (∀ r ∈ layerRoots, r ∈ allRoots) ∧ portfolioCount .keyCustody = 3 ∧ layerCount .keyCustody = 4 ∧ layerCount .measuredRates = files.length ∧ allRoots.filter (fun r => decide (4 * layerCount r * scenarios.length > 4 * portfolioCount r * files.length + files.length * scenarios.length)) = [.keyCustody, .implementationConformance]
~~~

## ControlStack/Core/Gate.lean

### 154. System.run_nil

Source: ControlStack/Core/Gate.lean:41 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem System.run_nil {St Op Eff : Type} (G : System St Op Eff) (s : St) : G.run s [] = s
~~~

### 155. System.run_cons

Source: ControlStack/Core/Gate.lean:43 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem System.run_cons {St Op Eff : Type} (G : System St Op Eff) (s : St) (o : Op) (ops : List Op) : G.run s (o :: ops) = G.run (G.step s o) ops
~~~

### 156. Spec.trace_safe

Source: ControlStack/Core/Gate.lean:55 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem Spec.trace_safe {St Op Eff : Type} {G : System St Op Eff} (S : Spec G) (s : St) (ops : List Op) (h : S.Inv s) : S.Inv (G.run s ops) ∧ G.effects s <+: G.effects (G.run s ops) ∧ ∀ e ∈ G.effects (G.run s ops), S.ok (G.run s ops) e
~~~

### 157. NoAgentEffects.agent_trace_inert

Source: ControlStack/Core/Gate.lean:70 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem NoAgentEffects.agent_trace_inert {St Op Eff : Type} {G : System St Op Eff} {agent : Op → Prop} (H : NoAgentEffects G agent) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, agent o) : G.effects (G.run s ops) = G.effects s
~~~

### 158. halt_absorbing

Source: ControlStack/Core/Gate.lean:97 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem halt_absorbing {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List (HOp Op)) : (withHalt G).run (s, true) ops = (s, true)
~~~

### 159. halt_freezes

Source: ControlStack/Core/Gate.lean:104 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List (HOp Op)) : (withHalt G).effects ((withHalt G).run (s, false) (.halt :: ops)) = G.effects s
~~~

## ControlStack/Core/Leakage.lean

### 160. transfer

Source: ControlStack/Core/Leakage.lean:54 | Family: F2 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem transfer {X T A : Type} [Fintype X] [Fintype T] [Fintype A] (p : X → ℝ) (lik : X → T → ℝ) (c : T → ℝ) (δ : T → A → ℝ) (u : X → A → ℝ) (b : ℝ) (hp : ∀ x, 0 ≤ p x) (hc : ∀ x t, lik x t ≤ c t) (hc0 : ∀ t, 0 ≤ c t) (hδ : ∀ t, IsDist (δ t)) (hu : ∀ x a, 0 ≤ u x a) (hb : ∀ a, ∑ x, p x * u x a ≤ b) : ∑ x, p x * ∑ t, lik x t * ∑ a, δ t a * u x a ≤ (∑ t, c t) * b
~~~

### 161. covert_from_transfer

Source: ControlStack/Core/Leakage.lean:84 | Family: F2 | Adversary: NON_ADAPTIVE | Status: SOURCE_ONLY

~~~lean
theorem covert_from_transfer {M V : Type} [Fintype M] [Fintype V] [DecidableEq M] [Nonempty M] (enc : M → V → ℝ) (dec : V → M → ℝ) (henc : ∀ m, IsDist (enc m)) (hdec : ∀ v, IsDist (dec v)) : ∑ m, (Fintype.card M : ℝ)⁻¹ * ∑ v, enc m v * ∑ a, dec v a * (if a = m then 1 else 0) ≤ (Fintype.card V : ℝ) * (Fintype.card M : ℝ)⁻¹
~~~

### 162. cval_nonneg

Source: ControlStack/Core/Leakage.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_nonneg (c : List O → O → ℝ) (B : List O → ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hB : ∀ g, 0 ≤ B g) : ∀ n g, 0 ≤ cval c B n g
~~~

### 163. cval_mono

Source: ControlStack/Core/Leakage.lean:125 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_mono (c : List O → O → ℝ) (B B' : List O → ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hBB : ∀ g, B g ≤ B' g) : ∀ n g, cval c B n g ≤ cval c B' n g
~~~

### 164. cval_wsum

Source: ControlStack/Core/Leakage.lean:131 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_wsum {X : Type} [Fintype X] (c : List O → O → ℝ) (p : X → ℝ) (B : X → List O → ℝ) : ∀ n g, ∑ x, p x * cval c (B x) n g = cval c (fun t => ∑ x, p x * B x t) n g
~~~

### 165. cval_smul

Source: ControlStack/Core/Leakage.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_smul (c : List O → O → ℝ) (b : ℝ) (B : List O → ℝ) : ∀ n g, cval c (fun t => b * B t) n g = b * cval c B n g
~~~

### 166. val_le_cval

Source: ControlStack/Core/Leakage.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_le_cval (K : List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (pay : List O → ℝ) (hK0 : ∀ h z, 0 ≤ K h z) (hdom : Dominated K c) (hc0 : ∀ g o, 0 ≤ c g o) (hpay : ∀ g, 0 ≤ pay g) : ∀ n h, val K pay n h ≤ cval c pay n (h.map Prod.snd)
~~~

### 167. seq_transfer

Source: ControlStack/Core/Leakage.lean:178 | Family: F8 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem seq_transfer {X : Type} [Fintype X] (p : X → ℝ) (K : X → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (pay : X → List O → ℝ) (B : List O → ℝ) (n : ℕ) (hp : ∀ x, 0 ≤ p x) (hK0 : ∀ x h z, 0 ≤ K x h z) (hdom : ∀ x, Dominated (K x) c) (hc0 : ∀ g o, 0 ≤ c g o) (hpay : ∀ x g, 0 ≤ pay x g) (hB : ∀ t, ∑ x, p x * pay x t ≤ B t) : ∑ x, p x * val (K x) (pay x) n [] ≤ cval c B n []
~~~

### 168. seq_transfer_const

Source: ControlStack/Core/Leakage.lean:192 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seq_transfer_const {X : Type} [Fintype X] (p : X → ℝ) (K : X → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (pay : X → List O → ℝ) (b : ℝ) (n : ℕ) (hp : ∀ x, 0 ≤ p x) (hK0 : ∀ x h z, 0 ≤ K x h z) (hdom : ∀ x, Dominated (K x) c) (hc0 : ∀ g o, 0 ≤ c g o) (hpay : ∀ x g, 0 ≤ pay x g) (hb : ∀ t, ∑ x, p x * pay x t ≤ b) : ∑ x, p x * val (K x) (pay x) n [] ≤ b * mass c n []
~~~

### 169. mass_le_prod

Source: ControlStack/Core/Leakage.lean:204 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mass_le_prod (c : List O → O → ℝ) (Lr : ℕ → ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hLr0 : ∀ i, 0 ≤ Lr i) (hL : ∀ g, ∑ o, c g o ≤ Lr g.length) : ∀ n g, mass c n g ≤ ∏ j ∈ range n, Lr (g.length + j)
~~~

### 170. mass_le_pow

Source: ControlStack/Core/Leakage.lean:224 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mass_le_pow (c : List O → O → ℝ) (L : ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hL0 : 0 ≤ L) (hL : ∀ g, ∑ o, c g o ≤ L) (n : ℕ) (g : List O) : mass c n g ≤ L ^ n
~~~

### 171. mass_const

Source: ControlStack/Core/Leakage.lean:229 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mass_const (w : O → ℝ) : ∀ n g, mass (fun _ o => w o) n g = (∑ o, w o) ^ n
~~~

### 172. covert_seq

Source: ControlStack/Core/Leakage.lean:248 | Family: F2 | Adversary: SHARED_SEED | Status: SOURCE_ONLY

~~~lean
theorem covert_seq {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (dec : Ω → List O → M → ℝ) (n : ℕ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c) (hc0 : ∀ g o, 0 ≤ c g o) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ mass c n [] / (Fintype.card M : ℝ)
~~~

### 173. covert_seq_seed

Source: ControlStack/Core/Leakage.lean:270 | Family: F2 | Adversary: SHARED_SEED | Status: SOURCE_ONLY

~~~lean
theorem covert_seq_seed {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : Ω → List O → O → ℝ) (dec : Ω → List O → M → ℝ) (n : ℕ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) (c ω)) (hc0 : ∀ ω g o, 0 ≤ c ω g o) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ (∑ ω, ρ ω * mass (c ω) n []) / (Fintype.card M : ℝ)
~~~

### 174. episode_dom

Source: ControlStack/Core/Leakage.lean:293 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem episode_dom {V S Z : Type} [Fintype V] [Fintype S] [Fintype Z] (enc : List (S × (V × Z)) → V × S → ℝ) (W : List (S × (V × Z)) → S → Z → ℝ) (cs : List (V × Z) → Z → ℝ) (henc : ∀ h, IsDist (enc h)) (hcs0 : ∀ g z, 0 ≤ cs g z) (hW : ∀ h s z, W h s z ≤ cs (h.map Prod.snd) z) : Dominated (fun h (y : S × (V × Z)) => enc h (y.2.1, y.1) * W h y.1 y.2.2) (fun g o => cs g o.2)
~~~

### 175. episode_mass

Source: ControlStack/Core/Leakage.lean:314 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem episode_mass {V Z : Type} [Fintype V] [Fintype Z] (cs : List (V × Z) → Z → ℝ) (g : List (V × Z)) : ∑ o : V × Z, cs g o.2 = (Fintype.card V : ℝ) * ∑ z, cs g z
~~~

### 176. sc01_adaptive_target

Source: ControlStack/Core/Leakage.lean:322 | Family: F2 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem sc01_adaptive_target {Ω Y Z : Type} [Fintype Ω] [Fintype Y] [Fintype Z] (ρ : Ω → ℝ) (K : Ω → Fin (2 ^ 32) → List (Y × (Option (Fin 8) × Z)) → Y × (Option (Fin 8) × Z) → ℝ) (cs : List (Option (Fin 8) × Z) → Z → ℝ) (lam : ℕ → ℝ) (dec : Ω → List (Option (Fin 8) × Z) → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) (fun g o => cs g o.2)) (hcs0 : ∀ g z, 0 ≤ cs g z) (hlam : ∀ g, ∑ z, cs g z ≤ lam g.length) (hlam0 : ∀ i, 0 ≤ lam i) (hprod : ∏ i ∈ range 5, lam i ≤ 65536 / 59049) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card (Fin (2 ^ 32)) : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) 5 []) ≤ (2 : ℝ)⁻¹ ^ 16
~~~

### 177. covert_side_bound

Source: ControlStack/Core/Leakage.lean:348 | Family: F2 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem covert_side_bound {Ω M V Y Z : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype V] [Fintype Y] [Fintype Z] (ρ : Ω → ℝ) (K : Ω → M → List (Y × (V × Z)) → Y × (V × Z) → ℝ) (cs : List (V × Z) → Z → ℝ) (lam : ℕ → ℝ) (dec : Ω → List (V × Z) → M → ℝ) (n : ℕ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) (fun g o => cs g o.2)) (hcs0 : ∀ g z, 0 ≤ cs g z) (hlam : ∀ g, ∑ z, cs g z ≤ lam g.length) (hlam0 : ∀ i, 0 ≤ lam i) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ (Fintype.card V : ℝ) ^ n * (∏ i ∈ range n, lam i) / (Fintype.card M : ℝ)
~~~

### 178. cval_live

Source: ControlStack/Core/Leakage.lean:381 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_live (st : O → Bool) (c : List O → O → ℝ) : ∀ n g, cval c (liveInd st) n g = liveInd st g * mass (dropStop st c) n g
~~~

### 179. val_congr_on

Source: ControlStack/Core/Leakage.lean:432 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_congr_on {Y O : Type} [Fintype Y] [Fintype O] (K : List (Y × O) → Y × O → ℝ) (P : List O → Prop) (pay pay' : List O → ℝ) (hP : ∀ h y o, K h (y, o) ≠ 0 → P (h.map Prod.snd) → P (h.map Prod.snd ++ [o])) (hagree : ∀ t, P t → pay t = pay' t) : ∀ n h, P (h.map Prod.snd) → val K pay n h = val K pay' n h
~~~

### 180. consistent_append

Source: ControlStack/Core/Leakage.lean:449 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem consistent_append (S : Finset (Fin N)) (g : List (AOut Z)) (o : AOut Z) (hg : Consistent S g) (ho : o.2.2 = (o.1 && decide (memN S g.length))) : Consistent S (g ++ [o])
~~~

### 181. surv_live

Source: ControlStack/Core/Leakage.lean:462 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_live (k : ℕ) (S : Finset (Fin N)) (t : List (AOut Z)) (ht : Consistent S t) : survInd k S t = survInd k S t * liveInd caughtFlag t
~~~

### 182. blind_audit

Source: ControlStack/Core/Leakage.lean:491 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem blind_audit (k B : ℕ) (hB : B ≤ N) (t : List (AOut Z)) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * survInd k S t ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

### 183. liveInd_nonneg

Source: ControlStack/Core/Leakage.lean:511 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem liveInd_nonneg {O : Type} (st : O → Bool) (t : List O) : 0 ≤ liveInd st t
~~~

### 184. survInd_nonneg

Source: ControlStack/Core/Leakage.lean:515 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survInd_nonneg (k : ℕ) (S : Finset (Fin N)) (t : List (AOut Z)) : 0 ≤ survInd k S t
~~~

### 185. audit_leak_bound_all

Source: ControlStack/Core/Leakage.lean:525 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem audit_leak_bound_all (k B : ℕ) (hB : B ≤ N) (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (hK0 : ∀ S h z, 0 ≤ K S h z) (hK1 : ∀ S h, ∑ z, K S h z ≤ 1) (hcons : ∀ S h y o, K S h (y, o) ≠ 0 → o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length))) (hdom : ∀ S h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o) (hcl0 : ∀ g o, 0 ≤ cl g o) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (K S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * mass (dropStop caughtFlag cl) N []
~~~

### 186. audit_leak_bound

Source: ControlStack/Core/Leakage.lean:579 | Family: F6 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem audit_leak_bound (k B : ℕ) (hB : B ≤ N) (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1) (hcons : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h y o, K S h (y, o) ≠ 0 → o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length))) (hdom : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o) (hcl0 : ∀ g o, 0 ≤ cl g o) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (K S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * mass (dropStop caughtFlag cl) N []
~~~

### 187. audit_leak_prod

Source: ControlStack/Core/Leakage.lean:616 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem audit_leak_prod (k B : ℕ) (hB : B ≤ N) (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (Lr : ℕ → ℝ) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1) (hcons : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h y o, K S h (y, o) ≠ 0 → o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length))) (hdom : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o) (hcl0 : ∀ g o, 0 ≤ cl g o) (hLr0 : ∀ i, 0 ≤ Lr i) (hL : ∀ g, ∑ o, dropStop caughtFlag cl g o ≤ Lr g.length) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (K S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * ∏ i ∈ range N, Lr i
~~~

### 188. audit_adaptive_hidden

Source: ControlStack/Core/Leakage.lean:644 | Family: F6 | Adversary: ADAPTIVE_FEEDBACK | Status: SOURCE_ONLY

~~~lean
theorem audit_adaptive_hidden (k B : ℕ) (hB : B ≤ N) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (hiddenK σ S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

## ControlStack/Core/Measured.lean

### 189. measured_bound

Source: ControlStack/Core/Measured.lean:55 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem measured_bound (μm : Ωm → ℝ) (hm0 : ∀ ω, 0 ≤ μm ω) (hm1 : ∑ ω, μm ω = 1) (G : Ωm → Prop) (δ b : ℝ) (hG : prob μm (fun ω => ¬ G ω) ≤ δ) (hb0 : 0 ≤ b) (f : Ωm → ℝ) (hf1 : ∀ ω, f ω ≤ 1) (hfG : ∀ ω, G ω → f ω ≤ b) : ∑ ω, μm ω * f ω ≤ b + δ
~~~

### 190. prob_le_one

Source: ControlStack/Core/Measured.lean:70 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prob_le_one (μ : Ωd → ℝ) (h0 : ∀ ω, 0 ≤ μ ω) (h1 : ∑ ω, μ ω = 1) (A : Ωd → Prop) : prob μ A ≤ 1
~~~

### 191. measured_prod

Source: ControlStack/Core/Measured.lean:78 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem measured_prod (μm : Ωm → ℝ) (hm0 : ∀ ω, 0 ≤ μm ω) (hm1 : ∑ ω, μm ω = 1) (μd : Ωd → ℝ) (hd0 : ∀ ω, 0 ≤ μd ω) (hd1 : ∑ ω, μd ω = 1) (G : Ωm → Prop) (δ b : ℝ) (hG : prob μm (fun ω => ¬ G ω) ≤ δ) (hb0 : 0 ≤ b) (bad : Ωm → Ωd → Prop) (hcert : ∀ ωm, G ωm → prob μd (bad ωm) ≤ b) : prob (fun ω : Ωm × Ωd => μm ω.1 * μd ω.2) (fun ω => bad ω.1 ω.2) ≤ b + δ
~~~

### 192. ofMeasured_ledger

Source: ControlStack/Core/Measured.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ofMeasured_ledger (μm : Ωm → ℝ) (hm0 : ∀ ω, 0 ≤ μm ω) (hm1 : ∑ ω, μm ω = 1) (μd : Ωd → ℝ) (hd0 : ∀ ω, 0 ≤ μd ω) (hd1 : ∑ ω, μd ω = 1) (procedure : String) (δ : ℚ) (G : Ωm → Prop) (bad : Ωm → Ωd → Prop) (ps : List Premise) (b : ℝ) (hb0 : 0 ≤ b) (hcert : AllHold ps → ∀ ωm, G ωm → prob μd (bad ωm) ≤ b) : let c
~~~

### 193. sum_cons

Source: ControlStack/Core/Measured.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Bool) → ℝ) : ∑ x, F x = ∑ b : Bool, ∑ y : Fin n → Bool, F (Fin.cons b y)
~~~

### 194. wB_cons

Source: ControlStack/Core/Measured.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wB_cons (p : ℝ) {n : ℕ} (b : Bool) (y : Fin n → Bool) : wB p (Fin.cons b y : Fin (n + 1) → Bool) = (if b then p else 1 - p) * wB p y
~~~

### 195. cnt_cons

Source: ControlStack/Core/Measured.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cnt_cons {n : ℕ} (b : Bool) (y : Fin n → Bool) : cnt (Fin.cons b y : Fin (n + 1) → Bool) = (if b then 1 else 0) + cnt y
~~~

### 196. wB_total

Source: ControlStack/Core/Measured.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wB_total (p : ℝ) (n : ℕ) : ∑ x : Fin n → Bool, wB p x = 1
~~~

### 197. wB_nonneg

Source: ControlStack/Core/Measured.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wB_nonneg (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) {n : ℕ} (x : Fin n → Bool) : 0 ≤ wB p x
~~~

### 198. tailP_zero

Source: ControlStack/Core/Measured.lean:158 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tailP_zero (n : ℕ) (p : ℝ) : tailP n 0 p = 1
~~~

### 199. tailP_nil

Source: ControlStack/Core/Measured.lean:161 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tailP_nil (t : ℕ) (p : ℝ) : tailP 0 (t + 1) p = 0
~~~

### 200. tailP_succ

Source: ControlStack/Core/Measured.lean:165 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tailP_succ (n t : ℕ) (p : ℝ) : tailP (n + 1) (t + 1) p = p * tailP n t p + (1 - p) * tailP n (t + 1) p
~~~

### 201. tailP_nonneg

Source: ControlStack/Core/Measured.lean:178 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tailP_nonneg (n t : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : 0 ≤ tailP n t p
~~~

### 202. tailP_anti

Source: ControlStack/Core/Measured.lean:182 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tailP_anti (n t : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : tailP n (t + 1) p ≤ tailP n t p
~~~

### 203. tailP_mono

Source: ControlStack/Core/Measured.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tailP_mono (n : ℕ) : ∀ (t : ℕ) (p p' : ℝ), 0 ≤ p → p ≤ p' → p' ≤ 1 → tailP n t p ≤ tailP n t p'
~~~

### 204. cf_zero

Source: ControlStack/Core/Measured.lean:210 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cf_zero (n : ℕ) (p : ℝ) : cf n 0 p = 1
~~~

### 205. cf_nil

Source: ControlStack/Core/Measured.lean:216 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cf_nil (t : ℕ) (p : ℝ) : cf 0 (t + 1) p = 0
~~~

### 206. cf_succ

Source: ControlStack/Core/Measured.lean:219 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cf_succ (n t : ℕ) (p : ℝ) : cf (n + 1) (t + 1) p = p * cf n t p + (1 - p) * cf n (t + 1) p
~~~

### 207. tailP_eq_cf

Source: ControlStack/Core/Measured.lean:254 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tailP_eq_cf (n : ℕ) : ∀ (t : ℕ) (p : ℝ), tailP n t p = cf n t p
~~~

### 208. cp_valid

Source: ControlStack/Core/Measured.lean:275 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cp_valid (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (rLow : ℕ → ℝ) (hr1 : ∀ s, rLow s ≤ 1) (hval : ∀ s, 0 < rLow s → tailP n s (rLow s) ≤ δ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : ∑ x : Fin n → Bool, (if p < rLow (cnt x) then wB p x else 0) ≤ δ
~~~

### 209. cp_threshold

Source: ControlStack/Core/Measured.lean:297 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cp_threshold (n s₀ : ℕ) (r₀ δ : ℝ) (hδ : 0 ≤ δ) (hr0 : 0 ≤ r₀) (hr1 : r₀ ≤ 1) (htail : tailP n s₀ r₀ ≤ δ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : ∑ x : Fin n → Bool, (if p < (if s₀ ≤ cnt x then r₀ else 0) then wB p x else 0) ≤ δ
~~~

### 210. choose_200_190

Source: ControlStack/Core/Measured.lean:316 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_200_190 : Nat.choose 200 190 = 22451004309013280
~~~

### 211. choose_200_191

Source: ControlStack/Core/Measured.lean:320 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_200_191 : Nat.choose 200 191 = 1175445251780800
~~~

### 212. choose_200_192

Source: ControlStack/Core/Measured.lean:324 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_200_192 : Nat.choose 200 192 = 55098996177225
~~~

### 213. choose_200_193

Source: ControlStack/Core/Measured.lean:328 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_200_193 : Nat.choose 200 193 = 2283896214600
~~~

### 214. choose_200_194

Source: ControlStack/Core/Measured.lean:332 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_200_194 : Nat.choose 200 194 = 82408626300
~~~

### 215. choose_200_195

Source: ControlStack/Core/Measured.lean:336 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_200_195 : Nat.choose 200 195 = 2535650040
~~~

### 216. choose_200_196

Source: ControlStack/Core/Measured.lean:340 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_200_196 : Nat.choose 200 196 = 64684950
~~~

### 217. choose_200_197

Source: ControlStack/Core/Measured.lean:344 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_200_197 : Nat.choose 200 197 = 1313400
~~~

### 218. choose_200_198

Source: ControlStack/Core/Measured.lean:348 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_200_198 : Nat.choose 200 198 = 19900
~~~

### 219. choose_200_199

Source: ControlStack/Core/Measured.lean:352 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_200_199 : Nat.choose 200 199 = 200
~~~

### 220. choose_200_200

Source: ControlStack/Core/Measured.lean:356 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem choose_200_200 : Nat.choose 200 200 = 1
~~~

### 221. tail_200_190

Source: ControlStack/Core/Measured.lean:361 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tail_200_190 : tailP 200 190 (9 / 10) ≤ 1 / 100
~~~

### 222. population_not_per_history

Source: ControlStack/Core/Measured.lean:374 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem population_not_per_history : (95 / 100 : ℝ) * 1 + 5 / 100 * 0 = 95 / 100 ∧ min (1 : ℝ) 0 = 0
~~~

### 223. strata_union

Source: ControlStack/Core/Measured.lean:379 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem strata_union {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (strata : Finset ℕ) (G : ℕ → Ω → Prop) : prob μ (fun ω => ∃ s ∈ strata, ¬ G s ω) ≤ ∑ s ∈ strata, prob μ (fun ω => ¬ G s ω)
~~~

### 224. measured_recall_example

Source: ControlStack/Core/Measured.lean:401 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem measured_recall_example {Y : Type} [Fintype Y] (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules 100 10 → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules 100 10 → ∀ h, ∑ z, K S h z ≤ 1) (homogeneous : ∀ S, S ∈ AuditBudget.randomSchedules 100 10 → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - p else 1)) : ∑ x : Fin 200 → Bool, wB p x * (if 190 ≤ cnt x then ∑ S : Finset (Fin 100), pU 100 10 S * val (K S) (recallSucc (N
~~~

### 225. ofMeasured_premises

Source: ControlStack/Core/Measured.lean:474 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ofMeasured_premises {Ωm Ωd : Type} [Fintype Ωm] [Fintype Ωd] (μm : Ωm → ℝ) (hm0 : ∀ ω, 0 ≤ μm ω) (hm1 : ∑ ω, μm ω = 1) (μd : Ωd → ℝ) (hd0 : ∀ ω, 0 ≤ μd ω) (hd1 : ∑ ω, μd ω = 1) (procedure : String) (δ : ℚ) (G : Ωm → Prop) (bad : Ωm → Ωd → Prop) (ps : List Premise) (b : ℝ) (hb0 : 0 ≤ b) (hcert : AllHold ps → ∀ ωm, G ωm → prob μd (bad ωm) ≤ b) : (ProbCert.ofMeasured μm hm0 hm1 μd hd0 hd1 procedure δ G bad ps b hb0 hcert).premises = ps ++ measuredPremises procedure δ μm G
~~~

### 226. measuredRecallLedger_eq

Source: ControlStack/Core/Measured.lean:520 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem measuredRecallLedger_eq (p : ℝ) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) : typedLedger (recallPremises p K σ) = measuredRecallLedger
~~~

### 227. recall_measured_holds

Source: ControlStack/Core/Measured.lean:525 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recall_measured_holds (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : prob (wB p) (fun x : Fin 200 → Bool => ¬ recallGood p x) ≤ ((1 / 100 : ℚ) : ℝ)
~~~

### 228. recallPremises_hold

Source: ControlStack/Core/Measured.lean:543 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recallPremises_hold (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hres : reservedProp K σ) (hhom : homogeneousProp p K σ) : AllHold (recallPremises p K σ)
~~~

### 229. measured_recall_number

Source: ControlStack/Core/Measured.lean:559 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem measured_recall_number : (91 / 100 : ℝ) ^ 5 + 1 / 100 = 6340321451 / 10 ^ 10
~~~

## ControlStack/Core/TrustRoot.lean

### 230. refinementOf_own

Source: ControlStack/Core/TrustRoot.lean:299 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refinementOf_own (sc : ℕ) (t : String) (h : refinementOf sc = some t) : ∃ d, t = refName sc d
~~~

### 231. allPrems_complete

Source: ControlStack/Core/TrustRoot.lean:345 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem allPrems_complete : ∀ p : Prem, p ∈ allPrems
~~~

### 232. graph_total

Source: ControlStack/Core/TrustRoot.lean:348 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem graph_total : ∀ s ∈ scenarios, ∀ p ∈ s.2, p ∈ allPrems
~~~

### 233. graph_discharged

Source: ControlStack/Core/TrustRoot.lean:350 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem graph_discharged : ∀ p ∈ allPrems, depsOf p ≠ []
~~~

### 234. graph_reduces

Source: ControlStack/Core/TrustRoot.lean:354 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem graph_reduces : ∀ p ∈ allPrems, rootsF fuel p = rootsF (fuel + 1) p ∧ rootsF 4 p = rootsF fuel p
~~~

### 235. scenario_roots_table

Source: ControlStack/Core/TrustRoot.lean:359 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem scenario_roots_table : scenarios.map (fun s => (s.1, scenarioRoots s.1)) = [(1, [.kernelMediation, .measuredRates, .implementationConformance]), (2, [.kernelMediation, .measuredRates]), (3, [.issuerAuthenticity, .kernelMediation, .measuredRates]), (4, [.kernelMediation, .measuredRates, .implementationConformance]), (5, [.kernelMediation, .measuredRates]), (6, [.issuerAuthenticity, .kernelMediation, .implementationConformance]), (7, [.kernelMediation, .measuredRates, .implementationConformance]), (8, [.issuerAuthenticity, .kernelMediation, .collisionResistance, .measuredRates]), (9, [.issuerAuthenticity, .kernelMediation, .measuredRates, .orgConfiguration]), (10, [.issuerAuthenticity, .kernelMediation, .measuredRates]), (11, [.issuerAuthenticity, .kernelMediation, .measuredRates]), (12, [.issuerAuthenticity, .kernelMediation, .measuredRates]), (13, [.issuerAuthenticity, .kernelMediation, .measuredRates, .implementationConformance]), (14, [.issuerAuthenticity, .monotonicAnchor, .trustedMeter, .measuredRates]), (15, [.issuerAuthenticity, .measuredRates, .humanJudgement]), (16, [.issuerAuthenticity, .kernelMediation, .collisionResistance, .measuredRates, .orgConfiguration, .implementationConformance]), (17, [.issuerAuthenticity, .kernelMediation, .measuredRates, .humanJudgement]), (18, [.issuerAuthenticity, .kernelMediation, .monotonicAnchor, .measuredRates, .implementationConformance]), (19, [.issuerAuthenticity, .monotonicAnchor, .measuredRates, .implementationConformance]), (20, [.issuerAuthenticity, .measuredRates, .humanJudgement]), (21, [.issuerAuthenticity, .kernelMediation, .keyCustody, .measuredRates]), (22, [.kernelMediation, .keyCustody, .measuredRates, .humanJudgement]), (23, [.issuerAuthenticity, .kernelMediation, .measuredRates, .implementationConformance]), (24, [.kernelMediation, .keyCustody, .measuredRates]), (25, [.issuerAuthenticity, .kernelMediation, .measuredRates, .humanJudgement, .implementationConformance]), (26, [.issuerAuthenticity, .monotonicAnchor, .measuredRates, .humanJudgement, .orgConfiguration, .implementationConformance, .externalContract]), (27, [.independentWitness, .collisionResistance, .implementationConformance]), (28, [.issuerAuthenticity, .monotonicAnchor, .trustedMeter, .measuredRates, .implementationConformance])]
~~~

### 236. portfolio_roots

Source: ControlStack/Core/TrustRoot.lean:391 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem portfolio_roots : allRoots.filter (fun r => decide (∃ s ∈ scenarios, r ∈ scenarioRoots s.1)) = allRoots ∧ (allRoots.filter Root.technical).length = 7
~~~

### 237. root_sharing

Source: ControlStack/Core/TrustRoot.lean:398 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem root_sharing : (scenarios.filter (fun s => decide (Root.measuredRates ∈ scenarioRoots s.1))).length = 26 ∧ (scenarios.filter (fun s => decide (Root.kernelMediation ∈ scenarioRoots s.1))).length = 21 ∧ (scenarios.filter (fun s => decide (Root.issuerAuthenticity ∈ scenarioRoots s.1))).length = 20 ∧ ∀ r ∈ allRoots, (scenarios.filter (fun s => decide (r ∈ scenarioRoots s.1))).length ≤ 26
~~~

### 238. correspondence_table

Source: ControlStack/Core/TrustRoot.lean:407 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem correspondence_table : (scenarios.filter (fun s => decide (Prem.modelRuntimeCorrespondence ∈ s.2))).map (fun s => (s.1, refinementOf s.1)) = [(1, none), (7, some (refName 7 "concrete_safe")), (13, none), (16, some (refName 16 "concrete_safe")), (18, some (refName 18 "concrete_safe")), (25, some (refName 25 "concrete_safe")), (26, some (refName 26 "concrete_safe")), (27, some (refName 27 "concrete_ext_safe")), (28, some (refName 28 "concrete_safe"))]
~~~

## ControlStack/CovertChannel.lean

### 239. per_seed_le

Source: ControlStack/CovertChannel.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem per_seed_le {M V : Type} [Fintype M] [Fintype V] (enc : M → V → ℝ) (dec : V → M → ℝ) (henc : ∀ m, IsDist (enc m)) (hdec : ∀ v, IsDist (dec v)) : ∑ m, ∑ v, enc m v * dec v m ≤ (Fintype.card V : ℝ)
~~~

### 240. covert_bound

Source: ControlStack/CovertChannel.lean:48 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem covert_bound {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V] [Nonempty M] (ρ : Ω → ℝ) (enc : Ω → M → V → ℝ) (dec : Ω → V → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (Fintype.card V : ℝ) / (Fintype.card M : ℝ)
~~~

### 241. covert_bound_schema

Source: ControlStack/CovertChannel.lean:63 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem covert_bound_schema {Ω M S : Type} [Fintype Ω] [Fintype M] [Fintype S] [Nonempty M] [DecidableEq S] (n : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → (Fin n → S) → ℝ) (dec : Ω → (Fin n → S) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (Fintype.card S : ℝ) ^ n / (Fintype.card M : ℝ)
~~~

### 242. attain_injective

Source: ControlStack/CovertChannel.lean:72 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attain_injective {M V : Type} [Fintype M] [Fintype V] [DecidableEq M] [DecidableEq V] [Nonempty M] (code : M → V) (decode : V → M) (hinv : ∀ m, decode (code m) = m) : successProb (Ω
~~~

### 243. design_point

Source: ControlStack/CovertChannel.lean:89 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem design_point {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → (Fin 16 → Bool) → ℝ) (dec : Ω → (Fin 16 → Bool) → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ 1 / 2 ^ 16
~~~

### 244. attain_embedding

Source: ControlStack/CovertChannel.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attain_embedding {M V : Type} [Fintype M] [Fintype V] [DecidableEq M] [DecidableEq V] [Nonempty M] [Nonempty V] (e : V → M) (he : Function.Injective e) : successProb (Ω
~~~

### 245. covert_bound_lifetime

Source: ControlStack/CovertChannel.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem covert_bound_lifetime {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] {E : ℕ} (V : Fin E → Type) [∀ e, Fintype (V e)] [∀ e, DecidableEq (V e)] (ρ : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ) (dec : Ω → ((e : Fin E) → V e) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (∏ e, (Fintype.card (V e) : ℝ)) / (Fintype.card M : ℝ)
~~~

## ControlStack/CovertNoGo.lean

### 246. controllable_leak

Source: ControlStack/CovertNoGo.lean:22 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem controllable_leak {M T V : Type} [Fintype M] [Fintype T] [DecidableEq M] [DecidableEq T] [DecidableEq V] (N : ℕ) (hN : 0 < N) (view : T → V) (realize : Fin N → T) (hdist : Function.Injective (fun i => view (realize i))) (e : Fin N → M) (he : Function.Injective e) : ∃ (enc : M → T → ℝ) (dec : V → M → ℝ), (∀ m, IsDist (enc m)) ∧ (∀ v, IsDist (dec v)) ∧ successView view enc dec = (N : ℝ) / (Fintype.card M : ℝ)
~~~

### 247. one_bit_coordinates

Source: ControlStack/CovertNoGo.lean:73 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem one_bit_coordinates {T V : Type} [Fintype T] [DecidableEq T] [DecidableEq V] (view : T → V) (t0 t1 : T) (h : view t0 ≠ view t1) : ∃ (enc : Bool → T → ℝ) (dec : V → Bool → ℝ), (∀ m, IsDist (enc m)) ∧ (∀ v, IsDist (dec v)) ∧ successView view enc dec = 1
~~~

## ControlStack/DeferGame.lean

### 248. deployV_step

Source: ControlStack/DeferGame.lean:58 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployV_step {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) : Pr[= true | deployV Bad π M D A Halt Svc b (n+1) u h] = ∑ x, Pr[= x | π h] * ∑ z, Pr[= z | M x] * (Pr[= true | D z] * Pr[= true | (if Bad x then pure true else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,true)]) : ProbComp Bool)] + Pr[= false | D z] * (if u < b then Pr[= true | (if Bad x then (fun caught => !caught) <$> A h x z else deployV Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)]) : ProbComp Bool)] else Pr[= true | (if Bad x then do let halt ← Halt h x z if halt then pure false else do let caught ← Svc h x z if caught then pure false else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) else do let halt ← Halt h x z if halt then pure false else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) : ProbComp Bool)]))
~~~

### 249. halt_then_prob

Source: ControlStack/DeferGame.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_then_prob (H K : ProbComp Bool) : Pr[= true | do let halt ← H; if halt then pure false else K] = Pr[= false | H] * Pr[= true | K]
~~~

### 250. halt_then_real

Source: ControlStack/DeferGame.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_then_real (H K : ProbComp Bool) : (Pr[= true | do let halt ← H; if halt then pure false else K]).toReal = (1 - (Pr[= true | H]).toReal) * (Pr[= true | K]).toReal
~~~

### 251. halt_service_continue_real

Source: ControlStack/DeferGame.lean:101 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_service_continue_real (H S C : ProbComp Bool) : (Pr[= true | do let halt ← H if halt then pure false else do let caught ← S if caught then pure false else C]).toReal = (1 - (Pr[= true | H]).toReal) * (1 - (Pr[= true | S]).toReal) * (Pr[= true | C]).toReal
~~~

### 252. calibrated_exhausted_benign_real

Source: ControlStack/DeferGame.lean:112 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem calibrated_exhausted_benign_real (H C : ProbComp Bool) (η : ℝ) (hH : (Pr[= true | H]).toReal = η) : (Pr[= true | do let halt ← H; if halt then pure false else C]).toReal = (1 - η) * (Pr[= true | C]).toReal
~~~

### 253. calibrated_exhausted_bad_real

Source: ControlStack/DeferGame.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem calibrated_exhausted_bad_real (H S C : ProbComp Bool) (η a c : ℝ) (hH : (Pr[= true | H]).toReal = η) (hS : (Pr[= true | S]).toReal = a) (hC : (Pr[= true | C]).toReal = c) : (Pr[= true | do let halt ← H if halt then pure false else do let caught ← S if caught then pure false else C]).toReal = (1 - η) * (1 - a) * c
~~~

### 254. calibrated_audit_escape_real

Source: ControlStack/DeferGame.lean:129 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem calibrated_audit_escape_real (A : ProbComp Bool) (r : ℝ) (hA : (Pr[= true | A]).toReal = r) : (Pr[= true | (fun caught => !caught) <$> A]).toReal = 1 - r
~~~

### 255. exhausted_benign_probability

Source: ControlStack/DeferGame.lean:159 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exhausted_benign_probability (H C : ProbComp Bool) : Pr[= true | do let halt ← H if halt then pure false else C] = Pr[= false | H] * Pr[= true | C]
~~~

### 256. exhausted_bad_then_probability

Source: ControlStack/DeferGame.lean:169 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exhausted_bad_then_probability (H S C : ProbComp Bool) : Pr[= true | do let halt ← H if halt then pure false else do let caught ← S if caught then pure false else C] = Pr[= false | H] * Pr[= false | S] * Pr[= true | C]
~~~

### 257. deployV_eq_catVE

Source: ControlStack/DeferGame.lean:200 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployV_eq_catVE {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) : ∀ n u h, Pr[= true | deployV Bad π M D A Halt Svc b n u h] = catVE Bad π M D A Halt Svc b n u h
~~~

### 258. catVE_ne_top

Source: ControlStack/DeferGame.lean:219 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_ne_top {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) : catVE Bad π M D A Halt Svc b n u h ≠ ⊤
~~~

### 259. catVE_transition_ne_top

Source: ControlStack/DeferGame.lean:229 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_transition_ne_top {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) (x : X) (z : Z) : (Pr[= true | D z] * (if Bad x then 1 else catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,true)])) + Pr[= false | D z] * (if u < b then (if Bad x then Pr[= false | A h x z] else catVE Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)])) else if Bad x then Pr[= false | Halt h x z] * Pr[= false | Svc h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) else Pr[= false | Halt h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]))) ≠ ⊤
~~~

### 260. catVE_inner_ne_top

Source: ControlStack/DeferGame.lean:274 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_inner_ne_top {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) (x : X) : (∑ z, Pr[= z | M x] * (Pr[= true | D z] * (if Bad x then 1 else catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,true)])) + Pr[= false | D z] * (if u < b then (if Bad x then Pr[= false | A h x z] else catVE Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)])) else if Bad x then Pr[= false | Halt h x z] * Pr[= false | Svc h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) else Pr[= false | Halt h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)])))) ≠ ⊤
~~~

### 261. catVE_toReal_eq_catV

Source: ControlStack/DeferGame.lean:296 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_toReal_eq_catV {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) (r η : ℝ) (a : Service X Z) (hA : ∀ h x z, Bad x → (Pr[= true | A h x z]).toReal = r) (hH : ∀ h x z, (Pr[= true | Halt h x z]).toReal = η) (hS : ∀ h x z, Bad x → (Pr[= true | Svc h x z]).toReal = a h x z) : ∀ n u h, (catVE Bad π M D A Halt Svc b n u h).toReal = catV Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D z]).toReal) (fun h x => (Pr[= x | π h]).toReal) r η a b n u h
~~~

### 262. defer_bridge

Source: ControlStack/DeferGame.lean:330 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem defer_bridge : DeferBridgeClaim
~~~

## ControlStack/DeferMono.lean

### 263. catVE_toReal_le_catV

Source: ControlStack/DeferMono.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_toReal_le_catV {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) (r η : ℝ) (a : Service X Z) (hA : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) (hH : ∀ h x z, η ≤ (Pr[= true | Halt h x z]).toReal) (hS : ∀ h x z, Bad x → a h x z ≤ (Pr[= true | Svc h x z]).toReal) : ∀ n u h, (catVE Bad π M D A Halt Svc b n u h).toReal ≤ catV Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D z]).toReal) (fun h x => (Pr[= x | π h]).toReal) r η a b n u h
~~~

### 264. defer_mono

Source: ControlStack/DeferMono.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem defer_mono : DeferMonoClaim
~~~

## ControlStack/Deployment/Contracts.lean

### 265. exclusive_sink

Source: ControlStack/Deployment/Contracts.lean:51 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exclusive_sink (d : IR) (h : Accepted d) (e : Edge) (member : e ∈ d.edges) (authority : e.authority = true) (sink : e.target = d.sink) : e.source = d.receiver
~~~

### 266. database_custody

Source: ControlStack/Deployment/Contracts.lean:55 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem database_custody (d : IR) (h : Accepted d) (e : Edge) (member : e ∈ d.edges) (authority : e.authority = true) (db : e.target = d.database) : e.source = d.receiver ∨ e.source = d.broker
~~~

### 267. runtime_exclusive

Source: ControlStack/Deployment/Contracts.lean:65 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runtime_exclusive (d : IR) (actual : List Edge) (h : Accepted d) (faithful : Faithful d actual) (e : Edge) (member : e ∈ actual) (authority : e.authority = true) (sink : e.target = d.sink) : e.source = d.receiver
~~~

### 268. agent_not_receiver_uid

Source: ControlStack/Deployment/Contracts.lean:71 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_not_receiver_uid (d : IR) (h : Accepted d) (r a : Node) (hr : r ∈ d.nodes) (rid : r.id = d.receiver) (ha : a ∈ d.nodes) (agent : a.agent = true) : a.uid ≠ r.uid
~~~

### 269. agent_call_legal

Source: ControlStack/Deployment/Contracts.lean:80 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_call_legal (d : IR) (h : Accepted d) (r a : Node) (hr : r ∈ d.nodes) (rid : r.id = d.receiver) (ha : a ∈ d.nodes) (agent : a.agent = true) (approvers admins : List Nat) (k : Nat) (tx : SC26.Tx) : SC26.legal (roles d r.uid approvers admins) (.bankCall a.uid k tx)
~~~

### 270. protocol_safe

Source: ControlStack/Deployment/Contracts.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem protocol_safe (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) (hops : ∀ o ∈ ops, SC26.legal R o) : SC26.Good R cap (SC26.run R cap SC26.full SC26.init ops)
~~~

### 271. one_use

Source: ControlStack/Deployment/Contracts.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem one_use (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) : (SC26.run R cap SC26.full SC26.init ops).reserved.Nodup
~~~

### 272. gate_contract

Source: ControlStack/Deployment/Contracts.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gate_contract (R : SC26.Roles) (cap : Nat) (ops : List {o : SC26.Op // SC26.legal R o}) : (SC26.spec R cap).Inv ((SC26.sys R cap).run SC26.init ops) ∧ (SC26.sys R cap).effects SC26.init <+: (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops) ∧ ∀ e ∈ (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops), (SC26.spec R cap).ok ((SC26.sys R cap).run SC26.init ops) e
~~~

### 273. broker_contract

Source: ControlStack/Deployment/Contracts.lean:105 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem broker_contract (R : TrustedBroker.Roles) (cap : Nat) (t : TrustedBroker.State) (trace : TrustedBroker.Trace R (TrustedBroker.initial cap) t) : TrustedBroker.Safe t
~~~

### 274. deployment_safe

Source: ControlStack/Deployment/Contracts.lean:125 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployment_safe (d : IR) (r : Node) (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) (actualEdges : List Edge) (sinkEffects : List (Nat × SC26.Tx)) (h : Accepted d) (faithful : RuntimeFaithful d r R cap ops actualEdges sinkEffects) : (∀ e ∈ actualEdges, e.authority = true → e.target = d.sink → e.source = d.receiver) ∧ (∀ e ∈ sinkEffects, ∃ req, SC26.reqOf (SC26.run R cap SC26.full SC26.init ops) e.1 = some req ∧ req.tx = e.2 ∧ e.1 ∈ (SC26.run R cap SC26.full SC26.init ops).reserved ∧ SC26.Approved R (SC26.run R cap SC26.full SC26.init ops) e.1 req) ∧ (sinkEffects.map Prod.fst).Nodup ∧ (sinkEffects.map (fun e => e.2.amount)).sum ≤ cap
~~~

### 275. clean_accepted

Source: ControlStack/Deployment/Contracts.lean:157 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem clean_accepted : Accepted clean
~~~

### 276. useful_acceptance

Source: ControlStack/Deployment/Contracts.lean:162 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem useful_acceptance : (SC26.run twoRoles 1 SC26.full SC26.init [.request 23701 payload, .approve 23703 0 payload, .execute 23701 0, .deliver 0, .arrive 0, .request 23702 payload, .approve 23703 1 payload, .execute 23702 1, .deliver 1, .arrive 1]).bank = [(0,payload)]
~~~

### 277. writable_mount_refutes

Source: ControlStack/Deployment/Contracts.lean:168 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem writable_mount_refutes : ¬ Accepted {clean with edges
~~~

### 278. unknown_refutes

Source: ControlStack/Deployment/Contracts.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unknown_refutes : ¬ Accepted {clean with edges
~~~

### 279. check_disabled_counterexample

Source: ControlStack/Deployment/Contracts.lean:176 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem check_disabled_counterexample : let s
~~~

## ControlStack/EgressGate.lean

### 280. lookup_pinned

Source: ControlStack/EgressGate.lean:26 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lookup_pinned (p : Policy) (key : String) (peer : Peer) (h : lookup p key = some peer) : peer ∈ p.map Rule.peer
~~~

### 281. direct_no_effect

Source: ControlStack/EgressGate.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem direct_no_effect (p : Policy) (s : State) (peer : Peer) (h : Invariant p s) : step p s (.directAttempt peer) = s
~~~

### 282. step_safe

Source: ControlStack/EgressGate.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_safe (p : Policy) (s : State) (a : Action) (h : Invariant p s) : Invariant p (step p s a)
~~~

### 283. trace_safe

Source: ControlStack/EgressGate.lean:126 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem trace_safe (p : Policy) (s : State) (actions : List Action) (h : Invariant p s) : Invariant p (run p s actions)
~~~

### 284. failed_launch

Source: ControlStack/EgressGate.lean:132 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem failed_launch (p : Policy) (s : State) (t : Topology) (h : safe t = false) : (step p s (.launch t)).active = false
~~~

### 285. crash_closed

Source: ControlStack/EgressGate.lean:135 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem crash_closed (p : Policy) (s : State) (key : String) : (step p (step p s .crashGateway) (.request key)).attempts = s.attempts
~~~

## ControlStack/Families/F1/FabricIsolation.lean

### 286. run_cons

Source: ControlStack/Families/F1/FabricIsolation.lean:99 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (C : Checks) (s : St) (o : Op) (ops : List Op) : run C s (o :: ops) = run C (step C s o) ops
~~~

### 287. inv_init

Source: ControlStack/Families/F1/FabricIsolation.lean:114 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init : Inv init
~~~

### 288. AccOk.mono

Source: ControlStack/Families/F1/FabricIsolation.lean:117 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem AccOk.mono {s t : St} (h : s.revoked <+: t.revoked) {a : Acc} (ha : AccOk s a) : AccOk t a
~~~

### 289. step_inv

Source: ControlStack/Families/F1/FabricIsolation.lean:123 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (s : St) (o : Op) (h : Inv s) : Inv (step full s o)
~~~

### 290. run_inv

Source: ControlStack/Families/F1/FabricIsolation.lean:189 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (s : St) (ops : List Op) (h : Inv s) : Inv (run full s ops)
~~~

### 291. fabric_safe

Source: ControlStack/Families/F1/FabricIsolation.lean:195 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fabric_safe (ops : List Op) : ∀ a ∈ (run full init ops).log, a.req = a.pd
~~~

### 292. revocation_absorbing

Source: ControlStack/Families/F1/FabricIsolation.lean:199 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem revocation_absorbing (ops : List Op) : ∀ a ∈ (run full init ops).log, a.key ∉ (run full init ops).revoked.take a.rlen
~~~

### 293. honest_access

Source: ControlStack/Families/F1/FabricIsolation.lean:205 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_access : (run full init [.register 1 0 5, .access 1 0 5]).log = [⟨1, 0, 1, 5, 0⟩]
~~~

### 294. shared_pd_breaks

Source: ControlStack/Families/F1/FabricIsolation.lean:208 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem shared_pd_breaks : (run ⟨false, true⟩ init [.register 1 0 5, .access 2 0 5]).log = [⟨2, 0, 1, 5, 0⟩] ∧ (run full init [.register 1 0 5, .access 2 0 5]).log = []
~~~

### 295. stale_key_reuse_breaks

Source: ControlStack/Families/F1/FabricIsolation.lean:215 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stale_key_reuse_breaks : let ops
~~~

### 296. dereg_blocks

Source: ControlStack/Families/F1/FabricIsolation.lean:222 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dereg_blocks : (run full init [.register 1 0 5, .dereg 1 0, .access 1 0 5]).log = []
~~~

### 297. guess_bound

Source: ControlStack/Families/F1/FabricIsolation.lean:227 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem guess_bound (K : ℕ) (hK : 0 < K) (g : List (Fin K)) : ((Finset.univ.filter (fun k : Fin K => k ∈ g)).card : ℝ) / K ≤ g.length / K
~~~

### 298. guess_example

Source: ControlStack/Families/F1/FabricIsolation.lean:236 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem guess_example (g : List (Fin (2 ^ 64))) (hg : g.length ≤ 2 ^ 20) : ((Finset.univ.filter (fun k : Fin (2 ^ 64) => k ∈ g)).card : ℝ) / (2 ^ 64 : ℕ) ≤ 1 / 2 ^ 44
~~~

## ControlStack/Families/F2/ChannelInstances.lean

### 299. covert_rounds

Source: ControlStack/Families/F2/ChannelInstances.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem covert_rounds (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (Lr : ℕ → ℝ) (dec : Ω → List O → M → ℝ) (n : ℕ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c) (hc0 : ∀ g o, 0 ≤ c g o) (hLr0 : ∀ i, 0 ≤ Lr i) (hL : ∀ g, ∑ o, c g o ≤ Lr g.length) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ (∏ i ∈ range n, Lr i) / (Fintype.card M : ℝ)
~~~

### 300. covert_alphabet

Source: ControlStack/Families/F2/ChannelInstances.lean:79 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem covert_alphabet (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (dec : Ω → List O → M → ℝ) (n : ℕ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hK1 : ∀ ω m h, ∑ z, K ω m h z ≤ 1) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ (Fintype.card O : ℝ) ^ n / (Fintype.card M : ℝ)
~~~

### 301. sc02_accumulated

Source: ControlStack/Families/F2/ChannelInstances.lean:105 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem sc02_accumulated (k E : ℕ) (ρ : Ω → ℝ) (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (L : ℕ → ℝ) (dec : Ω → List O → Fin (2 ^ k) → ℝ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c) (hc0 : ∀ g o, 0 ≤ c g o) (hL0 : ∀ i, 0 ≤ L i) (hL : ∀ g, ∑ o, c g o ≤ L g.length) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * (((2 : ℝ) ^ k)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) E []) ≤ (∏ e ∈ range E, L e) / 2 ^ k
~~~

### 302. prod_epoch

Source: ControlStack/Families/F2/ChannelInstances.lean:116 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prod_epoch (n a E : ℕ) (L : ℝ) (h : a + E ≤ n) : ∏ i ∈ range n, (if a ≤ i ∧ i < a + E then L else 1) = L ^ E
~~~

### 303. rekey_epoch

Source: ControlStack/Families/F2/ChannelInstances.lean:130 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rekey_epoch {M : Type} [Fintype M] [Nonempty M] (n a E : ℕ) (hE : a + E ≤ n) (L : ℝ) (hL0 : 0 ≤ L) (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (dec : Ω → List O → M → ℝ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c) (hc0 : ∀ g o, 0 ≤ c g o) (hin : ∀ g, a ≤ g.length ∧ g.length < a + E → ∑ o, c g o ≤ L) (hout : ∀ g, ¬(a ≤ g.length ∧ g.length < a + E) → ∑ o, c g o ≤ 1) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ L ^ E / (Fintype.card M : ℝ)
~~~

### 304. sc02_example

Source: ControlStack/Families/F2/ChannelInstances.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc02_example : ((21 : ℝ) / 20) ^ 20 / 2 ^ 16 ≤ 1 / 20000
~~~

### 305. sc02_no_rekey

Source: ControlStack/Families/F2/ChannelInstances.lean:153 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc02_no_rekey : (1 : ℝ) / 4 ≤ ((21 : ℝ) / 20) ^ 200 / 2 ^ 16
~~~

### 306. canonical_seq

Source: ControlStack/Families/F2/ChannelInstances.lean:162 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem canonical_seq {Ω M Y : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] (Kc m : ℕ) (ρ : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ) (dec : Ω → List (Fin Kc) → M → ℝ) (hρ : IsDist ρ) (hK0 : ∀ ω x h z, 0 ≤ K ω x h z) (hK1 : ∀ ω x h, ∑ z, K ω x h z ≤ 1) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ x, val (K ω x) (fun t => dec ω t x) m []) ≤ (Kc : ℝ) ^ m / (Fintype.card M : ℝ)
~~~

### 307. log_channel

Source: ControlStack/Families/F2/ChannelInstances.lean:176 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem log_channel {Ω M Y : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] (Kt f Q m : ℕ) (ρ : Ω → ℝ) (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) → Y × (Fin Kt × (Fin f → Fin Q)) → ℝ) (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ) (hρ : IsDist ρ) (hK0 : ∀ ω x h z, 0 ≤ K ω x h z) (hK1 : ∀ ω x h, ∑ z, K ω x h z ≤ 1) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ x, val (K ω x) (fun t => dec ω t x) m []) ≤ (Kt : ℝ) ^ m * (Q : ℝ) ^ (f * m) / (Fintype.card M : ℝ)
~~~

### 308. log_example

Source: ControlStack/Families/F2/ChannelInstances.lean:188 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem log_example : ((8 : ℝ) ^ 4 * (4 : ℝ) ^ (2 * 4)) / 2 ^ 64 = 1 / 2 ^ 36
~~~

### 309. free_text_leaks

Source: ControlStack/Families/F2/ChannelInstances.lean:192 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem free_text_leaks (n : ℕ) : successProb (Ω
~~~

### 310. gpu_bound

Source: ControlStack/Families/F2/ChannelInstances.lean:216 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gpu_bound {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] (m : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → List (Bool × Fin J) → Bool → ℝ) (W : Bool → Fin J → ℝ) (dec : Ω → List (Fin J) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω x h, IsDist (enc ω x h)) (hW : ∀ s o, 0 ≤ W s o) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ x, val (gpuK enc W ω x) (fun t => dec ω t x) m []) ≤ (∑ o, wmax W o) ^ m / (Fintype.card M : ℝ)
~~~

### 311. gpu_partition

Source: ControlStack/Families/F2/ChannelInstances.lean:241 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gpu_partition (W : Bool → Fin J → ℝ) (hW : IsDist (W false)) (hsame : ∀ o, W true o = W false o) : ∑ o, wmax W o = 1
~~~

### 312. gpu_jitter

Source: ControlStack/Families/F2/ChannelInstances.lean:248 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gpu_jitter (W : Bool → Fin J → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hW : IsDist (W false)) (hratio : ∀ o, W true o ≤ (1 + δ) * W false o) : ∑ o, wmax W o ≤ 1 + δ
~~~

### 313. gpuW_mass

Source: ControlStack/Families/F2/ChannelInstances.lean:261 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gpuW_mass : ∑ o, wmax gpuW o = 14 / 10
~~~

### 314. gpu_example

Source: ControlStack/Families/F2/ChannelInstances.lean:266 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gpu_example {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 16) → List (Bool × Fin 4) → Bool → ℝ) (dec : Ω → List (Fin 4) → Fin (2 ^ 16) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω x h, IsDist (enc ω x h)) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card (Fin (2 ^ 16)) : ℝ)⁻¹ * ∑ x, val (gpuK enc gpuW ω x) (fun t => dec ω t x) 10 []) ≤ 1 / 2000
~~~

### 315. gpu_jitter_example

Source: ControlStack/Families/F2/ChannelInstances.lean:284 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gpu_jitter_example : ∑ o, wmax gpuWj o = 102 / 100 ∧ ∑ o, wmax gpuWj o ≤ 1 + 1 / 12
~~~

## ControlStack/Families/F2/GPUResidue.lean

### 316. run_cons

Source: ControlStack/Families/F2/GPUResidue.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (small : ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) : run small C s (o :: ops) = run small C (step small C s o) ops
~~~

### 317. ownerOf_cons

Source: ControlStack/Families/F2/GPUResidue.lean:103 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ownerOf_cons {s t : St} {p : ℕ} {x : Option ℕ} (ht : t.owner = (p, x) :: s.owner) (q : ℕ) : ownerOf t q = if p = q then x else ownerOf s q
~~~

### 318. cellOf_cons

Source: ControlStack/Families/F2/GPUResidue.lean:108 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cellOf_cons {s t : St} {p : ℕ} {c : Cell} (ht : t.mem = (p, c) :: s.mem) (q : ℕ) : cellOf t q = if p = q then c else cellOf s q
~~~

### 319. cellOf_owner

Source: ControlStack/Families/F2/GPUResidue.lean:113 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem cellOf_owner (s : St) (o : List (ℕ × Option ℕ)) (q : ℕ) : cellOf { s with owner
~~~

### 320. ownerOf_mem

Source: ControlStack/Families/F2/GPUResidue.lean:116 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem ownerOf_mem (s : St) (m : List (ℕ × Cell)) (q : ℕ) : ownerOf { s with mem
~~~

### 321. inv_init

Source: ControlStack/Families/F2/GPUResidue.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (C : Checks) : Inv C init
~~~

### 322. step_inv

Source: ControlStack/Families/F2/GPUResidue.lean:131 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (small : ℕ) (C : Checks) (hC : Sound C) (s : St) (o : Op) (h : Inv C s) : Inv C (step small C s o)
~~~

### 323. run_inv

Source: ControlStack/Families/F2/GPUResidue.lean:219 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (small : ℕ) (C : Checks) (hC : Sound C) (s : St) (ops : List Op) (h : Inv C s) : Inv C (run small C s ops)
~~~

### 324. residue_safe

Source: ControlStack/Families/F2/GPUResidue.lean:227 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem residue_safe (small : ℕ) (C : Checks) (hC : Sound C) (ops : List Op) : ∀ r ∈ (run small C init ops).reads, ReadOk r
~~~

### 325. ownerOf_congr

Source: ControlStack/Families/F2/GPUResidue.lean:245 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ownerOf_congr {s t : St} (h : s.owner = t.owner) (p : ℕ) : ownerOf s p = ownerOf t p
~~~

### 326. step_rel

Source: ControlStack/Families/F2/GPUResidue.lean:248 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_rel (small : ℕ) (C : Checks) (A : ℕ) (s t : St) (hs : Inv C s) (o o' : Op) (ho : SameExceptA A o o') (h : Rel A s t) : Rel A (step small C s o) (step small C t o')
~~~

### 327. step_rel_inv

Source: ControlStack/Families/F2/GPUResidue.lean:340 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_rel_inv (small : ℕ) (C : Checks) (hC : Sound C) (A : ℕ) (ops ops' : List Op) (h : List.Forall₂ (SameExceptA A) ops ops') : ∀ s t, Inv C s → Rel A s t → Rel A (run small C s ops) (run small C t ops')
~~~

### 328. noninterference

Source: ControlStack/Families/F2/GPUResidue.lean:352 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem noninterference (small : ℕ) (C : Checks) (hC : Sound C) (A : ℕ) (ops ops' : List Op) (h : List.Forall₂ (SameExceptA A) ops ops') : (run small C init ops).reads.filter (fun r => r.tenant ≠ A) = (run small C init ops').reads.filter (fun r => r.tenant ≠ A)
~~~

### 329. no_scrub_residue

Source: ControlStack/Families/F2/GPUResidue.lean:363 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_scrub_residue : (run 16 ⟨false, false, false⟩ init (trace 64)).reads = [⟨2, 0, 42, some 1⟩]
~~~

### 330. fast_path_skip_residue

Source: ControlStack/Families/F2/GPUResidue.lean:367 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fast_path_skip_residue : (run 16 ⟨true, false, true⟩ init (trace 8)).reads = [⟨2, 0, 42, some 1⟩] ∧ (run 16 ⟨true, false, true⟩ init (trace 64)).reads = [⟨2, 0, 0, none⟩]
~~~

### 331. scrub_on_alloc_clean

Source: ControlStack/Families/F2/GPUResidue.lean:372 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem scrub_on_alloc_clean : (run 16 full init (trace 8)).reads = [⟨2, 0, 0, none⟩]
~~~

### 332. scrub_on_free_clean

Source: ControlStack/Families/F2/GPUResidue.lean:374 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem scrub_on_free_clean : (run 16 ⟨false, true, false⟩ init (trace 8)).reads = [⟨2, 0, 0, none⟩]
~~~

### 333. run_cons

Source: ControlStack/Families/F2/GPUResidue.lean:402 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (clear : Bool) (s : St) (o : Op) (ops : List Op) : run clear s (o :: ops) = run clear (step clear s o) ops
~~~

### 334. cellOf_ok

Source: ControlStack/Families/F2/GPUResidue.lean:409 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cellOf_ok (s : St) (h : ∀ e ∈ s.scratch, e.2.writer = some s.cur) (a : ℕ) : (cellOf s a).writer = none ∨ (cellOf s a).writer = some s.cur
~~~

### 335. step_inv

Source: ControlStack/Families/F2/GPUResidue.lean:416 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (s : St) (o : Op) (h : Inv s) : Inv (step true s o)
~~~

### 336. slice_safe

Source: ControlStack/Families/F2/GPUResidue.lean:433 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem slice_safe (s : St) (hs : Inv s) (ops : List Op) : ∀ r ∈ (run true s ops).reads, ReadOk r
~~~

### 337. inv_init

Source: ControlStack/Families/F2/GPUResidue.lean:440 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init : Inv init
~~~

### 338. no_clear_leaks

Source: ControlStack/Families/F2/GPUResidue.lean:443 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_clear_leaks : (run false init [.switch 1, .write 0 42, .switch 2, .read 0]).reads = [⟨2, 0, 42, some 1⟩] ∧ (run true init [.switch 1, .write 0 42, .switch 2, .read 0]).reads = [⟨2, 0, 0, none⟩]
~~~

## ControlStack/Families/F2/TimedRelease.lean

### 339. slot_inv

Source: ControlStack/Families/F2/TimedRelease.lean:114 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem slot_inv (L : ℕ) (A : List Msg) (g : GSt) (a : List Msg) (h : Inv L A g) : Inv L (A ++ a.filter (ok (D L))) (slot (D L) g a)
~~~

### 340. fold_inv

Source: ControlStack/Families/F2/TimedRelease.lean:143 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fold_inv (L : ℕ) (l : List (List Msg)) : ∀ (A : List Msg) (g : GSt), Inv L A g → Inv L (A ++ acc (D L) l) (l.foldl (slot (D L)) g)
~~~

### 341. fold_length

Source: ControlStack/Families/F2/TimedRelease.lean:152 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fold_length (C : Cfg) (l : List (List Msg)) (g : GSt) : (l.foldl (slot C) g).out.length = g.out.length + l.length
~~~

### 342. view_length

Source: ControlStack/Families/F2/TimedRelease.lean:165 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem view_length (C : Cfg) (sched : List (List Msg)) : (view C sched).length = sched.length
~~~

### 343. view_shape

Source: ControlStack/Families/F2/TimedRelease.lean:170 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem view_shape (L : ℕ) (sched : List (List Msg)) : ∃ k, k ≤ (acc (D L) sched).length ∧ k ≤ sched.length ∧ view (D L) sched = render L (((acc (D L) sched).map Msg.content).take k) sched.length
~~~

### 344. acc_take_prefix

Source: ControlStack/Families/F2/TimedRelease.lean:194 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem acc_take_prefix (C : Cfg) (sched : List (List Msg)) (i : ℕ) : acc C (sched.take i) <+: acc C sched
~~~

### 345. acc_take_succ

Source: ControlStack/Families/F2/TimedRelease.lean:198 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem acc_take_succ (C : Cfg) (sched : List (List Msg)) (i : ℕ) (hi : i < sched.length) : acc C (sched.take (i + 1)) = acc C (sched.take i) ++ (sched[i]).filter (ok C)
~~~

### 346. ready_state

Source: ControlStack/Families/F2/TimedRelease.lean:205 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ready_state (L : ℕ) (sched : List (List Msg)) (hr : Ready L sched) : ∀ i, i ≤ sched.length → (sched.take i).foldl (slot (D L)) g0 = ⟨(acc (D L) (sched.take i)).drop (min i (acc (D L) sched).length), ((acc (D L) (sched.take i)).take (min i (acc (D L) sched).length)).map (frameOf (D L)) ++ List.replicate (i - min i (acc (D L) sched).length) .dummy, decide ((acc (D L) sched).length < i)⟩ ∧ min i (acc (D L) sched).length ≤ (acc (D L) (sched.take i)).length
~~~

### 347. ready_view

Source: ControlStack/Families/F2/TimedRelease.lean:282 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ready_view (L : ℕ) (sched : List (List Msg)) (hr : Ready L sched) : view (D L) sched = render L (((acc (D L) sched).map Msg.content).take (min sched.length (acc (D L) sched).length)) sched.length
~~~

### 348. timing_noninterference

Source: ControlStack/Families/F2/TimedRelease.lean:295 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem timing_noninterference (L : ℕ) (s₁ s₂ : List (List Msg)) (h₁ : Ready L s₁) (h₂ : Ready L s₂) (hlen : s₁.length = s₂.length) (hcs : (acc (D L) s₁).map Msg.content = (acc (D L) s₂).map Msg.content) : view (D L) s₁ = view (D L) s₂
~~~

### 349. ready_latency

Source: ControlStack/Families/F2/TimedRelease.lean:306 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ready_latency (L : ℕ) (sched : List (List Msg)) (hr : Ready L sched) (j : ℕ) (hj : j < min sched.length (acc (D L) sched).length) : (view (D L) sched)[j]? = some (.data ((acc (D L) sched)[j]'(by omega)).content L)
~~~

### 350. throughput

Source: ControlStack/Families/F2/TimedRelease.lean:316 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem throughput (L : ℕ) (sched : List (List Msg)) : (view (D L) sched).length = sched.length ∧ ∀ f ∈ view (D L) sched, f = .dummy ∨ ∃ c, f = .data c L
~~~

### 351. timed_leakage

Source: ControlStack/Families/F2/TimedRelease.lean:331 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem timed_leakage {M : Type} [Fintype M] [DecidableEq M] (L S K : ℕ) (hK : 0 < K) (enc : M → List (List Msg)) (hlen : ∀ m, (enc m).length = S) (hcls : ∀ m, ∀ x ∈ acc (D L) (enc m), x.content < K) (dec : List Frame → M) : (univ.filter (fun m => dec (view (D L) (enc m)) = m)).card ≤ (S + 1) * K ^ S
~~~

### 352. release_on_arrival_leaks_timing

Source: ControlStack/Families/F2/TimedRelease.lean:384 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem release_on_arrival_leaks_timing : onArrival (D 8) early ≠ onArrival (D 8) spread ∧ view (D 8) early = view (D 8) spread
~~~

### 353. variable_size_leaks

Source: ControlStack/Families/F2/TimedRelease.lean:389 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem variable_size_leaks : view ⟨8, false, true, none⟩ [[⟨5, 3⟩]] ≠ view ⟨8, false, true, none⟩ [[⟨5, 7⟩]] ∧ view (D 8) [[⟨5, 3⟩]] = view (D 8) [[⟨5, 7⟩]]
~~~

### 354. overflow_leaks_timing

Source: ControlStack/Families/F2/TimedRelease.lean:397 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem overflow_leaks_timing : view ⟨8, true, false, some 1⟩ early ≠ view ⟨8, true, false, some 1⟩ spread ∧ view (D 8) early = view (D 8) spread
~~~

## ControlStack/Families/F3/DistributedHalt.lean

### 355. sum_window

Source: ControlStack/Families/F3/DistributedHalt.lean:57 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_window (T ρ lo hi : ℕ) (e : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P] (he : ∀ t, e t ≤ ρ) (hz : ∀ t, P t → e t ≠ 0 → lo ≤ t ∧ t < hi) : ∑ t ∈ range T, (if P t then e t else 0) ≤ ρ * (hi - lo)
~~~

### 356. initiated_after_le

Source: ControlStack/Families/F3/DistributedHalt.lean:104 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem initiated_after_le (n T t0 ρ Δ : ℕ) (e : ℕ → ℕ → ℕ) (δ : ℕ → ℕ) (hr : Rate ρ e) (hh : HaltAbsorbs t0 δ e) (hd : Delivered n Δ δ) : initiatedAfter n T t0 e ≤ ∑ i ∈ range n, ρ * δ i ∧ initiatedAfter n T t0 e ≤ n * ρ * Δ
~~~

### 357. landed_after_le

Source: ControlStack/Families/F3/DistributedHalt.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem landed_after_le (n T t0 ρ Δ L : ℕ) (e lat : ℕ → ℕ → ℕ) (δ : ℕ → ℕ) (hr : Rate ρ e) (hh : HaltAbsorbs t0 δ e) (hd : Delivered n Δ δ) (hl : Latency L lat) : landedAfter n T t0 e lat ≤ n * ρ * (L + Δ)
~~~

### 358. foldl_sublist

Source: ControlStack/Families/F3/DistributedHalt.lean:143 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_sublist (fence : Bool) (t0 ε e0 G : ℕ) : ∀ (evs : List (ℕ × ℕ)) (s : List (ℕ × ℕ)), ∃ l, evs.foldl (sinkStep fence t0 ε e0 G) s = s ++ l ∧ l.Sublist (evs.filter (accepts fence t0 ε e0))
~~~

### 359. foldl_len

Source: ControlStack/Families/F3/DistributedHalt.lean:166 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_len (fence : Bool) (t0 ε e0 G : ℕ) : ∀ (evs : List (ℕ × ℕ)) (s : List (ℕ × ℕ)), s.length ≤ G → (evs.foldl (sinkStep fence t0 ε e0 G) s).length ≤ G
~~~

### 360. sink_sublist

Source: ControlStack/Families/F3/DistributedHalt.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sink_sublist (fence : Bool) (t0 ε e0 G : ℕ) (evs : List (ℕ × ℕ)) : (sinkRun fence t0 ε e0 G evs).Sublist (evs.filter (accepts fence t0 ε e0))
~~~

### 361. sink_budget

Source: ControlStack/Families/F3/DistributedHalt.lean:189 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sink_budget (fence : Bool) (t0 ε e0 G : ℕ) (evs : List (ℕ × ℕ)) : (sinkRun fence t0 ε e0 G evs).length ≤ G
~~~

### 362. sink_count

Source: ControlStack/Families/F3/DistributedHalt.lean:193 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sink_count (fence : Bool) (t0 ε e0 G : ℕ) (evs : List (ℕ × ℕ)) (q : ℕ × ℕ → Bool) : (sinkRun fence t0 ε e0 G evs).countP q ≤ evs.countP (fun ev => q ev && accepts fence t0 ε e0 ev)
~~~

### 363. fenced_after_eps

Source: ControlStack/Families/F3/DistributedHalt.lean:201 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fenced_after_eps (t0 ε e0 G : ℕ) (evs : List (ℕ × ℕ)) (hold : ∀ ev ∈ evs, ev.2 ≤ e0) : (sinkRun true t0 ε e0 G evs).countP (fun ev => decide (t0 + ε ≤ ev.1)) = 0
~~~

### 364. listsum_range

Source: ControlStack/Families/F3/DistributedHalt.lean:219 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem listsum_range (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i
~~~

### 365. stream_countP

Source: ControlStack/Families/F3/DistributedHalt.lean:224 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stream_countP (n T : ℕ) (e lat ep : ℕ → ℕ → ℕ) (q : ℕ × ℕ → Bool) : (stream n T e lat ep).countP q = ∑ i ∈ range n, ∑ t ∈ range T, (if q (t + lat i t, ep i t) = true then e i t else 0)
~~~

### 366. stream_epochs

Source: ControlStack/Families/F3/DistributedHalt.lean:239 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stream_epochs (n T : ℕ) (e lat ep : ℕ → ℕ → ℕ) (e0 : ℕ) (hold : HoldsOld e0 ep) : ∀ ev ∈ stream n T e lat ep, ev.2 ≤ e0
~~~

### 367. fenced_window

Source: ControlStack/Families/F3/DistributedHalt.lean:248 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fenced_window (n T t0 ε e0 G ρ L : ℕ) (e lat ep : ℕ → ℕ → ℕ) (hr : Rate ρ e) (hl : Latency L lat) (hold : HoldsOld e0 ep) : (sinkRun true t0 ε e0 G (stream n T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) ≤ n * ρ * (L + ε)
~~~

### 368. unfenced_composed

Source: ControlStack/Families/F3/DistributedHalt.lean:270 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unfenced_composed (n T t0 ε e0 G ρ Δ L : ℕ) (e lat ep : ℕ → ℕ → ℕ) (δ : ℕ → ℕ) (hr : Rate ρ e) (hh : HaltAbsorbs t0 δ e) (hd : Delivered n Δ δ) (hl : Latency L lat) : (sinkRun false t0 ε e0 G (stream n T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) ≤ min G (n * ρ * (L + Δ))
~~~

### 369. fenced_composed

Source: ControlStack/Families/F3/DistributedHalt.lean:285 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fenced_composed (n T t0 ε e0 G ρ L : ℕ) (e lat ep : ℕ → ℕ → ℕ) (hr : Rate ρ e) (hl : Latency L lat) (hold : HoldsOld e0 ep) : (sinkRun true t0 ε e0 G (stream n T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) ≤ min G (n * ρ * (L + ε)) ∧ (sinkRun true t0 ε e0 G (stream n T e lat ep)).countP (fun ev => decide (t0 + ε ≤ ev.1)) = 0
~~~

### 370. foldl_all

Source: ControlStack/Families/F3/DistributedHalt.lean:295 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_all (fence : Bool) (t0 ε e0 G : ℕ) : ∀ (evs s : List (ℕ × ℕ)), (∀ ev ∈ evs, accepts fence t0 ε e0 ev = true) → s.length + evs.length ≤ G → evs.foldl (sinkStep fence t0 ε e0 G) s = s ++ evs
~~~

### 371. partition_count

Source: ControlStack/Families/F3/DistributedHalt.lean:315 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem partition_count (T t0 : ℕ) : ∑ i ∈ range 1, ∑ t ∈ range T, (if t0 ≤ t + 0 then partitionE i t else 0) = T - t0
~~~

### 372. stream_length

Source: ControlStack/Families/F3/DistributedHalt.lean:322 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stream_length (n T : ℕ) (e lat ep : ℕ → ℕ → ℕ) : (stream n T e lat ep).length = ∑ i ∈ range n, ∑ t ∈ range T, e i t
~~~

### 373. partition_unbounded

Source: ControlStack/Families/F3/DistributedHalt.lean:329 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem partition_unbounded (t0 ε e0 M : ℕ) : ∃ T, M < (sinkRun false t0 ε e0 (T + 1) (stream 1 T partitionE (fun _ _ => 0) (fun _ _ => e0))).countP (fun ev => decide (t0 ≤ ev.1))
~~~

### 374. partition_fenced

Source: ControlStack/Families/F3/DistributedHalt.lean:346 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem partition_fenced (t0 ε e0 G T : ℕ) : (sinkRun true t0 ε e0 G (stream 1 T partitionE (fun _ _ => 0) (fun _ _ => e0))).countP (fun ev => decide (t0 ≤ ev.1)) ≤ ε
~~~

### 375. token_leak

Source: ControlStack/Families/F3/DistributedHalt.lean:355 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem token_leak (t0 ε e0 : ℕ) : (sinkRun true t0 ε e0 1 [(t0 + ε, e0 + 1)]).countP (fun ev => decide (t0 + ε ≤ ev.1)) = 1
~~~

### 376. example_unfenced

Source: ControlStack/Families/F3/DistributedHalt.lean:362 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem example_unfenced (T t0 ε e0 G : ℕ) (e lat ep : ℕ → ℕ → ℕ) (δ : ℕ → ℕ) (hr : Rate 10 e) (hh : HaltAbsorbs t0 δ e) (hd : Delivered 1000 5 δ) (hl : Latency 0 lat) : (sinkRun false t0 ε e0 G (stream 1000 T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) ≤ 50000
~~~

### 377. example_fenced

Source: ControlStack/Families/F3/DistributedHalt.lean:368 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem example_fenced (T t0 e0 G : ℕ) (e lat ep : ℕ → ℕ → ℕ) (hr : Rate 10 e) (hl : Latency 0 lat) (hold : HoldsOld e0 ep) : (sinkRun true t0 1 e0 G (stream 1000 T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) ≤ 10000 ∧ (sinkRun true t0 1 e0 G (stream 1000 T e lat ep)).countP (fun ev => decide (t0 + 1 ≤ ev.1)) = 0
~~~

## ControlStack/Families/F4/AttestedKeyRelease.lean

### 378. run_snoc

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:157 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_snoc (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (l : List Op) (o : Op) : run A W C s (l ++ [o]) = step A W C (run A W C s l) o
~~~

### 379. codeOf_some

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:161 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem codeOf_some {s : St} {k c : ℕ} (h : codeOf s k = some c) : (k, c) ∈ s.sessions
~~~

### 380. codeOf_of_mem

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem codeOf_of_mem {s : St} {k c : ℕ} (h : (k, c) ∈ s.sessions) (huniq : ∀ p ∈ s.sessions, ∀ q ∈ s.sessions, p.1 = q.1 → p.2 = q.2) : codeOf s k = some c
~~~

### 381. inv_init

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:205 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (W : ℕ) (a0 : List ℕ) : Inv W (init a0)
~~~

### 382. step_inv

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:208 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (A : List ℕ) (W : ℕ) (s : St) (o : Op) (h : Inv W s) : Inv W (step A W full s o)
~~~

### 383. run_inv

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:380 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (A : List ℕ) (W : ℕ) (s : St) (ops : List Op) (h : Inv W s) : Inv W (run A W full s ops)
~~~

### 384. step_rels

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:387 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_rels (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (o : Op) : ∀ e ∈ (step A W C s o).rels, e ∈ s.rels ∨ ∃ pk r, o = .request pk r ∧ Pass C W s pk r ∧ e = (pk, r, s.now)
~~~

### 385. rels_sound

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:406 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rels_sound (A : List ℕ) (W : ℕ) (C : Cfg) (s0 : St) (ops : List Op) : ∀ e ∈ (run A W C s0 ops).rels, e ∈ s0.rels ∨ ∃ j, ∃ hj : j < ops.length, ops[j] = .request e.1 e.2.1 ∧ Pass C W (run A W C s0 (ops.take j)) e.1 e.2.1 ∧ e.2.2 = (run A W C s0 (ops.take j)).now
~~~

### 386. pass_full

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:431 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pass_full (W : ℕ) (s : St) (pk : ℕ) (r : Report) (h : Pass full W s pk r) : Attested W s pk r
~~~

### 387. weights_only_in_attested

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:440 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem weights_only_in_attested (A : List ℕ) (W : ℕ) (a0 : List ℕ) (ops : List Op) : ∀ d ∈ (run A W full (init a0) ops).decs, ∃ j, ∃ hj : j < ops.length, ∃ r : Report, ops[j] = .request d.1 r ∧ Attested W (run A W full (init a0) (ops.take j)) d.1 r ∧ r.meas = d.2.1
~~~

### 388. allow_clean

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:451 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem allow_clean (A : List ℕ) (W : ℕ) (C : Cfg) (debug : List ℕ) (s : St) (ops : List Op) (h0 : ∀ m ∈ s.allow, m ∉ debug) (hops : ∀ c m, Op.allowAdd c m ∈ ops → m ∉ debug) : ∀ m ∈ (run A W C s ops).allow, m ∉ debug
~~~

### 389. no_debug_decrypt

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:479 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_debug_decrypt (A : List ℕ) (W : ℕ) (a0 debug : List ℕ) (ops : List Op) (h0 : ∀ m ∈ a0, m ∉ debug) (hops : ∀ c m, Op.allowAdd c m ∈ ops → m ∉ debug) : ∀ d ∈ (run A W full (init a0) ops).decs, d.2.1 ∉ debug
~~~

### 390. revoked_mono

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:488 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem revoked_mono (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (ops : List Op) (m : ℕ) (hm : m ∈ s.revoked) : m ∈ (run A W C s ops).revoked
~~~

### 391. revocation_absorbing

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:506 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem revocation_absorbing (A : List ℕ) (W : ℕ) (s : St) (hs : Inv W s) (m : ℕ) (hm : m ∈ s.revoked) (ops : List Op) : m ∉ (run A W full s ops).allow ∧ ∀ e ∈ (run A W full s ops).rels, e ∈ s.rels ∨ e.2.1.meas ≠ m
~~~

### 392. replay_window

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:520 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem replay_window (A : List ℕ) (W : ℕ) (a0 : List ℕ) (ops : List Op) : ∀ e ∈ (run A W full (init a0) ops).rels, ∀ a ∈ (run A W full (init a0) ops).adv, e.1 = a.1 → e.2.2 ≤ a.2 + W
~~~

### 393. leak_needs_release

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:525 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem leak_needs_release (A : List ℕ) (W : ℕ) (a0 : List ℕ) (ops : List Op) : ∀ l ∈ (run A W full (init a0) ops).leaks, (∃ a ∈ (run A W full (init a0) ops).adv, a.1 = l.1) ∧ ∃ e ∈ (run A W full (init a0) ops).rels, e.1 = l.1
~~~

### 394. honest_liveness

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:533 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_liveness (A : List ℕ) (W : ℕ) (s : St) (hs : Inv W s) (k c : ℕ) (hk : (k, c) ∈ s.sessions) (hc : c ∈ s.allow) : (k, c, s.now) ∈ (run A W full s [.issue, .quote k s.nextNonce, .request k ⟨c, s.nextNonce, k⟩, .decrypt k]).decs
~~~

### 395. replay_without_freshness

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:575 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem replay_without_freshness : let bad
~~~

### 396. relay_without_binding

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:587 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem relay_without_binding : (run A0 2 { full with bind
~~~

### 397. debug_allowlisted

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:596 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem debug_allowlisted : (run A0 2 full (init [1, 7]) debugTrace).decs = [(0, 7, 0)] ∧ (run A0 2 full (init [1]) debugTrace).decs = []
~~~

### 398. toctou_without_integrity

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:605 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem toctou_without_integrity : (run A0 2 { full with integrity
~~~

### 399. revocation_example

Source: ControlStack/Families/F4/AttestedKeyRelease.lean:612 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem revocation_example : (run A0 2 full (init [1]) [.spawn 1, .revoke 0 1, .issue, .quote 0 0, .request 0 ⟨1, 0, 0⟩, .allowAdd 0 1, .issue, .quote 0 1, .request 0 ⟨1, 1, 0⟩, .decrypt 0]).rels = [] ∧ (run A0 2 full (init [1]) [.spawn 1, .issue, .quote 0 0, .request 0 ⟨1, 0, 0⟩, .decrypt 0]).decs = [(0, 1, 0)]
~~~

## ControlStack/Families/F4/AttestedLiveness.lean

### 400. run_append

Source: ControlStack/Families/F4/AttestedLiveness.lean:38 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_append (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (a b : List Op) : run A W C s (a ++ b) = run A W C (run A W C s a) b
~~~

### 401. run_cons

Source: ControlStack/Families/F4/AttestedLiveness.lean:42 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (o : Op) (ops : List Op) : run A W C s (o :: ops) = run A W C (step A W C s o) ops
~~~

### 402. step_alive

Source: ControlStack/Families/F4/AttestedLiveness.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_alive (A : List ℕ) (W : ℕ) (s : St) (o : Op) (k c : ℕ) (h : Alive k c s) : Alive k c (step A W full s o)
~~~

### 403. run_alive

Source: ControlStack/Families/F4/AttestedLiveness.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_alive (A : List ℕ) (W : ℕ) (s : St) (ops : List Op) (k c : ℕ) (h : Alive k c s) : Alive k c (run A W full s ops)
~~~

### 404. alive_code

Source: ControlStack/Families/F4/AttestedLiveness.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem alive_code (W : ℕ) (s : St) (hs : Inv W s) (k c : ℕ) (h : Alive k c s) : codeOf s k = some c ∨ codeOf s k = none
~~~

### 405. step_grow

Source: ControlStack/Families/F4/AttestedLiveness.lean:95 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_grow (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (o : Op) : (∀ x ∈ s.reports, x ∈ (step A W C s o).reports) ∧ (∀ x ∈ s.issued, x ∈ (step A W C s o).issued) ∧ ∀ x ∈ s.rels, x ∈ (step A W C s o).rels
~~~

### 406. run_grow

Source: ControlStack/Families/F4/AttestedLiveness.lean:101 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_grow (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (ops : List Op) : (∀ x ∈ s.reports, x ∈ (run A W C s ops).reports) ∧ (∀ x ∈ s.issued, x ∈ (run A W C s ops).issued) ∧ ∀ x ∈ s.rels, x ∈ (run A W C s ops).rels
~~~

### 407. step_uinv

Source: ControlStack/Families/F4/AttestedLiveness.lean:114 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_uinv (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (o : Op) (h : UInv s) : UInv (step A W C s o)
~~~

### 408. run_uinv

Source: ControlStack/Families/F4/AttestedLiveness.lean:126 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_uinv (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (ops : List Op) (h : UInv s) : UInv (run A W C s ops)
~~~

### 409. uinv_init

Source: ControlStack/Families/F4/AttestedLiveness.lean:131 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem uinv_init (a0 : List ℕ) : UInv (init a0)
~~~

### 410. progress_interleaved

Source: ControlStack/Families/F4/AttestedLiveness.lean:143 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem progress_interleaved (A : List ℕ) (W : ℕ) (s0 : St) (hs : Inv W s0) (hu : UInv s0) (k c : ℕ) (hk : (k, c) ∈ s0.sessions) (m1 m2 m3 : List Op) : let n
~~~

### 411. expiry_blocks

Source: ControlStack/Families/F4/AttestedLiveness.lean:202 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem expiry_blocks : (run A0 2 full (init [1]) expiryTrace).decs = []
~~~

### 412. expiry_ok

Source: ControlStack/Families/F4/AttestedLiveness.lean:204 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem expiry_ok : (run A0 3 full (init [1]) expiryTrace).decs = [(0, 1, 3)]
~~~

### 413. revocation_blocks

Source: ControlStack/Families/F4/AttestedLiveness.lean:207 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem revocation_blocks : (run A0 2 full (init [1]) [.spawn 1, .issue, .quote 0 0, .revoke 0 1, .request 0 ⟨1, 0, 0⟩, .decrypt 0]).decs = []
~~~

### 414. death_blocks

Source: ControlStack/Families/F4/AttestedLiveness.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem death_blocks : let s
~~~

### 415. nonce_theft_blocks

Source: ControlStack/Families/F4/AttestedLiveness.lean:218 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nonce_theft_blocks : let s
~~~

### 416. run_ticks

Source: ControlStack/Families/F4/AttestedLiveness.lean:227 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_ticks (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (D : ℕ) : (run A W C s (tickN D)).now = s.now + D ∧ (run A W C s (tickN D)).issued = s.issued ∧ (run A W C s (tickN D)).rels = s.rels ∧ (run A W C s (tickN D)).decs = s.decs ∧ (run A W C s (tickN D)).sessions = s.sessions
~~~

### 417. round_starves

Source: ControlStack/Families/F4/AttestedLiveness.lean:243 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem round_starves (A : List ℕ) (W : ℕ) (s : St) (hs : Inv W s) (k c D : ℕ) (hD : W < D) (hno : ∀ e ∈ s.rels, e.1 ≠ k) : (run A W full s (honestRound k c D s)).rels = s.rels ∧ (run A W full s (honestRound k c D s)).decs = s.decs ∧ Inv W (run A W full s (honestRound k c D s))
~~~

### 418. tick_starvation

Source: ControlStack/Families/F4/AttestedLiveness.lean:288 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tick_starvation (A : List ℕ) (W : ℕ) (k c D : ℕ) (hD : W < D) (m : ℕ) (s : St) (hs : Inv W s) (hno : ∀ e ∈ s.rels, e.1 ≠ k) : (starveRuns A W k c D m s).rels = s.rels ∧ (starveRuns A W k c D m s).decs = s.decs
~~~

### 419. starvation_example

Source: ControlStack/Families/F4/AttestedLiveness.lean:299 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem starvation_example (m : ℕ) : (starveRuns A0 2 0 1 3 m (run A0 2 full (init [1]) [.spawn 1])).decs = []
~~~

## ControlStack/Families/F4/GateClients.lean

### 420. dispatch_effects_prefix

Source: ControlStack/Families/F4/GateClients.lean:44 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dispatch_effects_prefix (s : AuditDispatch.St) (o : AuditDispatch.Op) : s.effects <+: (AuditDispatch.step s o).effects
~~~

### 421. dispatch_no_agent_effects

Source: ControlStack/Families/F4/GateClients.lean:55 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dispatch_no_agent_effects : NoAgentEffects dispatchSys (fun o => ∀ id, o ≠ .dispatch id)
~~~

### 422. auditGate_prefix

Source: ControlStack/Families/F4/GateClients.lean:65 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem auditGate_prefix (s : AuditGate.St) (o : AuditGate.Op) : s.executions <+: (AuditGate.step s o).executions
~~~

### 423. egress_prefix

Source: ControlStack/Families/F4/GateClients.lean:82 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem egress_prefix (p : EgressGate.Policy) (s : EgressGate.State) (a : EgressGate.Action) : s.attempts <+: (EgressGate.step p s a).attempts
~~~

### 424. step_inv

Source: ControlStack/Families/F4/GateClients.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (hash : C → H) (s : St C H) (o : Op C H) (h : Inv hash s) : Inv hash (step hash s o)
~~~

### 425. prefix_step

Source: ControlStack/Families/F4/GateClients.lean:169 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prefix_step (hash : C → H) (s : St C H) (o : Op C H) : s.deployed <+: (step hash s o).deployed
~~~

### 426. deployed_reviewed

Source: ControlStack/Families/F4/GateClients.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployed_reviewed (hash : C → H) (ops : List (Op C H)) : ∀ c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).deployed, hash c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).reviewed
~~~

### 427. deployed_is_reviewed

Source: ControlStack/Families/F4/GateClients.lean:195 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem deployed_is_reviewed (hash : C → H) (ops : List (Op C H)) (hinj : Set.InjOn hash {c | c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).store ∨ c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).reviewedContent}) : ∀ c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).deployed, c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).reviewedContent
~~~

### 428. collision_breaks

Source: ControlStack/Families/F4/GateClients.lean:210 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem collision_breaks : let s
~~~

### 429. agent_cannot_review

Source: ControlStack/Families/F4/GateClients.lean:222 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_cannot_review (hash : C → H) (s : St C H) (o : Op C H) (ho : agentOp o) : (step hash s o).reviewed = s.reviewed ∧ (step hash s o).reviewedContent = s.reviewedContent
~~~

### 430. step_inv

Source: ControlStack/Families/F4/GateClients.lean:273 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (s : St P) (o : Op P) (h : Inv s) : Inv (step s o)
~~~

### 431. prefix_step

Source: ControlStack/Families/F4/GateClients.lean:292 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prefix_step (s : St P) (o : Op P) : s.executed <+: (step s o).executed
~~~

### 432. approval_safe

Source: ControlStack/Families/F4/GateClients.lean:307 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem approval_safe (ops : List (Op P)) : let s
~~~

### 433. replay_without_nonce

Source: ControlStack/Families/F4/GateClients.lean:322 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem replay_without_nonce : let t : Tx Unit
~~~

### 434. agent_cannot_approve

Source: ControlStack/Families/F4/GateClients.lean:334 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_cannot_approve (s : St P) (o : Op P) (ho : agentOp o) : (step s o).approvals = s.approvals
~~~

### 435. replay_if_nonces_lost

Source: ControlStack/Families/F4/GateClients.lean:341 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem replay_if_nonces_lost : let t : Tx Unit
~~~

## ControlStack/Families/F5/EscrowBudget.lean

### 436. upd_n

Source: ControlStack/Families/F5/EscrowBudget.lean:106 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem upd_n (s : ESt) (i : ℕ) (v : GS) : (upd s i v).n = s.n
~~~

### 437. upd_now

Source: ControlStack/Families/F5/EscrowBudget.lean:107 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem upd_now (s : ESt) (i : ℕ) (v : GS) : (upd s i v).now = s.now
~~~

### 438. upd_cut

Source: ControlStack/Families/F5/EscrowBudget.lean:108 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem upd_cut (s : ESt) (i : ℕ) (v : GS) : (upd s i v).cut = s.cut
~~~

### 439. upd_self

Source: ControlStack/Families/F5/EscrowBudget.lean:109 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem upd_self (s : ESt) (i : ℕ) (v : GS) : (upd s i v).g i = v
~~~

### 440. upd_ne

Source: ControlStack/Families/F5/EscrowBudget.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem upd_ne (s : ESt) (i j : ℕ) (v : GS) (h : j ≠ i) : (upd s i v).g j = s.g j
~~~

### 441. inv_init

Source: ControlStack/Families/F5/EscrowBudget.lean:149 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (C : Cfg) : Inv C init
~~~

### 442. total_le_acc

Source: ControlStack/Families/F5/EscrowBudget.lean:151 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem total_le_acc (C : Cfg) (s : ESt) (h : Inv C s) : total s ≤ acc s
~~~

### 443. acc_upd

Source: ControlStack/Families/F5/EscrowBudget.lean:160 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem acc_upd (s : ESt) (i : ℕ) (v : GS) (hi : i < s.n) : acc (upd s i v) + (if (s.g i).settled then (s.g i).final else (s.g i).amt) = acc s + (if v.settled then v.final else v.amt)
~~~

### 444. acc_upd_le

Source: ControlStack/Families/F5/EscrowBudget.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem acc_upd_le (s : ESt) (i : ℕ) (v : GS) (hi : i < s.n) (hle : (if v.settled then v.final else v.amt) ≤ (if (s.g i).settled then (s.g i).final else (s.g i).amt)) : acc (upd s i v) ≤ acc s
~~~

### 445. step_inv

Source: ControlStack/Families/F5/EscrowBudget.lean:179 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (C : Cfg) (hC : C.aware = true) (s : ESt) (o : EOp) (ho : legal C s o) (h : Inv C s) : Inv C (step C s o)
~~~

### 446. legalTrace_of_B

Source: ControlStack/Families/F5/EscrowBudget.lean:298 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem legalTrace_of_B (C : Cfg) : ∀ (ops : List EOp) (s : ESt), legalTraceB C s ops = true → LegalTrace C s ops
~~~

### 447. run_inv

Source: ControlStack/Families/F5/EscrowBudget.lean:309 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (C : Cfg) (hC : C.aware = true) (s : ESt) (ops : List EOp) (hl : LegalTrace C s ops) (h : Inv C s) : Inv C (run C s ops)
~~~

### 448. escrow_safe

Source: ControlStack/Families/F5/EscrowBudget.lean:317 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem escrow_safe (C : Cfg) (hC : C.aware = true) (ops : List EOp) (hl : LegalTrace C init ops) : total (run C init ops) ≤ C.G
~~~

### 449. reclaim_frees

Source: ControlStack/Families/F5/EscrowBudget.lean:326 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reclaim_frees (C : Cfg) (hC : C.aware = true) (hE : C.expiry = true) (s : ESt) (h : Inv C s) (i c : ℕ) (hi : i < s.n) (hns : (s.g i).settled = false) (hlate : (s.g i).exp + 2 * C.σ ≤ s.now) (hc : s.now ≤ c + C.σ) (hreach : (s.g i).host ∉ s.cut) : ((step C s (.reclaim i c)).g i).settled = true ∧ ((step C s (.reclaim i c)).g i).final = (s.g i).spent ∧ acc (step C s (.reclaim i c)) + ((s.g i).amt - (s.g i).spent) = acc s
~~~

### 450. reconcile_frees

Source: ControlStack/Families/F5/EscrowBudget.lean:347 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reconcile_frees (C : Cfg) (s : ESt) (h : Inv C s) (i : ℕ) (hi : i < s.n) (hs : (s.g i).settled = true) (hreach : (s.g i).host ∉ s.cut) : acc (step C s (.reconcile i)) + ((s.g i).final - (s.g i).spent) = acc s
~~~

### 451. skewTrace_legal

Source: ControlStack/Families/F5/EscrowBudget.lean:371 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem skewTrace_legal (aware : Bool) : LegalTrace (C10 aware true) init skewTrace
~~~

### 452. skew_unaware_overspends

Source: ControlStack/Families/F5/EscrowBudget.lean:376 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem skew_unaware_overspends : total (run (C10 false true) init skewTrace) = 20 ∧ total (run (C10 true true) init skewTrace) ≤ 10
~~~

### 453. no_expiry_starves

Source: ControlStack/Families/F5/EscrowBudget.lean:387 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_expiry_starves : (run (C10 true false) init starveTrace).n = 1 ∧ (run (C10 true true) init starveTrace).n = 2
~~~

### 454. datacenter_example

Source: ControlStack/Families/F5/EscrowBudget.lean:397 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem datacenter_example (ops : List EOp) (hl : LegalTrace ⟨1000000, 2, true, true⟩ init ops) : total (run ⟨1000000, 2, true, true⟩ init ops) ≤ 1000000 ∧ 1000 * 1000 ≤ (1000000 : ℕ) ∧ 60 + 2 * 2 = 64
~~~

## ControlStack/Families/F5/EscrowBudgetMsg.lean

### 455. upd_n

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:129 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem upd_n (s : MSt) (i : ℕ) (v : GS) : (upd s i v).n = s.n
~~~

### 456. upd_now

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:130 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem upd_now (s : MSt) (i : ℕ) (v : GS) : (upd s i v).now = s.now
~~~

### 457. upd_net

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:131 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem upd_net (s : MSt) (i : ℕ) (v : GS) : (upd s i v).net = s.net
~~~

### 458. upd_cclk

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:132 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem upd_cclk (s : MSt) (i : ℕ) (v : GS) : (upd s i v).cclk = s.cclk
~~~

### 459. upd_hclk

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:133 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem upd_hclk (s : MSt) (i : ℕ) (v : GS) : (upd s i v).hclk = s.hclk
~~~

### 460. upd_self

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:134 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem upd_self (s : MSt) (i : ℕ) (v : GS) : (upd s i v).g i = v
~~~

### 461. upd_ne

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:135 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem upd_ne (s : MSt) (i j : ℕ) (v : GS) (h : j ≠ i) : (upd s i v).g j = s.g j
~~~

### 462. addSpent_amt

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:143 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem addSpent_amt (v : GS) (x : ℕ) : (addSpent v x).amt = v.amt
~~~

### 463. addSpent_exp

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:144 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem addSpent_exp (v : GS) (x : ℕ) : (addSpent v x).exp = v.exp
~~~

### 464. addSpent_spent

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:145 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem addSpent_spent (v : GS) (x : ℕ) : (addSpent v x).spent = v.spent + x
~~~

### 465. addSpent_settled

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem addSpent_settled (v : GS) (x : ℕ) : (addSpent v x).settled = v.settled
~~~

### 466. addSpent_final

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:147 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem addSpent_final (v : GS) (x : ℕ) : (addSpent v x).final = v.final
~~~

### 467. settleAt_amt

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:148 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem settleAt_amt (v : GS) (f : ℕ) : (settleAt v f).amt = v.amt
~~~

### 468. settleAt_exp

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:149 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem settleAt_exp (v : GS) (f : ℕ) : (settleAt v f).exp = v.exp
~~~

### 469. settleAt_spent

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem settleAt_spent (v : GS) (f : ℕ) : (settleAt v f).spent = v.spent
~~~

### 470. settleAt_settled

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:151 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem settleAt_settled (v : GS) (f : ℕ) : (settleAt v f).settled = true
~~~

### 471. settleAt_final

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:152 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem settleAt_final (v : GS) (f : ℕ) : (settleAt v f).final = f
~~~

### 472. settleOf_mem

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:160 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem settleOf_mem {s : MSt} {k i sp : ℕ} (h : settleOf s k = some (i, sp)) : Msg.settle i sp ∈ s.net
~~~

### 473. run_cons

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:202 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (C : Cfg) (s : MSt) (o : MOp) (ops : List MOp) : run C s (o :: ops) = run C (step C s o) ops
~~~

### 474. run_append

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:204 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_append (C : Cfg) (s : MSt) (a b : List MOp) : run C s (a ++ b) = run C (run C s a) b
~~~

### 475. legalTrace_of_B

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:228 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem legalTrace_of_B (C : Cfg) : ∀ (ops : List MOp) (s : MSt), legalTraceB C s ops = true → LegalTrace C s ops
~~~

### 476. legalTrace_append

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:240 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem legalTrace_append (C : Cfg) (s : MSt) (a b : List MOp) : LegalTrace C s (a ++ b) ↔ LegalTrace C s a ∧ LegalTrace C (run C s a) b
~~~

### 477. inv_init

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:265 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (C : Cfg) : Inv C init
~~~

### 478. total_le_acc

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:268 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem total_le_acc (C : Cfg) (s : MSt) (h : Inv C s) : total s ≤ acc s
~~~

### 479. acc_upd

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:276 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem acc_upd (s : MSt) (i : ℕ) (v : GS) (hi : i < s.n) : acc (upd s i v) + (if (s.g i).settled then (s.g i).final else (s.g i).amt) = acc s + (if v.settled then v.final else v.amt)
~~~

### 480. acc_upd_le

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:290 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem acc_upd_le (s : MSt) (i : ℕ) (v : GS) (hi : i < s.n) (hle : (if v.settled then v.final else v.amt) ≤ (if (s.g i).settled then (s.g i).final else (s.g i).amt)) : acc (upd s i v) ≤ acc s
~~~

### 481. msgs_upd

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:297 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem msgs_upd (s : MSt) (i : ℕ) (v : GS) (hm : ∀ m ∈ s.net, MsgOk s m) (hsp : v.spent = (s.g i).spent) (hex : v.exp = (s.g i).exp) : ∀ m ∈ (upd s i v).net, MsgOk (upd s i v) m
~~~

### 482. settled_ok_upd

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:316 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem settled_ok_upd (s : MSt) (i : ℕ) (v : GS) (h : ∀ j < s.n, (s.g j).settled = true → (s.g j).spent ≤ (s.g j).final ∧ (s.g j).final ≤ (s.g j).amt ∧ (s.g j).exp ≤ s.now) (hv : v.settled = true → v.spent ≤ v.final ∧ v.final ≤ v.amt ∧ v.exp ≤ s.now) : ∀ j < (upd s i v).n, ((upd s i v).g j).settled = true → ((upd s i v).g j).spent ≤ ((upd s i v).g j).final ∧ ((upd s i v).g j).final ≤ ((upd s i v).g j).amt ∧ ((upd s i v).g j).exp ≤ (upd s i v).now
~~~

### 483. within_upd

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:328 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem within_upd (s : MSt) (i : ℕ) (v : GS) (h : ∀ j < s.n, (s.g j).spent ≤ (s.g j).amt) (hv : v.spent ≤ v.amt) : ∀ j < (upd s i v).n, ((upd s i v).g j).spent ≤ ((upd s i v).g j).amt
~~~

### 484. step_inv

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:336 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (C : Cfg) (hC : C.aware = true) (s : MSt) (o : MOp) (ho : legal C s o) (h : Inv C s) : Inv C (step C s o)
~~~

### 485. run_inv

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:483 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (C : Cfg) (hC : C.aware = true) (s : MSt) (ops : List MOp) (hl : LegalTrace C s ops) (h : Inv C s) : Inv C (run C s ops)
~~~

### 486. escrow_safe

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:492 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem escrow_safe (C : Cfg) (hC : C.aware = true) (ops : List MOp) (hl : LegalTrace C init ops) : total (run C init ops) ≤ C.G
~~~

### 487. deliver_returns

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:501 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deliver_returns (C : Cfg) (s : MSt) (h : Inv C s) (k i sp : ℕ) (hk : settleOf s k = some (i, sp)) : ((step C s (.deliver k)).g i).settled = true ∧ ((step C s (.deliver k)).g i).final = ((step C s (.deliver k)).g i).spent ∧ acc (step C s (.deliver k)) + ((if (s.g i).settled then (s.g i).final else (s.g i).amt) - (s.g i).spent) = acc s
~~~

### 488. settled_stable

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:522 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem settled_stable (C : Cfg) (hC : C.aware = true) (s : MSt) (h : Inv C s) (i : ℕ) (hi : i < s.n) (hs : (s.g i).settled = true) (hf : (s.g i).final = (s.g i).spent) (o : MOp) (ho : legal C s o) : ((step C s o).g i).settled = true ∧ ((step C s o).g i).final = ((step C s o).g i).spent
~~~

### 489. n_mono

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:570 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem n_mono (C : Cfg) (s : MSt) (o : MOp) : s.n ≤ (step C s o).n
~~~

### 490. settled_stable_run

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:589 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem settled_stable_run (C : Cfg) (hC : C.aware = true) (s : MSt) (ops : List MOp) (hl : LegalTrace C s ops) (h : Inv C s) (i : ℕ) (hi : i < s.n) (hs : (s.g i).settled = true) (hf : (s.g i).final = (s.g i).spent) : ((run C s ops).g i).settled = true ∧ ((run C s ops).g i).final = ((run C s ops).g i).spent
~~~

### 491. escrow_returns

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:601 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem escrow_returns (C : Cfg) (hC : C.aware = true) (pre post : List MOp) (k i sp : ℕ) (hl : LegalTrace C init (pre ++ .deliver k :: post)) (hdel : settleOf (run C init pre) k = some (i, sp)) : ((run C init (pre ++ .deliver k :: post)).g i).settled = true ∧ ((run C init (pre ++ .deliver k :: post)).g i).final = ((run C init (pre ++ .deliver k :: post)).g i).spent
~~~

### 492. settle_enabled

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:616 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem settle_enabled (C : Cfg) (hC : C.aware = true) (s : MSt) (i : ℕ) (hi : i < s.n) (hup : s.up (s.g i).host = true) (hexp : (s.g i).exp + C.σ ≤ s.cclk) : LegalTrace C s [.poll i, .reply i, .deliver (s.net.length + 1)] ∧ ((run C s [.poll i, .reply i, .deliver (s.net.length + 1)]).g i).settled = true ∧ ((run C s [.poll i, .reply i, .deliver (s.net.length + 1)]).g i).final = (s.g i).spent
~~~

### 493. skewTrace_legal

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:650 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem skewTrace_legal (aware : Bool) : LegalTrace (C10 aware) init skewTrace
~~~

### 494. skew_unaware_overspends

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:656 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem skew_unaware_overspends : total (run (C10 false) init skewTrace) = 20 ∧ total (run (C10 true) init skewTrace) ≤ 10
~~~

### 495. crash_holds_escrow

Source: ControlStack/Families/F5/EscrowBudgetMsg.lean:671 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem crash_holds_escrow : (run (C10 true) init crashPre).net.length = 1 ∧ (run (C10 true) init crashPre).n = 1 ∧ (run (C10 true) init (crashPre ++ crashPost)).n = 2 ∧ LegalTrace (C10 true) init (crashPre ++ crashPost)
~~~

## ControlStack/Families/F5/Lease.lean

### 496. spent_append

Source: ControlStack/Families/F5/Lease.lean:107 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem spent_append (work : List (ℕ × ℕ × ℕ)) (e : ℕ × ℕ × ℕ) (id : ℕ) : spent (work ++ [e]) id = spent work id + (if e.1 = id then e.2.1 else 0)
~~~

### 497. total_append

Source: ControlStack/Families/F5/Lease.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem total_append (work : List (ℕ × ℕ × ℕ)) (e : ℕ × ℕ × ℕ) : total (work ++ [e]) = total work + e.2.1
~~~

### 498. spent_eq_zero_of_absent

Source: ControlStack/Families/F5/Lease.lean:114 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem spent_eq_zero_of_absent (work : List (ℕ × ℕ × ℕ)) (id : ℕ) (h : ∀ e ∈ work, e.1 ≠ id) : spent work id = 0
~~~

### 499. step_inv

Source: ControlStack/Families/F5/Lease.lean:120 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (cap : ℕ) (s : St) (o : Op) (h : Inv cap s) : Inv cap (step cap s o)
~~~

### 500. prefix_step

Source: ControlStack/Families/F5/Lease.lean:180 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prefix_step (cap : ℕ) (s : St) (o : Op) : s.work <+: (step cap s o).work
~~~

### 501. lease_safe

Source: ControlStack/Families/F5/Lease.lean:204 | Family: F5 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem lease_safe (cap : ℕ) (ops : List Op) : let s
~~~

### 502. revoke_step

Source: ControlStack/Families/F5/Lease.lean:213 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem revoke_step (cap : ℕ) (s : St) (o : Op) (id : ℕ) (hr : id ∈ s.revoked) : id ∈ (step cap s o).revoked ∧ ∃ δ, (step cap s o).work = s.work ++ δ ∧ ∀ e ∈ δ, e.1 ≠ id
~~~

### 503. revoke_absorbing

Source: ControlStack/Families/F5/Lease.lean:238 | Family: F5 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem revoke_absorbing (cap : ℕ) (s : St) (ops : List Op) (id : ℕ) (hr : id ∈ s.revoked) : ∃ δ, ((sys cap).run s ops).work = s.work ++ δ ∧ ∀ e ∈ δ, e.1 ≠ id
~~~

### 504. length_le_sum

Source: ControlStack/Families/F5/Lease.lean:252 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem length_le_sum (L : List (ℕ × ℕ × ℕ)) (h : ∀ e ∈ L, 1 ≤ e.2.1) : L.length ≤ (L.map (fun e => e.2.1)).sum
~~~

### 505. work_count_le

Source: ControlStack/Families/F5/Lease.lean:264 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem work_count_le (cap : ℕ) (ops : List Op) : let s
~~~

### 506. agent_cannot_issue

Source: ControlStack/Families/F5/Lease.lean:282 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_cannot_issue (cap : ℕ) (s : St) (o : Op) (ho : agentOp o) : (step cap s o).leases = s.leases ∧ (step cap s o).revoked = s.revoked
~~~

### 507. revoked_worker_stays_stopped

Source: ControlStack/Families/F5/Lease.lean:298 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem revoked_worker_stays_stopped : let ops
~~~

### 508. zero_cost_refused

Source: ControlStack/Families/F5/Lease.lean:304 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem zero_cost_refused : ([Op.issue ⟨0, 0, 100⟩ 1, .work 1 0, .work 1 0].foldl (step 100) init).work = []
~~~

### 509. fork_without_lease_accounting

Source: ControlStack/Families/F5/Lease.lean:328 | Family: F5 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem fork_without_lease_accounting : let ops
~~~

### 510. reissue_takes_effect

Source: ControlStack/Families/F5/Lease.lean:335 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reissue_takes_effect : let ops
~~~

## ControlStack/Families/F6/DamageBound.lean

### 511. val_le_const

Source: ControlStack/Families/F6/DamageBound.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_le_const (K : List (Y × O) → Y × O → ℝ) (pay : List O → ℝ) (M : ℝ) (hK0 : ∀ h z, 0 ≤ K h z) (hK1 : ∀ h, ∑ z, K h z ≤ 1) (hM : 0 ≤ M) (hpay : ∀ t, pay t ≤ M) : ∀ n h, val K pay n h ≤ M
~~~

### 512. val_mono_on

Source: ControlStack/Families/F6/DamageBound.lean:84 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_mono_on (K : List (Y × O) → Y × O → ℝ) (P : List O → Prop) (pay pay' : List O → ℝ) (hK0 : ∀ h z, 0 ≤ K h z) (hP : ∀ h y o, K h (y, o) ≠ 0 → P (h.map Prod.snd) → P (h.map Prod.snd ++ [o])) (hle : ∀ t, P t → pay t ≤ pay' t) : ∀ n h, P (h.map Prod.snd) → val K pay n h ≤ val K pay' n h
~~~

### 513. val_smul

Source: ControlStack/Families/F6/DamageBound.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_smul (K : List (Y × O) → Y × O → ℝ) (c : ℝ) (pay : List O → ℝ) : ∀ n h, val K (fun t => c * pay t) n h = c * val K pay n h
~~~

### 514. val_add

Source: ControlStack/Families/F6/DamageBound.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_add (K : List (Y × O) → Y × O → ℝ) (p q : List O → ℝ) : ∀ n h, val K (fun t => p t + q t) n h = val K p n h + val K q n h
~~~

### 515. val_finsum

Source: ControlStack/Families/F6/DamageBound.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_finsum {ι : Type} (s : Finset ι) (K : List (Y × O) → Y × O → ℝ) (f : ι → List O → ℝ) : ∀ n h, val K (fun t => ∑ j ∈ s, f j t) n h = ∑ j ∈ s, val K (f j) n h
~~~

### 516. val_det

Source: ControlStack/Families/F6/DamageBound.lean:131 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_det [DecidableEq Y] [DecidableEq O] (z0 : Y × O) (pay : List O → ℝ) : ∀ n h, val (fun _ z => if z = z0 then (1 : ℝ) else 0) pay n h = pay (h.map Prod.snd ++ List.replicate n z0.2)
~~~

### 517. pre_all

Source: ControlStack/Families/F6/DamageBound.lean:161 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pre_all (g : List (AOut Unit)) (hg : (g.all fun o => !caughtFlag o) = true) : pre g = g
~~~

### 518. pre_snoc

Source: ControlStack/Families/F6/DamageBound.lean:170 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pre_snoc (g : List (AOut Unit)) (o : AOut Unit) : pre (g ++ [o]) = if (g.all fun o => !caughtFlag o) = true then (if caughtFlag o = true then g else g ++ [o]) else pre g
~~~

### 519. attacked_snoc

Source: ControlStack/Families/F6/DamageBound.lean:186 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attacked_snoc (g : List (AOut Unit)) (o : AOut Unit) (i : ℕ) (h : attacked g i = true) : attacked (g ++ [o]) i = true
~~~

### 520. attackSet_snoc

Source: ControlStack/Families/F6/DamageBound.lean:196 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attackSet_snoc {N : ℕ} (g : List (AOut Unit)) (o : AOut Unit) : attackSet (N
~~~

### 521. ucX_mono

Source: ControlStack/Families/F6/DamageBound.lean:202 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ucX_mono (N : ℕ) (g : List (AOut Unit)) (o : AOut Unit) : ucX N g ≤ ucX N (g ++ [o])
~~~

### 522. ucX_stuck

Source: ControlStack/Families/F6/DamageBound.lean:210 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ucX_stuck (N : ℕ) (g : List (AOut Unit)) (o : AOut Unit) (h : (g.all fun o => !caughtFlag o) = false ∨ caughtFlag o = true) : ucX N (g ++ [o]) = ucX N g
~~~

### 523. ucX_le

Source: ControlStack/Families/F6/DamageBound.lean:220 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ucX_le (N : ℕ) (t : List (AOut Unit)) : ucX N t ≤ N
~~~

### 524. ucX_tail

Source: ControlStack/Families/F6/DamageBound.lean:225 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ucX_tail (N : ℕ) (t : List (AOut Unit)) : (ucX N t : ℝ) = ∑ j ∈ range N, (if j + 1 ≤ ucX N t then (1 : ℝ) else 0)
~~~

### 525. sum_point

Source: ControlStack/Families/F6/DamageBound.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_point (z0 : Y × AOut Unit) (F : Y × AOut Unit → ℝ) : ∑ y, ∑ o, (if (y, o) = z0 then (1 : ℝ) else 0) * F (y, o) = F z0
~~~

### 526. val_frozen

Source: ControlStack/Families/F6/DamageBound.lean:257 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_frozen (j : ℕ) (y0 : Y) (Kx : List (Y × AOut Unit) → Y × AOut Unit → ℝ) : ∀ n h, j ≤ ucX N (h.map Prod.snd) → val (freezeK N j y0 Kx) (pX N j) n h = 1
~~~

### 527. freeze_le

Source: ControlStack/Families/F6/DamageBound.lean:273 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem freeze_le (j : ℕ) (y0 : Y) (Kx : List (Y × AOut Unit) → Y × AOut Unit → ℝ) (hK0 : ∀ h z, 0 ≤ Kx h z) (hK1 : ∀ h, ∑ z, Kx h z ≤ 1) : ∀ n h, val Kx (pX N j) n h ≤ val (freezeK N j y0 Kx) (pX N j) n h
~~~

### 528. pX_le_succ

Source: ControlStack/Families/F6/DamageBound.lean:291 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pX_le_succ (j : ℕ) (y0 : Y) (Kx : List (Y × AOut Unit) → Y × AOut Unit → ℝ) (hK0 : ∀ h z, 0 ≤ Kx h z) (n : ℕ) : val (freezeK N j y0 Kx) (pX N j) n [] ≤ val (freezeK N j y0 Kx) (recallSucc (N
~~~

### 529. tail_bound

Source: ControlStack/Families/F6/DamageBound.lean:328 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tail_bound (y0 : Y) (j Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) (pX N j) N [] ≤ hypMiss N Bh j r
~~~

### 530. expected_uc

Source: ControlStack/Families/F6/DamageBound.lean:373 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem expected_uc (y0 : Y) (Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) (fun t => (ucX N t : ℝ)) N [] ≤ ∑ j ∈ range N, hypMiss N Bh (j + 1) r
~~~

### 531. damage_bound

Source: ControlStack/Families/F6/DamageBound.lean:394 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem damage_bound (y0 : Y) (Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) (D : ℝ) (hD : 0 ≤ D) (dmg : List (AOut Unit) → ℝ) (hdD : ∀ t, dmg t ≤ D * ucX N t) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) dmg N [] ≤ D * ∑ j ∈ range N, hypMiss N Bh (j + 1) r
~~~

### 532. damage_cap_inflight

Source: ControlStack/Families/F6/DamageBound.lean:423 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem damage_cap_inflight (y0 : Y) (Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) (D F G : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (hG : 0 ≤ G) (dmg : List (AOut Unit) → ℝ) (hdD : ∀ t, dmg t ≤ D * ucX N t + F) (hdG : ∀ t, dmg t ≤ G) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) dmg N [] ≤ min G (D * ∑ j ∈ range N, hypMiss N Bh (j + 1) r + F)
~~~

### 533. hypMiss_one

Source: ControlStack/Families/F6/DamageBound.lean:473 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hypMiss_one (B k : ℕ) : hypMiss N B k 1 = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

### 534. sum_range_choose_succ

Source: ControlStack/Families/F6/DamageBound.lean:481 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_range_choose_succ (B : ℕ) : ∀ n, ∑ m ∈ range n, Nat.choose m B = Nat.choose n (B + 1)
~~~

### 535. expected_r1

Source: ControlStack/Families/F6/DamageBound.lean:487 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem expected_r1 (B : ℕ) (hB : B ≤ N) : ∑ j ∈ range N, hypMiss N B (j + 1) 1 = ((N : ℝ) - B) / (B + 1)
~~~

### 536. sum_pU_eq

Source: ControlStack/Families/F6/DamageBound.lean:507 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_pU_eq (B : ℕ) (X : Finset (Fin N) → ℝ) : ∑ S : Finset (Fin N), pU N B S * X S = (Nat.choose N B : ℝ)⁻¹ * ∑ S ∈ AuditBudget.randomSchedules N B, X S
~~~

### 537. count_mem

Source: ControlStack/Families/F6/DamageBound.lean:515 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem count_mem (B : ℕ) (hB1 : 1 ≤ B) (a : Fin N) : ((AuditBudget.randomSchedules N B).filter (fun S => a ∈ S)).card = Nat.choose (N - 1) (B - 1)
~~~

### 538. hyp_step

Source: ControlStack/Families/F6/DamageBound.lean:529 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hyp_step (B k : ℕ) (hB : B ≤ N) (hk : k < N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : hypMiss N B (k + 1) r ≤ (1 - r * B / N) * hypMiss N B k r
~~~

### 539. hypMiss_zero

Source: ControlStack/Families/F6/DamageBound.lean:645 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hypMiss_zero (B : ℕ) (hB : B ≤ N) (r : ℝ) : hypMiss N B 0 r = 1
~~~

### 540. hyp_geom

Source: ControlStack/Families/F6/DamageBound.lean:651 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hyp_geom (B : ℕ) (hB : B ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : ∀ k, k ≤ N → hypMiss N B k r ≤ (1 - r * B / N) ^ k
~~~

### 541. expected_geom

Source: ControlStack/Families/F6/DamageBound.lean:672 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem expected_geom (B : ℕ) (hB : B ≤ N) (hB0 : 0 < B) (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) : ∑ j ∈ range N, hypMiss N B (j + 1) r ≤ ((N : ℝ) - r * B) / (r * B)
~~~

### 542. no_halt_damage

Source: ControlStack/Families/F6/DamageBound.lean:708 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_damage (N : ℕ) (D : ℝ) : val (fun (_ : List (Unit × AOut Unit)) z => if z = ((), ((true, (), true) : AOut Unit)) then (1 : ℝ) else 0) (fun t => D * (attackSet (N
~~~

### 543. no_cap_damage

Source: ControlStack/Families/F6/DamageBound.lean:732 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_cap_damage (M : ℝ) : val (fun (_ : List (Unit × AOut Unit)) z => if z = ((), ((true, (), false) : AOut Unit)) then (1 : ℝ) else 0) (fun t => M * ucX 1 t) 1 [] = M
~~~

### 544. example_r1

Source: ControlStack/Families/F6/DamageBound.lean:745 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem example_r1 : ∑ j ∈ range 100, hypMiss 100 10 (j + 1) 1 = 90 / 11
~~~

### 545. example_r_half

Source: ControlStack/Families/F6/DamageBound.lean:749 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem example_r_half : ∑ j ∈ range 100, hypMiss 100 10 (j + 1) (1 / 2) ≤ 19
~~~

## ControlStack/Families/F6/EnsembleKernel.lean

### 546. mixture_nonneg

Source: ControlStack/Families/F6/EnsembleKernel.lean:49 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mixture_nonneg (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (ν : (Fin m → Bool) → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1) (y : Hid m) : 0 ≤ mixture b ν q y
~~~

### 547. mixture_total

Source: ControlStack/Families/F6/EnsembleKernel.lean:56 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mixture_total (b : ℝ) (ν : (Fin m → Bool) → ℝ) (hν1 : ∑ x, ν x = 1) (q : Fin m → ℝ) : ∑ y : Hid m, mixture b ν q y = 1
~~~

### 548. ensK_premises

Source: ControlStack/Families/F6/EnsembleKernel.lean:76 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ensK_premises (β : ℝ) (r : Fin m → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (b : List (AOut Unit) → ℝ) (ν : List (AOut Unit) → (Fin m → Bool) → ℝ) (q : List (AOut Unit) → Fin m → ℝ) (hp : Params β r b ν q) (S : Finset (Fin N)) (h : List (Hid m × AOut Unit)) : (∀ z, 0 ≤ ensK σ b ν q S h z) ∧ (∑ z, ensK σ b ν q S h z ≤ 1) ∧ ∀ a : Bool, ∑ y, ensK σ b ν q S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then β + ∏ j, (1 - r j) else 1)
~~~

### 549. ensK_adaptive

Source: ControlStack/Families/F6/EnsembleKernel.lean:140 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ensK_adaptive (k Bh : ℕ) (hB : Bh ≤ N) (β : ℝ) (r : Fin m → ℝ) (hβ0 : 0 ≤ β) (hr : ∀ j, 0 ≤ r j ∧ r j ≤ 1) (he1 : β + ∏ j, (1 - r j) ≤ 1) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (b : List (AOut Unit) → ℝ) (ν : List (AOut Unit) → (Fin m → Bool) → ℝ) (q : List (AOut Unit) → Fin m → ℝ) (hp : Params β r b ν q) : ∑ S : Finset (Fin N), pU N Bh S * val (ensK σ b ν q S) (recallSucc (N
~~~

### 550. ensK_example

Source: ControlStack/Families/F6/EnsembleKernel.lean:156 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ensK_example (k Bh : ℕ) (hB : Bh ≤ N) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (b : List (AOut Unit) → ℝ) (ν : List (AOut Unit) → (Fin 3 → Bool) → ℝ) (q : List (AOut Unit) → Fin 3 → ℝ) (hp : Params (1 / 20) (fun _ => 3 / 5) b ν q) : ∑ S : Finset (Fin N), pU N Bh S * val (ensK σ b ν q S) (recallSucc (N
~~~

## ControlStack/Families/F6/MonitorCollusion.lean

### 551. pass_transfer

Source: ControlStack/Families/F6/MonitorCollusion.lean:65 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem pass_transfer (Ph Pr β : V → ℝ) (hh : IsDist Ph) (hr : IsDist Pr) (hβ : ∀ v, 0 ≤ β v ∧ β v ≤ 1) : |passRate Pr β - passRate Ph β| ≤ tv Ph Pr
~~~

### 552. pass_equal

Source: ControlStack/Families/F6/MonitorCollusion.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pass_equal (Ph Pr β : V → ℝ) (heq : Ph = Pr) : passRate Pr β = passRate Ph β
~~~

### 553. sum_max_eq

Source: ControlStack/Families/F6/MonitorCollusion.lean:90 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_max_eq (P Q : V → ℝ) (hP : IsDist P) (hQ : IsDist Q) : ∑ v, max (P v) (Q v) = 1 + tv P Q
~~~

### 554. collusion_ml

Source: ControlStack/Families/F6/MonitorCollusion.lean:105 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem collusion_ml (p : Bool → ℝ) (lik : Bool → V → ℝ) (δ : V → Bool → ℝ) (hp : ∀ φ, 0 ≤ p φ) (hlik : ∀ φ v, 0 ≤ lik φ v) (hδ : ∀ v, IsDist (δ v)) : ∑ φ, p φ * ∑ v, lik φ v * ∑ a, δ v a * (if a = φ then 1 else 0) ≤ (∑ v, max (lik true v) (lik false v)) * max (p true) (p false)
~~~

### 555. collusion_uniform

Source: ControlStack/Families/F6/MonitorCollusion.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem collusion_uniform (Ph Pr : V → ℝ) (hh : IsDist Ph) (hr : IsDist Pr) (δ : V → Bool → ℝ) (hδ : ∀ v, IsDist (δ v)) : ∑ φ, (1 / 2 : ℝ) * ∑ v, (if φ then Pr v else Ph v) * ∑ a, δ v a * (if a = φ then 1 else 0) ≤ (1 + tv Pr Ph) / 2
~~~

### 556. canon_channel

Source: ControlStack/Families/F6/MonitorCollusion.lean:140 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem canon_channel {M : Type} [Fintype M] [DecidableEq M] [Nonempty M] (K : ℕ) (κ : V → Fin K) (enc : M → V → ℝ) (henc : ∀ m, IsDist (enc m)) (dec : Fin K → M → ℝ) (hdec : ∀ k, IsDist (dec k)) : ∑ m, (Fintype.card M : ℝ)⁻¹ * ∑ v, enc m v * ∑ a, dec (κ v) a * (if a = m then 1 else 0) ≤ (K : ℝ) * (Fintype.card M : ℝ)⁻¹
~~~

### 557. stego_fools_honeypots

Source: ControlStack/Families/F6/MonitorCollusion.lean:179 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stego_fools_honeypots : passRate stegoReal stegoMonitor = 1 ∧ passRate stegoHoney stegoMonitor = 0 ∧ tv stegoHoney stegoReal = 1
~~~

### 558. canon_restores

Source: ControlStack/Families/F6/MonitorCollusion.lean:185 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem canon_restores (β : Fin 1 → ℝ) : passRate stegoReal (fun v => β ((fun _ => 0 : Bool → Fin 1) v)) = passRate stegoHoney (fun v => β ((fun _ => 0 : Bool → Fin 1) v))
~~~

### 559. phase_learning

Source: ControlStack/Families/F6/MonitorCollusion.lean:203 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem phase_learning (K : Bool → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (L : ℝ) (hK0 : ∀ φ h z, 0 ≤ K φ h z) (hdom : ∀ φ, Dominated (K φ) c) (hc0 : ∀ g o, 0 ≤ c g o) (hL0 : 0 ≤ L) (hL : ∀ g, ∑ o, c g o ≤ L) (guess : List O → Bool → ℝ) (hg : ∀ t, IsDist (guess t)) (m : ℕ) : ∑ φ, (1 / 2 : ℝ) * val (K φ) (fun t => guess t φ) m [] ≤ (1 / 2) * L ^ m
~~~

### 560. bscK_dist

Source: ControlStack/Families/F6/MonitorCollusion.lean:216 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bscK_dist (φ : Bool) (h : List (Unit × Bool)) : IsDist (bscK φ h)
~~~

### 561. phase_example

Source: ControlStack/Families/F6/MonitorCollusion.lean:223 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem phase_example (guess : List Bool → Bool → ℝ) (hg : ∀ t, IsDist (guess t)) : ∑ φ, (1 / 2 : ℝ) * val (bscK φ) (fun t => guess t φ) 10 [] < 0.553
~~~

## ControlStack/Families/F6/MonitorEnsemble.lean

### 562. P_mono

Source: ControlStack/Families/F6/MonitorEnsemble.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem P_mono {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (E F : Ω → Bool) (h : ∀ ω, E ω = true → F ω = true) : P μ E ≤ P μ F
~~~

### 563. escape_le_each

Source: ControlStack/Families/F6/MonitorEnsemble.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem escape_le_each {Ω : Type} [Fintype Ω] {m : ℕ} (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (miss : Fin m → Ω → Bool) (j : Fin m) : P μ (allMiss miss) ≤ P μ (miss j)
~~~

### 564. escape_le_recall

Source: ControlStack/Families/F6/MonitorEnsemble.lean:69 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem escape_le_recall {Ω : Type} [Fintype Ω] {m : ℕ} (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (miss : Fin m → Ω → Bool) (r : Fin m → ℝ) (hr : ∀ j, P μ (miss j) ≤ 1 - r j) : ∀ j, P μ (allMiss miss) ≤ 1 - r j
~~~

### 565. correlated_tight

Source: ControlStack/Families/F6/MonitorEnsemble.lean:76 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem correlated_tight (q : ℝ) : P (fun ω : Bool => if ω then q else 1 - q) (allMiss (fun (_ : Fin 3) ω => ω)) = q ∧ ∀ j : Fin 3, P (fun ω : Bool => if ω then q else 1 - q) ((fun (_ : Fin 3) ω => ω) j) = q
~~~

### 566. indep_dist

Source: ControlStack/Families/F6/MonitorEnsemble.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem indep_dist {m : ℕ} (q : Fin m → ℝ) : ∑ x, indepW q x = 1
~~~

### 567. indepW_nonneg

Source: ControlStack/Families/F6/MonitorEnsemble.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem indepW_nonneg {m : ℕ} (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1) (x : Fin m → Bool) : 0 ≤ indepW q x
~~~

### 568. indep_escape

Source: ControlStack/Families/F6/MonitorEnsemble.lean:99 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem indep_escape {m : ℕ} (q r : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j) (hqr : ∀ j, q j ≤ 1 - r j) : P (indepW q) (allMiss (fun j x => x j)) = ∏ j, q j ∧ ∏ j, q j ≤ ∏ j, (1 - r j)
~~~

### 569. mixture_escape_eq

Source: ControlStack/Families/F6/MonitorEnsemble.lean:120 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mixture_escape_eq {m : ℕ} (b : ℝ) (ν : (Fin m → Bool) → ℝ) (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j) : P (mixture b ν q) escapes = b * P ν (allMiss (fun j x => x j)) + (1 - b) * ∏ j, q j
~~~

### 570. blind_spot_escape

Source: ControlStack/Families/F6/MonitorEnsemble.lean:133 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem blind_spot_escape {m : ℕ} (β b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ β) (ν : (Fin m → Bool) → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (q r : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j) (hqr : ∀ j, q j ≤ 1 - r j) : P (mixture b ν q) escapes ≤ β + ∏ j, (1 - r j)
~~~

### 571. beta_necessary

Source: ControlStack/Families/F6/MonitorEnsemble.lean:149 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem beta_necessary : P (mixture (1 / 20) (fun x => if x = (fun _ => true) then 1 else 0) (fun (_ : Fin 3) => 2 / 5)) escapes = 1 / 20 + 38 / 625 ∧ (8 : ℝ) / 125 < 1 / 20 + 38 / 625 ∧ (1 : ℝ) / 20 + 38 / 625 ≤ 1 / 20 + 8 / 125
~~~

### 572. ensemble_adaptive

Source: ControlStack/Families/F6/MonitorEnsemble.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ensemble_adaptive {N : ℕ} {Y : Type} [Fintype Y] (k Bh : ℕ) (hB : Bh ≤ N) (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hens : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then e else 1)) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) (recallSucc (N
~~~

### 573. ensemble_example

Source: ControlStack/Families/F6/MonitorEnsemble.lean:190 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ensemble_example : (1 : ℝ) / 20 + ∏ _j : Fin 3, (1 - 3 / 5 : ℝ) = 57 / 500 ∧ ∑ j ∈ range 100, hypMiss 100 10 (j + 1) (1 - 57 / 500) ≤ 103 / 10 ∧ ∑ j ∈ range 100, hypMiss 100 10 (j + 1) (3 / 5) ≤ 47 / 3
~~~

## ControlStack/Families/F6/ReservedAudit.lean

### 574. pU_nonneg

Source: ControlStack/Families/F6/ReservedAudit.lean:70 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pU_nonneg (N B : ℕ) (S : Finset (Fin N)) : 0 ≤ pU N B S
~~~

### 575. reserved_leak_bound_all

Source: ControlStack/Families/F6/ReservedAudit.lean:76 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reserved_leak_bound_all (k B : ℕ) (hB : B ≤ N) (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (hK0 : ∀ S h z, 0 ≤ K S h z) (hdom : ∀ S h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o) (hK1 : ∀ S h, ∑ z, K S h z ≤ 1) (hcl0 : ∀ g o, 0 ≤ cl g o) : ∑ S : Finset (Fin N), pU N B S * val (K S) (successInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * mass (dropStop caughtFlag cl) N []
~~~

### 576. reserved_leak_bound

Source: ControlStack/Families/F6/ReservedAudit.lean:114 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reserved_leak_bound (k B : ℕ) (hB : B ≤ N) (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1) (hdom : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o) (hcl0 : ∀ g o, 0 ≤ cl g o) : ∑ S : Finset (Fin N), pU N B S * val (K S) (successInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * mass (dropStop caughtFlag cl) N []
~~~

### 577. reserved_adaptive

Source: ControlStack/Families/F6/ReservedAudit.lean:157 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reserved_adaptive (k Bh : ℕ) (hB : Bh ≤ N) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hmarg : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, ∑ c : Bool, K S h (y, (a, (), c)) ≤ σ (h.map Prod.snd) a) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) (successInd k S) N [] ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ)
~~~

### 578. flagRun_inv

Source: ControlStack/Families/F6/ReservedAudit.lean:202 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem flagRun_inv (Bf : ℕ) (fs : List Bool) (st : ℕ × ℕ) (h : st.2 = min st.1 Bf) : (fs.foldl (flagStep Bf) st).2 = min (fs.foldl (flagStep Bf) st).1 Bf
~~~

### 579. flagRun_audits_le

Source: ControlStack/Families/F6/ReservedAudit.lean:215 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem flagRun_audits_le (Bf : ℕ) (fs : List Bool) : (flagRun Bf fs).2 ≤ Bf
~~~

### 580. reservedK_nonneg

Source: ControlStack/Families/F6/ReservedAudit.lean:229 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reservedK_nonneg (Bf : ℕ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (φ : Finset (Fin N) → List (Bool × AOut Unit) → Bool → Bool → ℝ) (hφ : ∀ S h a, IsDist (φ S h a)) (S : Finset (Fin N)) (h : List (Bool × AOut Unit)) (z : Bool × AOut Unit) : 0 ≤ reservedK Bf σ φ S h z
~~~

### 581. sum_ite_bool

Source: ControlStack/Families/F6/ReservedAudit.lean:235 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_ite_bool (e : Bool) : ∑ c : Bool, (if c = e then (1 : ℝ) else 0) = 1
~~~

### 582. reservedK_sum_c

Source: ControlStack/Families/F6/ReservedAudit.lean:239 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reservedK_sum_c (Bf : ℕ) (σ : List (AOut Unit) → Bool → ℝ) (φ : Finset (Fin N) → List (Bool × AOut Unit) → Bool → Bool → ℝ) (S : Finset (Fin N)) (h : List (Bool × AOut Unit)) (y a : Bool) : ∑ c : Bool, reservedK Bf σ φ S h (y, (a, (), c)) = σ (h.map Prod.snd) a * φ S h a y
~~~

### 583. reservedK_sum

Source: ControlStack/Families/F6/ReservedAudit.lean:247 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reservedK_sum (Bf : ℕ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (φ : Finset (Fin N) → List (Bool × AOut Unit) → Bool → Bool → ℝ) (hφ : ∀ S h a, IsDist (φ S h a)) (S : Finset (Fin N)) (h : List (Bool × AOut Unit)) : ∑ z, reservedK Bf σ φ S h z ≤ 1
~~~

### 584. reserved_policy_bound

Source: ControlStack/Families/F6/ReservedAudit.lean:261 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reserved_policy_bound (k Bh Bf : ℕ) (hB : Bh ≤ N) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (φ : Finset (Fin N) → List (Bool × AOut Unit) → Bool → Bool → ℝ) (hφ : ∀ S h a, IsDist (φ S h a)) : ∑ S : Finset (Fin N), pU N Bh S * val (reservedK Bf σ φ S) (successInd k S) N [] ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ)
~~~

### 585. flag_audits_le

Source: ControlStack/Families/F6/ReservedAudit.lean:281 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem flag_audits_le (Bf : ℕ) (flags : Fin N → Bool) : (univ.filter (fun i => Necessity.audited Bf flags i = true)).card ≤ Bf
~~~

### 586. reserved_total_le

Source: ControlStack/Families/F6/ReservedAudit.lean:308 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reserved_total_le (Bh Bf : ℕ) (S : Finset (Fin N)) (hS : S.card = Bh) (flags : Fin N → Bool) : (S ∪ univ.filter (fun i => Necessity.audited Bf flags i = true)).card ≤ Bh + Bf
~~~

### 587. sum_pU

Source: ControlStack/Families/F6/ReservedAudit.lean:326 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_pU (B : ℕ) (hB : B ≤ N) : ∑ S : Finset (Fin N), pU N B S = 1
~~~

### 588. sum_pU_disjoint

Source: ControlStack/Families/F6/ReservedAudit.lean:332 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_pU_disjoint (B k : ℕ) (A : Finset (Fin N)) (hA : A.card = k) : ∑ S : Finset (Fin N), pU N B S * (if Disjoint S A then 1 else 0) = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

### 589. missRecall_const

Source: ControlStack/Families/F6/ReservedAudit.lean:346 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem missRecall_const (B : ℕ) (A : Finset (Fin N)) (r : ℝ) : missRecall B A (fun _ => r) = ∑ S : Finset (Fin N), pU N B S * (1 - r) ^ (S ∩ A).card
~~~

### 590. recall_miss_le

Source: ControlStack/Families/F6/ReservedAudit.lean:354 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recall_miss_le (B k : ℕ) (hB : B ≤ N) (A : Finset (Fin N)) (hA : A.card = k) (r : ℝ) (rec : Fin N → ℝ) (hr0 : 0 ≤ r) (hrec : ∀ i, r ≤ rec i ∧ rec i ≤ 1) : missRecall B A rec ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) + (1 - (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)) * (1 - r)
~~~

### 591. observable_reserved_nogo

Source: ControlStack/Families/F6/ReservedAudit.lean:392 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem observable_reserved_nogo {N Bh k : ℕ} (S : Finset (Fin N)) (hS : S.card = Bh) (hk : k ≤ N - Bh) : ∃ A : Finset (Fin N), A.card = k ∧ Disjoint S A
~~~

### 592. observable_and_exhausted

Source: ControlStack/Families/F6/ReservedAudit.lean:400 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem observable_and_exhausted : Disjoint ({0} : Finset (Fin 4)) {2, 3} ∧ ∀ i ∈ ({2, 3} : Finset (Fin 4)), Necessity.audited 1 (fun _ => true) i = false
~~~

### 593. recall_zero_vacuous

Source: ControlStack/Families/F6/ReservedAudit.lean:407 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recall_zero_vacuous {N : ℕ} (B k : ℕ) (hB : B ≤ N) (A : Finset (Fin N)) : missRecall B A (fun _ => 0) = 1 ∧ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) + (1 - (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)) * (1 - 0) = 1
~~~

### 594. reserved_example

Source: ControlStack/Families/F6/ReservedAudit.lean:419 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reserved_example (Bf : ℕ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (φ : Finset (Fin 100) → List (Bool × AOut Unit) → Bool → Bool → ℝ) (hφ : ∀ S h a, IsDist (φ S h a)) : ∑ S : Finset (Fin 100), pU 100 10 S * val (reservedK Bf σ φ S) (successInd 5 S) 100 [] ≤ (10104934117421 : ℝ) / 17310309456440
~~~

### 595. recall_example

Source: ControlStack/Families/F6/ReservedAudit.lean:429 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recall_example (A : Finset (Fin 100)) (hA : A.card = 5) (rec : Fin 100 → ℝ) (hrec : ∀ i, 1 / 2 ≤ rec i ∧ rec i ≤ 1) : missRecall 10 A rec ≤ ((10104934117421 : ℝ) / 17310309456440 + 1) / 2
~~~

## ControlStack/Families/F6/ReservedRecall.lean

### 596. count_inter

Source: ControlStack/Families/F6/ReservedRecall.lean:53 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem count_inter (B k j : ℕ) (A : Finset (Fin N)) (hA : A.card = k) (hj : j ≤ B) : ((AuditBudget.randomSchedules N B).filter (fun S => (S ∩ A).card = j)).card = Nat.choose k j * Nat.choose (N - k) (B - j)
~~~

### 597. hypMiss_nonneg

Source: ControlStack/Families/F6/ReservedRecall.lean:108 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hypMiss_nonneg (N B k : ℕ) (r : ℝ) (hr1 : r ≤ 1) : 0 ≤ hypMiss N B k r
~~~

### 598. missRecall_closed

Source: ControlStack/Families/F6/ReservedRecall.lean:116 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem missRecall_closed (B k : ℕ) (A : Finset (Fin N)) (hA : A.card = k) (r : ℝ) : missRecall B A (fun _ => r) = hypMiss N B k r
~~~

### 599. missRecall_anti

Source: ControlStack/Families/F6/ReservedRecall.lean:141 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem missRecall_anti (B : ℕ) (A A' : Finset (Fin N)) (hAA : A ⊆ A') (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : missRecall B A' (fun _ => r) ≤ missRecall B A (fun _ => r)
~~~

### 600. miss_ge_k

Source: ControlStack/Families/F6/ReservedRecall.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem miss_ge_k (B k : ℕ) (A : Finset (Fin N)) (hA : k ≤ A.card) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : missRecall B A (fun _ => r) ≤ hypMiss N B k r
~~~

### 601. hypMiss_le_two_term

Source: ControlStack/Families/F6/ReservedRecall.lean:157 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hypMiss_le_two_term (B k : ℕ) (hB : B ≤ N) (hk : k ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : hypMiss N B k r ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) + (1 - (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)) * (1 - r)
~~~

### 602. cval_factor

Source: ControlStack/Families/F6/ReservedRecall.lean:175 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_factor (c f : List O → O → ℝ) (Φ : List O → ℝ) (B : List O → ℝ) (hΦ : ∀ g o, Φ (g ++ [o]) = Φ g * f g o) : ∀ n g, Φ g * cval (fun g o => c g o * f g o) B n g = cval c (fun t => B t * Φ t) n g
~~~

### 603. term_snoc

Source: ControlStack/Families/F6/ReservedRecall.lean:207 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem term_snoc (r : ℝ) (S : Finset (Fin N)) (g : List (AOut Unit)) (o : AOut Unit) (j : Fin N) : (if j ∈ S ∧ attNC (g ++ [o]) j = true then 1 - r else 1) = (if j ∈ S ∧ attNC g j = true then 1 - r else 1) * (if (j : ℕ) = g.length ∧ j ∈ S ∧ (o.1 = true ∧ o.2.2 = false) then 1 - r else 1)
~~~

### 604. prod_single_fac

Source: ControlStack/Families/F6/ReservedRecall.lean:230 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prod_single_fac (r : ℝ) (S : Finset (Fin N)) (g : List (AOut Unit)) (o : AOut Unit) : ∏ j : Fin N, (if (j : ℕ) = g.length ∧ j ∈ S ∧ (o.1 = true ∧ o.2.2 = false) then 1 - r else 1) = fac r S g o
~~~

### 605. phi_snoc

Source: ControlStack/Families/F6/ReservedRecall.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem phi_snoc (r : ℝ) (S : Finset (Fin N)) (g : List (AOut Unit)) (o : AOut Unit) : phi r S (g ++ [o]) = phi r S g * fac r S g o
~~~

### 606. phi_nil

Source: ControlStack/Families/F6/ReservedRecall.lean:257 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem phi_nil (r : ℝ) (S : Finset (Fin N)) : phi r S [] = 1
~~~

### 607. phi_live

Source: ControlStack/Families/F6/ReservedRecall.lean:261 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem phi_live (r : ℝ) (S : Finset (Fin N)) (t : List (AOut Unit)) (hl : (t.all fun o => !caughtFlag o) = true) : phi r S t = (1 - r) ^ (S ∩ attackSet (N
~~~

### 608. adaptive_recall_bound

Source: ControlStack/Families/F6/ReservedRecall.lean:292 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adaptive_recall_bound {Y : Type} [Fintype Y] (k Bh : ℕ) (_hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) (recallSucc (N
~~~

### 609. adaptive_recall_two_term

Source: ControlStack/Families/F6/ReservedRecall.lean:377 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adaptive_recall_two_term {Y : Type} [Fintype Y] (k Bh : ℕ) (hB : Bh ≤ N) (hk : k ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) (recallSucc (N
~~~

### 610. recall_instance_bound

Source: ControlStack/Families/F6/ReservedRecall.lean:402 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recall_instance_bound (k Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) : ∑ S : Finset (Fin N), pU N Bh S * val (recallK r σ S) (recallSucc (N
~~~

### 611. recall_example

Source: ControlStack/Families/F6/ReservedRecall.lean:424 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recall_example (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) : ∑ S : Finset (Fin 100), pU 100 10 S * val (recallK (1 / 2) σ S) (recallSucc (N
~~~

## ControlStack/GateComposition.lean

### 612. shared_invariants

Source: ControlStack/GateComposition.lean:18 | Family: F8 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem shared_invariants {S A : Type} (P Q : S → Prop) (step : S → A → S) (s : S) (actions : List A) (hJoint : ∀ (x : S) (a : A), P x → Q x → P (step x a) ∧ Q (step x a)) (h : P s ∧ Q s) : P (run step s actions) ∧ Q (run step s actions)
~~~

### 613. confused_deputy_counterexample

Source: ControlStack/GateComposition.lean:45 | Family: F8 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem confused_deputy_counterexample : (unsafeDeputyStep { gateAApproved
~~~

## ControlStack/GatewayCore.lean

### 614. frozen

Source: ControlStack/GatewayCore.lean:72 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma frozen (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (v : View S slots) (h : st.snap = some v) (tr : List (Ev C R)) : runG valid st tr = st
~~~

### 615. close_freezes

Source: ControlStack/GatewayCore.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem close_freezes (valid : (c : Fin C) → R → Option (S c)) (pre post : List (Ev C R)) : finalView (runG valid (init (S
~~~

### 616. blanked_stays

Source: ControlStack/GatewayCore.lean:101 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma blanked_stays (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (hb : st.blanked = true) (hs : st.snap = none ∨ st.snap = some nullView) (tr : List (Ev C R)) : (runG valid st tr).blanked = true ∧ ((runG valid st tr).snap = none ∨ (runG valid st tr).snap = some nullView)
~~~

### 617. finalView_blanked

Source: ControlStack/GatewayCore.lean:144 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma finalView_blanked (st : GSt S slots) (hb : st.blanked = true) (hs : st.snap = none ∨ st.snap = some nullView) : finalView st = nullView
~~~

### 618. refusal_blanks

Source: ControlStack/GatewayCore.lean:152 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refusal_blanks (valid : (c : Fin C) → R → Option (S c)) (pre post : List (Ev C R)) (e : Ev C R) (hpre : (runG valid (init (S
~~~

### 619. other_blanks

Source: ControlStack/GatewayCore.lean:184 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem other_blanks (valid : (c : Fin C) → R → Option (S c)) (pre post : List (Ev C R)) (hpre : (runG valid (init (S
~~~

### 620. card_prefixes

Source: ControlStack/GatewayCore.lean:200 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem card_prefixes [∀ c, Fintype (S c)] [∀ c, DecidableEq (S c)] : Fintype.card (Prefixes S slots) = viewSpace slots (fun c => Fintype.card (S c))
~~~

### 621. viewOf_reachable

Source: ControlStack/GatewayCore.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma viewOf_reachable (st : GSt S slots) (h : ∀ c, (st.buf c).length ≤ slots c) : viewOf st ∈ Set.range (embedAll (S
~~~

### 622. gstep_inv

Source: ControlStack/GatewayCore.lean:217 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma gstep_inv (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (e : Ev C R) (h : Inv st) : Inv (gstep valid st e)
~~~

### 623. runG_inv

Source: ControlStack/GatewayCore.lean:247 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma runG_inv (valid : (c : Fin C) → R → Option (S c)) (tr : List (Ev C R)) (st : GSt S slots) (h : Inv st) : Inv (runG valid st tr)
~~~

### 624. view_reachable

Source: ControlStack/GatewayCore.lean:254 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem view_reachable (valid : (c : Fin C) → R → Option (S c)) (tr : List (Ev C R)) : finalView (runG valid (init (S
~~~

### 625. core_bound

Source: ControlStack/GatewayCore.lean:265 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem core_bound {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R] [∀ c, Fintype (S c)] [∀ c, DecidableEq (S c)] [Fintype (Ev C R)] (valid : (c : Fin C) → R → Option (S c)) (L : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ) (dec : Ω → View S slots → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : (∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ tr, enc ω m tr * dec ω (finalView (runG valid (init (S
~~~

### 626. sc01_episode_views

Source: ControlStack/GatewayCore.lean:297 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc01_episode_views : viewSpace (C
~~~

## ControlStack/GatewayModel.lean

### 627. blank_absorbing

Source: ControlStack/GatewayModel.lean:47 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem blank_absorbing {R S : Type} (valid : R → Option S) (slots : ℕ) (tr : List (Act R)) (st : St S) (h : st.blanked = true) : (tr.foldl (step valid slots) st).blanked = true
~~~

### 628. other_blanks

Source: ControlStack/GatewayModel.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem other_blanks {R S : Type} (valid : R → Option S) (slots : ℕ) (pre post : List (Act R)) : deliver slots (run valid slots (pre ++ Act.other :: post)) = fun _ => none
~~~

### 629. push_dist

Source: ControlStack/GatewayModel.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_dist {T V : Type} [Fintype T] [Fintype V] [DecidableEq V] (f : T → V) (p : T → ℝ) (hp : IsDist p) : IsDist (push f p)
~~~

### 630. gateway_bound

Source: ControlStack/GatewayModel.lean:84 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem gateway_bound {Ω M R S : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R] [Fintype S] [DecidableEq S] (valid : R → Option S) (slots L : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → (Fin L → Act R) → ℝ) (dec : Ω → (Fin slots → Option S) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : (∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ tr, enc ω m tr * dec ω (deliver slots (run valid slots (List.ofFn tr))) m)) ≤ ((Fintype.card S : ℝ) + 1) ^ slots / (Fintype.card M : ℝ)
~~~

### 631. buf_le

Source: ControlStack/GatewayModel.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem buf_le {R S : Type} (valid : R → Option S) (slots : ℕ) (tr : List (Act R)) (st : St S) (h : st.buf.length ≤ slots) : (tr.foldl (step valid slots) st).buf.length ≤ slots
~~~

### 632. deliver_eq_embed

Source: ControlStack/GatewayModel.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deliver_eq_embed {S : Type} (slots : ℕ) (st : St S) (h : st.buf.length ≤ slots) : deliver slots st = embedPrefix slots (toPrefix slots st h)
~~~

### 633. gateway_bound_reachable

Source: ControlStack/GatewayModel.lean:153 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gateway_bound_reachable {Ω M R S : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R] [Fintype S] [DecidableEq S] (valid : R → Option S) (slots L : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → (Fin L → Act R) → ℝ) (dec : Ω → (Fin slots → Option S) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : (∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ tr, enc ω m tr * dec ω (deliver slots (run valid slots (List.ofFn tr))) m)) ≤ (∑ j : Fin (slots + 1), (Fintype.card S : ℝ) ^ (j : ℕ)) / (Fintype.card M : ℝ)
~~~

## ControlStack/HaltLiveness.lean

### 634. run_append

Source: ControlStack/HaltLiveness.lean:18 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_append {St Op Eff : Type} (G : System St Op Eff) (s : St) (before after : List Op) : G.run s (before ++ after) = G.run (G.run s before) after
~~~

### 635. delivered_halt_absorbs

Source: ControlStack/HaltLiveness.lean:24 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem delivered_halt_absorbs {St Op Eff : Type} (G : System St Op Eff) (sh : St × Bool) (rest : List (HOp Op)) : (withHalt G).run sh (.halt :: rest) = (sh.1, true)
~~~

### 636. liveness_if_delivered

Source: ControlStack/HaltLiveness.lean:40 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem liveness_if_delivered {St Op Eff : Type} (G : System St Op Eff) (s : St) (n : Nat) (ops : List (HOp Op)) (h : DeliveredWithin n ops) : ((withHalt G).run (s, false) ops).2 = true
~~~

### 637. effects_frozen_after_delivered_halt

Source: ControlStack/HaltLiveness.lean:51 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem effects_frozen_after_delivered_halt {St Op Eff : Type} (G : System St Op Eff) (s : St) (before after : List (HOp Op)) : (withHalt G).effects ((withHalt G).run (s, false) (before ++ (.halt :: after))) = (withHalt G).effects ((withHalt G).run (s, false) before)
~~~

### 638. ordinary_operations_never_halt

Source: ControlStack/HaltLiveness.lean:62 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem ordinary_operations_never_halt {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List Op) : ((withHalt G).run (s, false) (ops.map HOp.op)).2 = false
~~~

## ControlStack/HoneypotBridgeProof.lean

### 639. honeypotPasses_step

Source: ControlStack/HoneypotBridgeProof.lean:34 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honeypotPasses_step {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (n k : ℕ) : Pr[= k | honeypotPasses H M D (n + 1)] = Pr[= true | H >>= M >>= D] * Pr[= k | (fun a => a + 1) <$> honeypotPasses H M D n] + Pr[= false | H >>= M >>= D] * Pr[= k | honeypotPasses H M D n]
~~~

### 640. honeypotPasses_probOutput

Source: ControlStack/HoneypotBridgeProof.lean:42 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honeypotPasses_probOutput {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (n k : ℕ) : Pr[= k | honeypotPasses H M D n] = (n.choose k : ENNReal) * Pr[= true | H >>= M >>= D] ^ k * Pr[= false | H >>= M >>= D] ^ (n - k)
~~~

### 641. bridge

Source: ControlStack/HoneypotBridgeProof.lean:76 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bridge : BridgeClaim
~~~

## ControlStack/LifetimeLedger.lean

### 642. pr_append_one

Source: ControlStack/LifetimeLedger.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma pr_append_one (ℓ ℓ' : L) (k : ℕ) (adm : List (L × ℕ)) : pr ℓ' (adm ++ [(ℓ, k)]) = pr ℓ' adm * (if ℓ = ℓ' then k else 1)
~~~

### 643. step_inv

Source: ControlStack/LifetimeLedger.lean:69 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma step_inv (cap : ℕ) (s : Option (L → ℕ)) (adm : List (L × ℕ)) (e : Ev L) (he : ¬ e.isRestore) (h : Inv cap (s, adm)) : Inv cap ((step cap s e).1, adm ++ (step cap s e).2.toList)
~~~

### 644. run_inv

Source: ControlStack/LifetimeLedger.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma run_inv (cap : ℕ) : ∀ (es : List (Ev L)) (st : Option (L → ℕ) × List (L × ℕ)), (∀ e ∈ es, ¬ e.isRestore) → Inv cap st → Inv cap (run cap st es) | [], st, _, h => h | e :: es, (s, adm), hes, h => by simp only [run] exact run_inv cap es _ (fun e' he' => hes e' (List.mem_cons_of_mem e he')) (step_inv cap s adm e (hes e List.mem_cons_self) h) theorem ledger_safe (cap : ℕ) (hcap : 1 ≤ cap) (es : List (Ev L)) (hes : ∀ e ∈ es, ¬ e.isRestore) (ℓ : L) : pr ℓ (run cap (some (fun _ => 1), []) es).2 ≤ cap
~~~

### 645. ledger_safe

Source: ControlStack/LifetimeLedger.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ledger_safe (cap : ℕ) (hcap : 1 ≤ cap) (es : List (Ev L)) (hes : ∀ e ∈ es, ¬ e.isRestore) (ℓ : L) : pr ℓ (run cap (some (fun _ => 1), []) es).2 ≤ cap
~~~

### 646. restore_breaks

Source: ControlStack/LifetimeLedger.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem restore_breaks (cap : ℕ) (hcap : 2 ≤ cap) (ℓ : L) : cap < pr ℓ (run cap (some (fun _ => 1), []) [.charge ℓ cap, .restore (fun _ => 1), .charge ℓ cap]).2
~~~

### 647. lifetime_secret_bound

Source: ControlStack/LifetimeLedger.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lifetime_secret_bound {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] {E : ℕ} (V : Fin E → Type) [∀ e, Fintype (V e)] [∀ e, DecidableEq (V e)] (cap : ℕ) (hV : ∏ e, Fintype.card (V e) ≤ cap) (ρ : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ) (dec : Ω → ((e : Fin E) → V e) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (cap : ℝ) / (Fintype.card M : ℝ)
~~~

## ControlStack/MultiStep.lean

### 648. V_zero

Source: ControlStack/MultiStep.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem V_zero {A : Type} [Fintype A] (π κ : List A → A → ℝ) (h : List A) : V π κ 0 h = 1
~~~

### 649. V_succ

Source: ControlStack/MultiStep.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem V_succ {A : Type} [Fintype A] (π κ : List A → A → ℝ) (k : ℕ) (h : List A) : V π κ (k + 1) h = ∑ a, π h a * (1 - κ h a) * V π κ k (h ++ [a])
~~~

### 650. survival_bounds

Source: ControlStack/MultiStep.lean:54 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_bounds {A : Type} [Fintype A] (π κ : List A → A → ℝ) (hπ : IsPolicy π) (hκ : IsMonitor κ) (k : ℕ) (h : List A) : 0 ≤ V π κ k h ∧ V π κ k h ≤ 1
~~~

### 651. survival_le

Source: ControlStack/MultiStep.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_le {A : Type} [Fintype A] (π κ : List A → A → ℝ) (hπ : IsPolicy π) (hκ : IsMonitor κ) (c : ℝ) (hc1 : c ≤ 1) (hcκ : ∀ h a, c ≤ κ h a) (k : ℕ) (h : List A) : V π κ k h ≤ (1 - c) ^ k
~~~

### 652. survival_const

Source: ControlStack/MultiStep.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_const {A : Type} [Fintype A] (π : List A → A → ℝ) (hπ : IsPolicy π) (c : ℝ) (k : ℕ) (h : List A) : V π (fun _ _ => c) k h = (1 - c) ^ k
~~~

### 653. V_never

Source: ControlStack/MultiStep.lean:104 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem V_never {A : Type} [Fintype A] (π : List A → A → ℝ) (hπ : IsPolicy π) (k : ℕ) (h : List A) : V π (fun _ _ => 0) k h = 1
~~~

### 654. V_always

Source: ControlStack/MultiStep.lean:109 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem V_always {A : Type} [Fintype A] (π : List A → A → ℝ) (k : ℕ) (h : List A) : V π (fun _ _ => 1) (k + 1) h = 0
~~~

### 655. seeded_marginal

Source: ControlStack/MultiStep.lean:125 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seeded_marginal {A : Type} (c : ℝ) (h : List A) (a : A) : seededMarginal c h a = c
~~~

### 656. seeded_survival

Source: ControlStack/MultiStep.lean:129 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seeded_survival {A : Type} [Fintype A] (c : ℝ) (π : List A → A → ℝ) (hπ : IsPolicy π) (k : ℕ) (hk : 1 ≤ k) (h : List A) : V π (seededκ true) k h = 0 ∧ V π (seededκ false) k h = 1 ∧ seededSurvival c π k h = 1 - c
~~~

### 657. pow_lt_self_of_two_le

Source: ControlStack/MultiStep.lean:139 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pow_lt_self_of_two_le (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (k : ℕ) (hk : 2 ≤ k) : (1 - c) ^ k < 1 - c
~~~

### 658. correlated_nogo

Source: ControlStack/MultiStep.lean:149 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem correlated_nogo {A : Type} [Fintype A] (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (π : List A → A → ℝ) (hπ : IsPolicy π) (k : ℕ) (hk : 2 ≤ k) (h : List A) : (∀ (h' : List A) (a : A), seededMarginal c h' a = c) ∧ seededSurvival c π k h = 1 - c ∧ V π (fun _ _ => c) k h = (1 - c) ^ k ∧ (1 - c) ^ k < seededSurvival c π k h
~~~

### 659. Vs_eq

Source: ControlStack/MultiStep.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Vs_eq {A Θ : Type} [Fintype A] [Fintype Θ] (π : List A → A → ℝ) (κ : Θ → List A → A → ℝ) (k : ℕ) (h : List A) (w : Θ → ℝ) : Vs π κ k h w = ∑ θ, w θ * V π (κ θ) k h
~~~

### 660. reachable_nonneg

Source: ControlStack/MultiStep.lean:184 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reachable_nonneg {A Θ : Type} (ρ : Θ → ℝ) (κ : Θ → List A → A → ℝ) (hρ : ∀ θ, 0 ≤ ρ θ) (hκ : ∀ θ, IsMonitor (κ θ)) {h : List A} {w : Θ → ℝ} (hr : Reachable ρ κ h w) : ∀ θ, 0 ≤ w θ
~~~

### 661. survival_avg

Source: ControlStack/MultiStep.lean:195 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_avg {A Θ : Type} [Fintype A] [Fintype Θ] (π : List A → A → ℝ) (hπ : IsPolicy π) (κ : Θ → List A → A → ℝ) (ρ : Θ → ℝ) (c : ℝ) (hc1 : c ≤ 1) (hpost : ∀ h w, Reachable ρ κ h w → ∀ a, c * ∑ θ, w θ ≤ ∑ θ, w θ * κ θ h a) (k : ℕ) : ∑ θ, ρ θ * V π (κ θ) k [] ≤ (1 - c) ^ k * ∑ θ, ρ θ
~~~

### 662. seeded_violates_posterior

Source: ControlStack/MultiStep.lean:225 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seeded_violates_posterior {A : Type} (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (a b : A) : let ρ : Bool → ℝ
~~~

### 663. survival_example

Source: ControlStack/MultiStep.lean:235 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_example {A : Type} [Fintype A] (π κ : List A → A → ℝ) (hπ : IsPolicy π) (hκ : IsMonitor κ) (hcκ : ∀ h a, (1 / 10 : ℝ) ≤ κ h a) (h : List A) : V π κ 5 h ≤ 0.59049
~~~

## ControlStack/OutcomeProof.lean

### 664. probOutput_isCat

Source: ControlStack/OutcomeProof.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_isCat (c : ProbComp Outcome) : Pr[= true | isCat <$> c] = Pr[= Outcome.catastrophe | c]
~~~

### 665. map_deployO

Source: ControlStack/OutcomeProof.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem map_deployO {X Z : Type} (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n : ℕ) : ∀ u h, isCat <$> deployO Bad π M D A b n u h = deploy Bad π M D A b n u h
~~~

### 666. marginal

Source: ControlStack/OutcomeProof.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem marginal : MarginalClaim
~~~

### 667. probOutput_auditO

Source: ControlStack/OutcomeProof.lean:44 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_auditO (c : ProbComp Bool) (o : Outcome) : Pr[= o | (fun caught => if caught then Outcome.caught else Outcome.catastrophe) <$> c] = Pr[= true | c] * (if o = Outcome.caught then 1 else 0) + Pr[= false | c] * (if o = Outcome.catastrophe then 1 else 0)
~~~

### 668. deployO_step

Source: ControlStack/OutcomeProof.lean:51 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployO_step {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) (o : Outcome) : Pr[= o | deployO Bad π M D A b (n+1) u h] = ∑ x, Pr[= x | π h] * ∑ z, Pr[= z | M x] * (Pr[= true | D z] * Pr[= o | (if Bad x then pure .catastrophe else deployO Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Outcome)] + Pr[= false | D z] * Pr[= o | (if u < b then (if Bad x then (fun caught => if caught then Outcome.caught else Outcome.catastrophe) <$> A h x z else deployO Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure .halted : ProbComp Outcome)])
~~~

### 669. deployO_step_real

Source: ControlStack/OutcomeProof.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployO_step_real {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) (o : Outcome) : (Pr[= o | deployO Bad π M D A b (n+1) u h]).toReal = ∑ x, (Pr[= x | π h]).toReal * ∑ z, (Pr[= z | M x]).toReal * ((Pr[= true | D z]).toReal * (Pr[= o | (if Bad x then pure .catastrophe else deployO Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Outcome)]).toReal + (1 - (Pr[= true | D z]).toReal) * (Pr[= o | (if u < b then (if Bad x then (fun caught => if caught then Outcome.caught else Outcome.catastrophe) <$> A h x z else deployO Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure .halted : ProbComp Outcome)]).toReal)
~~~

### 670. deployO_rejected

Source: ControlStack/OutcomeProof.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployO_rejected {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n : ℕ) : ∀ u h, Pr[= Outcome.rejected | deployO Bad π M D A b n u h] = 0
~~~

### 671. deployLaw

Source: ControlStack/OutcomeProof.lean:99 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployLaw : DeployLawClaim
~~~

### 672. conservation

Source: ControlStack/OutcomeProof.lean:129 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conservation : ConservationClaim
~~~

### 673. nonneg

Source: ControlStack/OutcomeProof.lean:154 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nonneg : NonnegClaim
~~~

### 674. deployO_rejected

Source: ControlStack/OutcomeProof.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployO_rejected' {X Z : Type} (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n : ℕ) : ∀ u h, Pr[= Outcome.rejected | deployO Bad π M D A b n u h] = 0
~~~

### 675. probEvent_not_toReal

Source: ControlStack/OutcomeProof.lean:190 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probEvent_not_toReal {α : Type} (c : ProbComp α) (p : α → Prop) : (Pr[fun x => ¬ p x | c]).toReal = 1 - (Pr[p | c]).toReal
~~~

### 676. gameLaw

Source: ControlStack/OutcomeProof.lean:199 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gameLaw : GameLawClaim
~~~

### 677. rateLink

Source: ControlStack/OutcomeProof.lean:231 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rateLink : RateLinkClaim
~~~

### 678. binCDF_succ_zero

Source: ControlStack/OutcomeProof.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem binCDF_succ_zero (n : ℕ) (f : ℝ) : binCDF (n + 1) 0 f = (1 - f) * binCDF n 0 f
~~~

### 679. binCDF_succ_succ

Source: ControlStack/OutcomeProof.lean:255 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem binCDF_succ_succ (n s : ℕ) (f : ℝ) : binCDF (n + 1) (s + 1) f = (1 - f) * binCDF n (s + 1) f + f * binCDF n s f
~~~

### 680. wsum_const

Source: ControlStack/OutcomeProof.lean:275 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum_const {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (φ : Z → ℝ) (μ : X → ℝ) (hM1 : ∀ x, ∑ z, M x z = 1) (hμ1 : ∑ x, μ x = 1) (a c : ℝ) : ∑ x, μ x * ∑ z, M x z * (φ z * a + (1 - φ z) * c) = (1 - flagRate M μ φ) * a + flagRate M μ φ * c
~~~

### 681. catG_benign

Source: ControlStack/OutcomeProof.lean:297 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catG_benign {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R : Hist X Z → X → Z → ℝ) (b : ℕ) (hben : ∀ h x, π h x ≠ 0 → ¬ Bad x) : ∀ n u h, catG Bad M φ π R b n u h = 0 ∧ caughtG Bad M φ π R b n u h = 0
~~~

### 682. complG_benign

Source: ControlStack/OutcomeProof.lean:312 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem complG_benign {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (μ : X → ℝ) (b : ℕ) (hM1 : ∀ x, ∑ z, M x z = 1) (hμ1 : ∑ x, μ x = 1) (hben : ∀ x, μ x ≠ 0 → ¬ Bad x) : ∀ n u h, u ≤ b → complG Bad M φ (fun _ => μ) b n u h = binCDF n (b - u) (flagRate M μ φ)
~~~

### 683. benignRecursion

Source: ControlStack/OutcomeProof.lean:341 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem benignRecursion : BenignRecursionClaim
~~~

### 684. honest

Source: ControlStack/OutcomeProof.lean:351 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest : HonestClaim
~~~

### 685. binCDF_nonneg

Source: ControlStack/OutcomeProof.lean:387 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem binCDF_nonneg (n s : ℕ) (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1) : 0 ≤ binCDF n s f
~~~

### 686. pareto

Source: ControlStack/OutcomeProof.lean:392 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pareto : ParetoClaim
~~~

### 687. witness

Source: ControlStack/OutcomeProof.lean:431 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## ControlStack/PolicyTamper.lean

### 688. policy_preserved_if_protected

Source: ControlStack/PolicyTamper.lean:31 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem policy_preserved_if_protected (p : Policy) (s : St) (ops : List Op) (h : s.activePolicy = p) : (run false s ops).activePolicy = p
~~~

### 689. tamper_possible_if_writable

Source: ControlStack/PolicyTamper.lean:42 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem tamper_possible_if_writable (s : St) (replacement : Policy) : (step true s (.attemptPolicyWrite replacement)).activePolicy = replacement
~~~

## ControlStack/RefinementProof.lean

### 690. probOutput_true_add_false_one

Source: ControlStack/RefinementProof.lean:6 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_true_add_false_one (c : ProbComp Bool) : Pr[= true | c] + Pr[= false | c] = 1
~~~

### 691. probOutput_false_toReal

Source: ControlStack/RefinementProof.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_false_toReal (c : ProbComp Bool) : (Pr[= false | c]).toReal = 1 - (Pr[= true | c]).toReal
~~~

### 692. probOutput_not_true

Source: ControlStack/RefinementProof.lean:20 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_not_true (c : ProbComp Bool) : Pr[= true | (fun caught => !caught) <$> c] = Pr[= false | c]
~~~

### 693. deploy_step

Source: ControlStack/RefinementProof.lean:24 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deploy_step {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) : Pr[= true | deploy Bad π M D A b (n+1) u h] = ∑ x, Pr[= x | π h] * ∑ z, Pr[= z | M x] * (Pr[= true | D z] * Pr[= true | (if Bad x then pure true else deploy Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Bool)] + Pr[= false | D z] * Pr[= true | (if u < b then (if Bad x then (fun caught => !caught) <$> A h x z else deploy Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure false : ProbComp Bool)])
~~~

### 694. deploy_step_real

Source: ControlStack/RefinementProof.lean:36 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deploy_step_real {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) : (Pr[= true | deploy Bad π M D A b (n+1) u h]).toReal = ∑ x, (Pr[= x | π h]).toReal * ∑ z, (Pr[= z | M x]).toReal * ((Pr[= true | D z]).toReal * (Pr[= true | (if Bad x then pure true else deploy Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Bool)]).toReal + (1 - (Pr[= true | D z]).toReal) * (Pr[= true | (if u < b then (if Bad x then (fun caught => !caught) <$> A h x z else deploy Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure false : ProbComp Bool)]).toReal)
~~~

### 695. toReal_probOutput_le_one

Source: ControlStack/RefinementProof.lean:58 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem toReal_probOutput_le_one {α : Type} (c : ProbComp α) (x : α) : (Pr[= x | c]).toReal ≤ 1
~~~

### 696. toReal_probEvent_le_one

Source: ControlStack/RefinementProof.lean:62 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem toReal_probEvent_le_one {α : Type} (c : ProbComp α) (p : α → Prop) : (Pr[p | c]).toReal ≤ 1
~~~

### 697. sum_toReal_probOutput

Source: ControlStack/RefinementProof.lean:66 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_toReal_probOutput {α : Type} [Fintype α] (c : ProbComp α) : ∑ x, (Pr[= x | c]).toReal = 1
~~~

### 698. catG_const

Source: ControlStack/RefinementProof.lean:72 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catG_const {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (b : ℕ) : ∀ n u h, catG Bad M φ π (fun _ _ _ => r) b n u h = cat Bad M φ π r b n u h
~~~

### 699. catG_congr

Source: ControlStack/RefinementProof.lean:80 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catG_congr {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R R' : Hist X Z → X → Z → ℝ) (b : ℕ) (hR : ∀ h x z, Bad x → R h x z = R' h x z) : ∀ n u h, catG Bad M φ π R b n u h = catG Bad M φ π R' b n u h
~~~

### 700. catG_le_cat

Source: ControlStack/RefinementProof.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catG_le_cat {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R : Hist X Z → X → Z → ℝ) (r : ℝ) (b : ℕ) (hπ : ∀ h x, 0 ≤ π h x) (hM : ∀ x z, 0 ≤ M x z) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) (hR : ∀ h x z, Bad x → r ≤ R h x z) : ∀ n u h, catG Bad M φ π R b n u h ≤ cat Bad M φ π r b n u h
~~~

### 701. wsum_le

Source: ControlStack/RefinementProof.lean:122 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum_le {Y : Type} [Fintype Y] (w f : Y → ℝ) (c : ℝ) (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∑ y, w y = 1) (hf : ∀ y, f y ≤ c) : ∑ y, w y * f y ≤ c
~~~

### 702. t3a

Source: ControlStack/RefinementProof.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t3a {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r A : ℝ) (b : ℕ) (hM0 : ∀ x z, 0 ≤ M x z) (hM1 : ∀ x, ∑ z, M x z = 1) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) (hπ0 : ∀ h x, 0 ≤ π h x) (hπ1 : ∀ h, ∑ x, π h x = 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hbad : ∀ x, Bad x → ∑ z, M x z * φ z ≤ A) : ∀ n u h, cat Bad M φ π r b n u h ≤ (if u < b then 1 - r + r * A else A)
~~~

### 703. final_dom

Source: ControlStack/RefinementProof.lean:185 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem final_dom (S h L r A B : ℝ) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hA : A ≤ L * h) (hB : h * S ≤ B) : S * (1 - r + r * A) ≤ (1 - r) + r * (L * B)
~~~

### 704. first_moment

Source: ControlStack/RefinementProof.lean:198 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem first_moment (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hB : binCDF (n + 1) (s + 1) h ≤ 1) : ((n : ℝ) + 1) * (h * binCDF n s h) ≤ (s : ℝ) + 1
~~~

### 705. first_moment

Source: ControlStack/RefinementProof.lean:238 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem first_moment' (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hB : binCDF (n + 1) (s + 1) h ≤ 1) : h * binCDF n s h ≤ ((s : ℝ) + 1) / ((n : ℝ) + 1)
~~~

### 706. deployG

Source: ControlStack/RefinementProof.lean:245 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployG : DeployGClaim
~~~

### 707. deploy_le

Source: ControlStack/RefinementProof.lean:258 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deploy_le : DeployClaim
~~~

### 708. deploy_exact

Source: ControlStack/RefinementProof.lean:264 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deploy_exact : DeployExactClaim
~~~

### 709. protocol

Source: ControlStack/RefinementProof.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem protocol : ProtocolClaim
~~~

### 710. endToEnd

Source: ControlStack/RefinementProof.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem endToEnd : EndToEndClaim
~~~

### 711. attain

Source: ControlStack/RefinementProof.lean:343 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attain : AttainClaim
~~~

### 712. witness

Source: ControlStack/RefinementProof.lean:375 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## ControlStack/SafetyCaseSC01.lean

### 713. step_adm

Source: ControlStack/SafetyCaseSC01.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma step_adm {L : Type} [DecidableEq L] (cap : ℕ) (s : Option (L → ℕ)) (e : Ev L) (a : L × ℕ) (h : (step cap s e).2 = some a) : ∃ ℓ k, e = .charge ℓ k ∧ a = (ℓ, k)
~~~

### 714. run_sizes

Source: ControlStack/SafetyCaseSC01.lean:32 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma run_sizes {L : Type} [DecidableEq L] (cap : ℕ) (K : ℕ) : ∀ (es : List (Ev L)) (st : Option (L → ℕ) × List (L × ℕ)), (∀ e ∈ es, ∀ ℓ k, e = .charge ℓ k → k = K) → (∀ a ∈ st.2, a.2 = K) → ∀ a ∈ (run cap st es).2, a.2 = K | [], st, _, h => h | e :: es, (s, adm), hes, h => by simp only [run] apply run_sizes cap K es _ (fun e' he' => hes e' (List.mem_cons_of_mem e he')) intro a ha rcases List.mem_append.1 ha with ha | ha · exact h a ha · cases hst : (step cap s e).2 with | none => simp [hst] at ha | some b => simp [hst] at ha; rw [ha] obtain ⟨ℓ, k, rfl, rfl⟩
~~~

### 715. pr_const

Source: ControlStack/SafetyCaseSC01.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma pr_const {L : Type} [DecidableEq L] (ℓ : L) (K : ℕ) (adm : List (L × ℕ)) (h : ∀ a ∈ adm, a.2 = K) : pr ℓ adm = K ^ (adm.filter (fun a => a.1 = ℓ)).length
~~~

### 716. ledger_five

Source: ControlStack/SafetyCaseSC01.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ledger_five {L : Type} [DecidableEq L] (es : List (Ev L)) (hes : ∀ e ∈ es, ¬ e.isRestore) (h9 : ∀ e ∈ es, ∀ ℓ k, e = .charge ℓ k → k = 9) (ℓ : L) : ((run (2 ^ 16) (some (fun _ => 1), []) es).2.filter (fun a => a.1 = ℓ)).length ≤ 5
~~~

### 717. bit_refutes

Source: ControlStack/SafetyCaseSC01.lean:78 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bit_refutes {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (enc : Ω → Bool → Unit × S → ℝ) (dec : Ω → Unit × O → Bool → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : 2 * sideSuccess ρ W enc dec ≤ ∑ o, c o
~~~

### 718. refute_threshold

Source: ControlStack/SafetyCaseSC01.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refute_threshold : (2 : ℝ) * (5551 / 10000) > 65536 / 59049
~~~

### 719. sc01_case

Source: ControlStack/SafetyCaseSC01.lean:95 | Family: F2 | Adversary: SIDE_OBSERVING | Status: PROVED_RECORDED

~~~lean
theorem sc01_case : (∀ {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ), (∀ s o, W s o ≤ c o) → (∀ o, 0 ≤ c o) → ∑ o, c o ≤ 65536 / 59049 → ∀ (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ) (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ), IsDist ρ → (∀ ω m, IsDist (enc ω m)) → (∀ ω y, IsDist (dec ω y)) → sideSuccess ρ W enc dec ≤ 1 / 2 ^ 16) ∧ (∀ p : ℝ, 0 ≤ p → p ≤ 9 / 10 → passProb p ≤ 1 / 80) ∧ (tail 64 (93382 / 100000) ≤ 1 / 80 ∧ (9 : ℝ) / 10 ≤ 93382 / 100000) ∧ (viewSpace (C
~~~

## ControlStack/ScenarioACore.lean

### 720. card_epPrefix

Source: ControlStack/ScenarioACore.lean:55 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem card_epPrefix : Fintype.card EpPrefix = 9
~~~

### 721. epView_card

Source: ControlStack/ScenarioACore.lean:60 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem epView_card : Fintype.card EpView = 9
~~~

### 722. prefixToView_viewToPrefix

Source: ControlStack/ScenarioACore.lean:71 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma prefixToView_viewToPrefix (o : ScenarioARepair.View) : prefixToView (viewToPrefix o) = o
~~~

### 723. viewToPrefix_prefixToView

Source: ControlStack/ScenarioACore.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma viewToPrefix_prefixToView (p : EpPrefix) : viewToPrefix (prefixToView p) = p
~~~

### 724. prefixEquiv_apply

Source: ControlStack/ScenarioACore.lean:99 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prefixEquiv_apply (p : EpPrefix) : prefixEquiv p = embedAll p 0 0
~~~

### 725. epView_ext

Source: ControlStack/ScenarioACore.lean:102 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma epView_ext (v w : EpView) (h : v 0 0 = w 0 0) : v = w
~~~

### 726. embedAll_viewToPrefix

Source: ControlStack/ScenarioACore.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem embedAll_viewToPrefix (v : EpView) : embedAll (prefixEquiv.symm (v 0 0)) = v
~~~

### 727. embedAll_surjective

Source: ControlStack/ScenarioACore.lean:114 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem embedAll_surjective : Function.Surjective (embedAll (C
~~~

### 728. embedAll_injective

Source: ControlStack/ScenarioACore.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem embedAll_injective : Function.Injective (embedAll (C
~~~

### 729. reachable_eq_univ

Source: ControlStack/ScenarioACore.lean:124 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reachable_eq_univ : Set.range (embedAll (C
~~~

### 730. delivered_view_coord

Source: ControlStack/ScenarioACore.lean:130 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem delivered_view_coord {R : Type} (valid : (c : Fin 1) → R → Option (Fin 8)) (tr : List (Ev 1 R)) : finalView (runG valid (init (S
~~~

### 731. card_five_prefixes

Source: ControlStack/ScenarioACore.lean:140 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem card_five_prefixes : Fintype.card (Fin 5 → EpPrefix) = 59049
~~~

### 732. lifetime_bound_prefixes

Source: ControlStack/ScenarioACore.lean:145 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lifetime_bound_prefixes {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → (Fin 5 → EpPrefix) → ℝ) (dec : Ω → (Fin 5 → EpPrefix) → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (59049 : ℝ) / 2 ^ 32 ∧ (59049 : ℝ) / 2 ^ 32 ≤ 1 / 2 ^ 16
~~~

### 733. five_episode_core_bound

Source: ControlStack/ScenarioACore.lean:163 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem five_episode_core_bound {Ω R : Type} [Fintype Ω] [Fintype R] [Fintype (Ev 1 R)] (valid : (c : Fin 1) → R → Option (Fin 8)) (L : ℕ) (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → (Fin 5 → Fin L → Ev 1 R) → ℝ) (dec : Ω → (Fin 5 → EpView) → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc (fun ω tr m => dec ω (lifetimeView valid tr) m) ≤ (59049 : ℝ) / 2 ^ 32 ∧ (59049 : ℝ) / 2 ^ 32 ≤ 1 / 2 ^ 16
~~~

### 734. card_varObs

Source: ControlStack/ScenarioACore.lean:202 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem card_varObs : Fintype.card VarObs = 66430
~~~

### 735. varObs_gt

Source: ControlStack/ScenarioACore.lean:208 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem varObs_gt : (2 : ℕ) ^ 16 < 66430
~~~

### 736. varObsEmbed_injective

Source: ControlStack/ScenarioACore.lean:216 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem varObsEmbed_injective : Function.Injective varObsEmbed
~~~

### 737. attainEnc_dist

Source: ControlStack/ScenarioACore.lean:230 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma attainEnc_dist {M V : Type} [Fintype V] [DecidableEq M] [DecidableEq V] [Nonempty V] (e : V → M) (he : Function.Injective e) (m : M) : IsDist (attainEnc e () m)
~~~

### 738. attainDec_dist

Source: ControlStack/ScenarioACore.lean:244 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma attainDec_dist {M V : Type} [Fintype M] [DecidableEq M] (e : V → M) (v : V) : IsDist (attainDec e () v)
~~~

### 739. varObs_attain

Source: ControlStack/ScenarioACore.lean:252 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem varObs_attain : (∀ m, IsDist (attainEnc varObsEmbed () m)) ∧ (∀ v, IsDist (attainDec varObsEmbed () v)) ∧ successProb (Ω
~~~

### 740. varObs_breaks_target

Source: ControlStack/ScenarioACore.lean:265 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem varObs_breaks_target : ∃ (enc : Unit → Fin (2 ^ 32) → VarObs → ℝ) (dec : Unit → VarObs → Fin (2 ^ 32) → ℝ), IsDist (fun _ : Unit => (1 : ℝ)) ∧ (∀ ω m, IsDist (enc ω m)) ∧ (∀ ω v, IsDist (dec ω v)) ∧ (1 : ℝ) / 2 ^ 16 < successProb (fun _ => 1) enc dec
~~~

## ControlStack/ScenarioARepair.lean

### 741. transcript_card

Source: ControlStack/ScenarioARepair.lean:11 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem transcript_card : Fintype.card Transcript = 59049
~~~

### 742. repair_recovery

Source: ControlStack/ScenarioARepair.lean:14 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_recovery {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → Transcript → ℝ) (dec : Ω → Transcript → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (59049 : ℝ) / 2 ^ 32
~~~

### 743. repair_target

Source: ControlStack/ScenarioARepair.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_target {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → Transcript → ℝ) (dec : Ω → Transcript → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ 1 / 2 ^ 16
~~~

## ControlStack/ScenarioASide.lean

### 744. repair_side

Source: ControlStack/ScenarioASide.lean:18 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_side {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ) (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ W enc dec ≤ 59049 * (∑ o, c o) / 2 ^ 32
~~~

### 745. repair_side_target

Source: ControlStack/ScenarioASide.lean:27 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_side_target {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (hL : ∑ o, c o ≤ 65536 / 59049) (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ) (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ W enc dec ≤ 1 / 2 ^ 16
~~~

### 746. card_obs

Source: ControlStack/ScenarioASide.lean:41 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma card_obs : Fintype.card (Transcript × Bool) ≤ 2 ^ 32
~~~

### 747. emb_inj

Source: ControlStack/ScenarioASide.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma emb_inj : Function.Injective emb
~~~

### 748. repair_one_bit_attained

Source: ControlStack/ScenarioASide.lean:56 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_one_bit_attained : ∃ (enc : Unit → Fin (2 ^ 32) → Transcript × Bool → ℝ) (dec : Unit → Transcript × Bool → Fin (2 ^ 32) → ℝ), (∀ ω m, IsDist (enc ω m)) ∧ (∀ ω y, IsDist (dec ω y)) ∧ sideSuccess (fun _ => (1 : ℝ)) idKernel enc dec = 2 * 59049 / 2 ^ 32 ∧ (1 : ℝ) / 2 ^ 16 < 2 * 59049 / 2 ^ 32
~~~

### 749. bsc_lifetime_ok

Source: ControlStack/ScenarioASide.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bsc_lifetime_ok : (2 * (1 - (49 : ℝ) / 100)) ^ 5 ≤ 65536 / 59049
~~~

### 750. bsc_lifetime_fails

Source: ControlStack/ScenarioASide.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bsc_lifetime_fails : (65536 : ℝ) / 59049 < (2 * (1 - (48 : ℝ) / 100)) ^ 5
~~~

## ControlStack/ScenarioAUsefulness.lean

### 751. passProb_eq

Source: ControlStack/ScenarioAUsefulness.lean:28 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma passProb_eq (p : ℝ) : passProb p = 64 * p ^ 63 - 63 * p ^ 64
~~~

### 752. passProb_mono

Source: ControlStack/ScenarioAUsefulness.lean:34 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma passProb_mono : MonotoneOn passProb (Set.Icc 0 1)
~~~

### 753. false_pass_le

Source: ControlStack/ScenarioAUsefulness.lean:55 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem false_pass_le (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 9 / 10) : passProb p ≤ 1 / 80
~~~

### 754. endpoint64

Source: ControlStack/ScenarioAUsefulness.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem endpoint64 : tail 64 (93382 / 100000) ≤ 1 / 80 ∧ 1 / 80 < tail 64 (93383 / 100000)
~~~

### 755. endpoint63

Source: ControlStack/ScenarioAUsefulness.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem endpoint63 : tail 63 (90438 / 100000) ≤ 1 / 80 ∧ 1 / 80 < tail 63 (90439 / 100000)
~~~

### 756. reject62

Source: ControlStack/ScenarioAUsefulness.lean:69 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reject62 : 1 / 80 < tail 62 (9 / 10)
~~~

### 757. endpoints_clear_floor

Source: ControlStack/ScenarioAUsefulness.lean:75 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem endpoints_clear_floor : (9 : ℝ) / 10 ≤ 90438 / 100000 ∧ (90438 : ℝ) / 100000 ≤ 93382 / 100000
~~~

## ControlStack/Scenarios/AuthInstancesA.lean

### 758. sc16_review_step

Source: ControlStack/Scenarios/AuthInstancesA.lean:44 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc16_review_step (R : Roles) (h : ℕ → ℕ) (s : SC16.St) (o : SC16.Op) (x : Review) (hx : x ∈ (SC16.step R h full s o).reviews) : x ∈ s.reviews ∨ ∃ c, claim16 o = some c ∧ (o = .review c x.d ∧ c = x.reviewer ∧ c ∈ R.reviewers)
~~~

### 759. sc16_appr_step

Source: ControlStack/Scenarios/AuthInstancesA.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc16_appr_step (R : Roles) (h : ℕ → ℕ) (s : SC16.St) (o : SC16.Op) (x : Appr) (hx : x ∈ (SC16.step R h full s o).approvals) : x ∈ s.approvals ∨ ∃ c, claim16 o = some c ∧ (o = .approve c x.n x.d x.target x.slot ∧ c = x.approver ∧ c ∈ R.approvers)
~~~

### 760. sc16_safe_authenticated

Source: ControlStack/Scenarios/AuthInstancesA.lean:58 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc16_safe_authenticated (R : Roles) (h : ℕ → ℕ) (U : List ℕ) (ops : List (ℕ × SC16.Op)) (hUr : ∀ u ∈ U, u ∉ R.reviewers) (hUa : ∀ u ∈ U, u ∉ R.approvers) : Good R h (authRun (SC16.step R h full) claim16 SC16.init ops) ∧ (∀ rv ∈ (authRun (SC16.step R h full) claim16 SC16.init ops).reviews, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .review c rv.d ∧ c = rv.reviewer ∧ c ∈ R.reviewers)) ∧ (∀ ap ∈ (authRun (SC16.step R h full) claim16 SC16.init ops).approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .approve c ap.n ap.d ap.target ap.slot ∧ c = ap.approver ∧ c ∈ R.approvers))
~~~

### 761. forged16_deploys_without_auth

Source: ControlStack/Scenarios/AuthInstancesA.lean:76 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forged16_deploys_without_auth : (authRun (SC16.step R0 id full) (fun _ => none) SC16.init forged16).deployed = [⟨0, 5, 7⟩] ∧ (authRun (SC16.step R0 id full) claim16 SC16.init forged16).deployed = []
~~~

### 762. sc25_verdict_step

Source: ControlStack/Scenarios/AuthInstancesA.lean:99 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc25_verdict_step (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : SC25.St) (o : SC25.Op) (x : Verdict) (hx : x ∈ (SC25.step R h cls full s o).verdicts) : x ∈ s.verdicts ∨ ∃ c, claim25 o = some c ∧ (o = .audit c x.id x.pass ∧ x.by_ = some c ∧ c ∈ R.auditors)
~~~

### 763. sc25_appr_step

Source: ControlStack/Scenarios/AuthInstancesA.lean:105 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc25_appr_step (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : SC25.St) (o : SC25.Op) (x : SC25.Appr) (hx : x ∈ (SC25.step R h cls full s o).approvals) : x ∈ s.approvals ∨ ∃ c, claim25 o = some c ∧ (o = .approve c x.id ∧ c = x.approver ∧ c ∈ R.approvers)
~~~

### 764. sc25_safe_authenticated

Source: ControlStack/Scenarios/AuthInstancesA.lean:112 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc25_safe_authenticated (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (U : List ℕ) (ops : List (ℕ × SC25.Op)) (hUv : ∀ u ∈ U, u ∉ R.auditors) (hUa : ∀ u ∈ U, u ∉ R.approvers) : Good R h cls (authRun (SC25.step R h cls full) claim25 SC25.init ops) ∧ (∀ v ∈ (authRun (SC25.step R h cls full) claim25 SC25.init ops).verdicts, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .audit c v.id v.pass ∧ v.by_ = some c ∧ c ∈ R.auditors)) ∧ (∀ ap ∈ (authRun (SC25.step R h cls full) claim25 SC25.init ops).approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .approve c ap.id ∧ c = ap.approver ∧ c ∈ R.approvers))
~~~

### 765. forged25_executes_without_auth

Source: ControlStack/Scenarios/AuthInstancesA.lean:130 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forged25_executes_without_auth : ((authRun (SC25.step R0 id cls0 full) (fun _ => none) SC25.init forged25).executed.map Exec.id) = [0] ∧ (authRun (SC25.step R0 id cls0 full) claim25 SC25.init forged25).executed = []
~~~

### 766. sc28_lease_step

Source: ControlStack/Scenarios/AuthInstancesA.lean:152 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc28_lease_step (admins : List ℕ) (G : ℕ) (s : SC28.St) (o : SC28.Op) (x : ℕ × ℕ) (hx : x ∈ (SC28.step admins G full s o).leases) : x ∈ s.leases ∨ ∃ c, claim28 o = some c ∧ (o = .issue c x.1 x.2 ∧ c ∈ admins)
~~~

### 767. sc28_revoke_step

Source: ControlStack/Scenarios/AuthInstancesA.lean:159 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc28_revoke_step (admins : List ℕ) (G : ℕ) (s : SC28.St) (o : SC28.Op) (x : ℕ) (hx : x ∈ (SC28.step admins G full s o).revoked) : x ∈ s.revoked ∨ ∃ c, claim28 o = some c ∧ (o = .revoke c x ∧ c ∈ admins)
~~~

### 768. sc28_safe_authenticated

Source: ControlStack/Scenarios/AuthInstancesA.lean:166 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc28_safe_authenticated (admins : List ℕ) (G : ℕ) (U : List ℕ) (ops : List (ℕ × SC28.Op)) (hU : ∀ u ∈ U, u ∉ admins) (hlegal : ∀ io ∈ ops, SC28.legal io.2) : Good G (authRun (SC28.step admins G full) claim28 SC28.init ops) ∧ (∀ l ∈ (authRun (SC28.step admins G full) claim28 SC28.init ops).leases, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .issue c l.1 l.2 ∧ c ∈ admins)) ∧ (∀ l ∈ (authRun (SC28.step admins G full) claim28 SC28.init ops).revoked, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .revoke c l ∧ c ∈ admins))
~~~

### 769. forged28_consumes_without_auth

Source: ControlStack/Scenarios/AuthInstancesA.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forged28_consumes_without_auth : (authRun (SC28.step [9] 1000 full) (fun _ => none) SC28.init forged28).usage = [(1, 0, 5)] ∧ (authRun (SC28.step [9] 1000 full) claim28 SC28.init forged28).usage = []
~~~

### 770. sc17_appr_step

Source: ControlStack/Scenarios/AuthInstancesA.lean:208 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc17_appr_step (E : Env) (s : SC17.St) (o : SC17.Op) (x : Ap) (hx : x ∈ (SC17.step E full s o).approvals) : x ∈ s.approvals ∨ ∃ c, claim17 o = some c ∧ (o = .approve c x.id ∧ c = x.reviewer ∧ c ∈ E.reviewers)
~~~

### 771. sc17_prop_step

Source: ControlStack/Scenarios/AuthInstancesA.lean:214 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc17_prop_step (E : Env) (s : SC17.St) (o : SC17.Op) (x : Pr) (hx : x ∈ (SC17.step E full s o).props) : x ∈ s.props ∨ ∃ c, claim17 o = some c ∧ (c = x.author ∧ (o = .propose c x.id x.diff ∨ o = .amend c x.id x.diff))
~~~

### 772. sc17_safe_authenticated

Source: ControlStack/Scenarios/AuthInstancesA.lean:222 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc17_safe_authenticated (E : Env) (g0 : List SC17.G) (U : List ℕ) (ops : List (ℕ × SC17.Op)) (hU : ∀ u ∈ U, u ∉ E.reviewers) : Good E (authRun (SC17.step E full) claim17 (SC17.init g0) ops) ∧ (∀ a ∈ (authRun (SC17.step E full) claim17 (SC17.init g0) ops).approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .approve c a.id ∧ c = a.reviewer ∧ c ∈ E.reviewers)) ∧ (∀ p ∈ (authRun (SC17.step E full) claim17 (SC17.init g0) ops).props, ∃ c o, (c, o) ∈ ops ∧ (c = p.author ∧ (o = .propose c p.id p.diff ∨ o = .amend c p.id p.diff)))
~~~

### 773. forged17_applies_without_auth

Source: ControlStack/Scenarios/AuthInstancesA.lean:239 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forged17_applies_without_auth : (authRun (SC17.step E0 full) (fun _ => none) (SC17.init []) forged17).live = [(1, 1, 1)] ∧ (authRun (SC17.step E0 full) claim17 (SC17.init []) forged17).applied = []
~~~

### 774. sc19_appr_step

Source: ControlStack/Scenarios/AuthInstancesA.lean:260 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc19_appr_step (E : Env) (s : SC19.St) (o : SC19.Op) (x : ℕ × ℕ × ℕ) (hx : x ∈ (SC19.step E full s o).approvals) : x ∈ s.approvals ∨ ∃ c, claim19 o = some c ∧ (o = .approve c x.1 ∧ c = x.2.1 ∧ c ∈ E.approvers)
~~~

### 775. sc19_verify_step

Source: ControlStack/Scenarios/AuthInstancesA.lean:266 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc19_verify_step (E : Env) (s : SC19.St) (o : SC19.Op) (x : ℕ) (hx : x ∈ (SC19.step E full s o).verified) : x ∈ s.verified ∨ ∃ c, claim19 o = some c ∧ (o = .verify c x ∧ c ∈ E.verifiers)
~~~

### 776. sc19_safe_authenticated

Source: ControlStack/Scenarios/AuthInstancesA.lean:273 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc19_safe_authenticated (E : Env) (U : List ℕ) (ops : List (ℕ × SC19.Op)) (hUa : ∀ u ∈ U, u ∉ E.approvers) (hUv : ∀ u ∈ U, u ∉ E.verifiers) : Good E (authRun (SC19.step E full) claim19 SC19.init ops) ∧ (∀ a ∈ (authRun (SC19.step E full) claim19 SC19.init ops).approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .approve c a.1 ∧ c = a.2.1 ∧ c ∈ E.approvers)) ∧ (∀ i ∈ (authRun (SC19.step E full) claim19 SC19.init ops).verified, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .verify c i ∧ c ∈ E.verifiers))
~~~

### 777. forged19_destroys_without_auth

Source: ControlStack/Scenarios/AuthInstancesA.lean:292 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forged19_destroys_without_auth : (authRun (SC19.step E0 full) (fun _ => none) SC19.init forged19).destroyed = [⟨0, 1, 7, 1, 5, 0⟩] ∧ (authRun (SC19.step E0 full) claim19 SC19.init forged19).destroyed = []
~~~

## ControlStack/Scenarios/AuthInstancesB.lean

### 778. roleOk_mem

Source: ControlStack/Scenarios/AuthInstancesB.lean:36 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem roleOk_mem (E : Env) (sec : Bool) (r : ℕ) (h : roleOk E sec r = true) : r ∈ E.reviewers ++ E.security
~~~

### 779. sc15_review_step

Source: ControlStack/Scenarios/AuthInstancesB.lean:40 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc15_review_step (E : Env) (s : SC15.St) (o : SC15.Op) (x : Rev) (hx : x ∈ (SC15.step E full s o).reviews) : x ∈ s.reviews ∨ ∃ c, claim15 o = some c ∧ (o = .review c x.id x.sec ∧ c = x.reviewer ∧ roleOk E x.sec c = true)
~~~

### 780. sc15_safe_authenticated

Source: ControlStack/Scenarios/AuthInstancesB.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc15_safe_authenticated (E : Env) (U : List ℕ) (ops : List (ℕ × SC15.Op)) (hU : ∀ u ∈ U, u ∉ E.reviewers ++ E.security) : (∀ c ∈ (authRun (SC15.step E full) claim15 SC15.init ops).merged, MergeOk E (authRun (SC15.step E full) claim15 SC15.init ops) c) ∧ (∀ r ∈ (authRun (SC15.step E full) claim15 SC15.init ops).reviews, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .review c r.id r.sec ∧ c = r.reviewer ∧ roleOk E r.sec c = true))
~~~

### 781. forged15_merges_without_auth

Source: ControlStack/Scenarios/AuthInstancesB.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forged15_merges_without_auth : (authRun (SC15.step E0 full) (fun _ => none) SC15.init forged15).merged = [⟨0, 1, 7, [5], [5]⟩] ∧ (authRun (SC15.step E0 full) claim15 SC15.init forged15).merged = []
~~~

### 782. sc20_promote_step

Source: ControlStack/Scenarios/AuthInstancesB.lean:85 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc20_promote_step (E : Env) (s : SC20.St) (o : SC20.Op) (x : ℕ × ℕ × ℕ) (hx : x ∈ (SC20.step E full s o).promoted) : x ∈ s.promoted ∨ ∃ c, claim20 o = some c ∧ (o = .promote c x.1 ∧ c = x.2.1 ∧ c ∈ E.reviewers)
~~~

### 783. sc20_safe_authenticated

Source: ControlStack/Scenarios/AuthInstancesB.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc20_safe_authenticated (E : Env) (U : List ℕ) (ops : List (ℕ × SC20.Op)) (hU : ∀ u ∈ U, u ∉ E.reviewers) : Good E (authRun (SC20.step E full) claim20 SC20.init ops) ∧ (∀ p ∈ (authRun (SC20.step E full) claim20 SC20.init ops).promoted, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .promote c p.1 ∧ c = p.2.1 ∧ c ∈ E.reviewers))
~~~

### 784. forged20_trains_without_auth

Source: ControlStack/Scenarios/AuthInstancesB.lean:105 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forged20_trains_without_auth : (authRun (SC20.step E0 full) (fun _ => none) SC20.init forged20).trained = [[(1, 66)]] ∧ (authRun (SC20.step E0 full) claim20 SC20.init forged20).trained = []
~~~

### 785. sc23_conf_step

Source: ControlStack/Scenarios/AuthInstancesB.lean:125 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc23_conf_step (P : Policy) (s : SC23.St) (o : SC23.Op) (x : Conf) (hx : x ∈ (SC23.step P full s o).confs) : x ∈ s.confs ∨ ∃ c, claim23 o = some c ∧ (o = .confirm c x.n x.tool x.vals ∧ c = x.by_ ∧ c ∈ P.users)
~~~

### 786. sc23_safe_authenticated

Source: ControlStack/Scenarios/AuthInstancesB.lean:132 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc23_safe_authenticated (P : Policy) (U : List ℕ) (ops : List (ℕ × SC23.Op)) (hU : ∀ u ∈ U, u ∉ P.users) : Good P (authRun (SC23.step P full) claim23 SC23.init ops) ∧ (∀ cf ∈ (authRun (SC23.step P full) claim23 SC23.init ops).confs, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .confirm c cf.n cf.tool cf.vals ∧ c = cf.by_ ∧ c ∈ P.users))
~~~

### 787. forged23_acts_without_auth

Source: ControlStack/Scenarios/AuthInstancesB.lean:145 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forged23_acts_without_auth : (authRun (SC23.step P0 full) (fun _ => none) SC23.init forged23).executed = [⟨5, [66], true, some 7⟩] ∧ (authRun (SC23.step P0 full) claim23 SC23.init forged23).executed = []
~~~

### 788. sc12_active_step

Source: ControlStack/Scenarios/AuthInstancesB.lean:165 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc12_active_step (admins : List ℕ) (s : SC12.St) (o : SC12.Op) (x : ℕ) (hx : x ∈ (SC12.step admins full s o).active) : x ∈ s.active ∨ ∃ c, claim12 o = some c ∧ (o = .start c x ∧ c ∈ admins)
~~~

### 789. sc12_safe_authenticated

Source: ControlStack/Scenarios/AuthInstancesB.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc12_safe_authenticated (admins : List ℕ) (U : List ℕ) (ops : List (ℕ × SC12.Op)) (hU : ∀ u ∈ U, u ∉ admins) : Good (authRun (SC12.step admins full) claim12 SC12.init ops) ∧ (∀ e ∈ (authRun (SC12.step admins full) claim12 SC12.init ops).live, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .start c e.origin ∧ c ∈ admins))
~~~

### 790. forged12_spawns_without_auth

Source: ControlStack/Scenarios/AuthInstancesB.lean:188 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forged12_spawns_without_auth : (authRun (SC12.step [9] full) (fun _ => none) SC12.init forged12).live.length = 2 ∧ (authRun (SC12.step [9] full) claim12 SC12.init forged12).live = []
~~~

### 791. sc18_safe_authenticated

Source: ControlStack/Scenarios/AuthInstancesB.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc18_safe_authenticated (admins : List ℕ) (trusted T : ℕ) (U : List ℕ) (ops : List (ℕ × SC18.Op)) (hU : ∀ u ∈ U, u ∉ admins) (htrusted : ∀ io ∈ ops, io.1 ∉ U → SC18.legal admins trusted io.2) : Good T (authRun (SC18.step admins trusted T full) claim18 (SC18.init trusted) ops)
~~~

### 792. forged18_redirects_without_auth

Source: ControlStack/Scenarios/AuthInstancesB.lean:228 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forged18_redirects_without_auth : (authRun (SC18.step [9] 0 5 full) (fun _ => none) (SC18.init 0) forged18).cfg = 66 ∧ (authRun (SC18.step [9] 0 5 full) claim18 (SC18.init 0) forged18).cfg = 0
~~~

## ControlStack/Scenarios/EvalIntegrity.lean

### 793. run_cons

Source: ControlStack/Scenarios/EvalIntegrity.lean:101 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 794. inv_init

Source: ControlStack/Scenarios/EvalIntegrity.lean:115 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) : Inv E init
~~~

### 795. resultOf_none

Source: ControlStack/Scenarios/EvalIntegrity.lean:117 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem resultOf_none {s : St} {t : ℕ} (h : resultOf s t = none) : ∀ e ∈ s.results, e.1 ≠ t
~~~

### 796. resultOf_some

Source: ControlStack/Scenarios/EvalIntegrity.lean:122 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem resultOf_some {s : St} {t : ℕ} (h : (s.results.map Prod.fst).Nodup) {e : Res} (he : e ∈ s.results) (ht : e.1 = t) : resultOf s t = some e
~~~

### 797. step_inv

Source: ControlStack/Scenarios/EvalIntegrity.lean:132 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o)
~~~

### 798. run_inv

Source: ControlStack/Scenarios/EvalIntegrity.lean:210 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 799. sc21_safe

Source: ControlStack/Scenarios/EvalIntegrity.lean:218 | Family: F4 | Adversary: NON_ADAPTIVE | Status: PROVED_RECORDED

~~~lean
theorem sc21_safe (E : Env) (ops : List Op) : ∀ p ∈ (run E full init ops).published, PubOk E p
~~~

### 800. step_halted

Source: ControlStack/Scenarios/EvalIntegrity.lean:221 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s
~~~

### 801. halt_freezes

Source: ControlStack/Scenarios/EvalIntegrity.lean:231 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
~~~

### 802. published_prefix

Source: ControlStack/Scenarios/EvalIntegrity.lean:236 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem published_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.published <+: (step E C s o).published
~~~

### 803. honest_publish

Source: ControlStack/Scenarios/EvalIntegrity.lean:265 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_publish : (run E0 full init [.report 0 1 5, .report 1 0 5, .reexec 1, .publish]).published = [([(1, 0, 5), (0, 1, 5)], [1])]
~~~

### 804. suppression_breaks

Source: ControlStack/Scenarios/EvalIntegrity.lean:270 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem suppression_breaks : (run E0 { full with complete
~~~

### 805. modified_evaluator_breaks

Source: ControlStack/Scenarios/EvalIntegrity.lean:276 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem modified_evaluator_breaks : (run E0 { full with frozenEval
~~~

### 806. overwrite_after_check_breaks

Source: ControlStack/Scenarios/EvalIntegrity.lean:283 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem overwrite_after_check_breaks : (run E0 { full with appendOnly
~~~

### 807. undetected_iff_disjoint

Source: ControlStack/Scenarios/EvalIntegrity.lean:299 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem undetected_iff_disjoint (rep truth : Fin N → ℕ) (S : Finset (Fin N)) : S.filter (fun i => rep i ≠ truth i) = ∅ ↔ Disjoint S (corrupt rep truth)
~~~

### 808. survival_is_unflagged_fraction

Source: ControlStack/Scenarios/EvalIntegrity.lean:304 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_is_unflagged_fraction (rep truth : Fin N → ℕ) (B : ℕ) : survival (randomSchedules N B) (corrupt rep truth) = (((randomSchedules N B).filter (fun S => S.filter (fun i => rep i ≠ truth i) = ∅)).card : ℝ) / ((randomSchedules N B).card : ℝ)
~~~

### 809. sc21_undetected_prob

Source: ControlStack/Scenarios/EvalIntegrity.lean:314 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc21_undetected_prob (rep truth : Fin N → ℕ) {B k : ℕ} (hk : (corrupt rep truth).card = k) : survival (randomSchedules N B) (corrupt rep truth) = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

### 810. sc21_undetected_le_pow

Source: ControlStack/Scenarios/EvalIntegrity.lean:318 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc21_undetected_le_pow (rep truth : Fin N → ℕ) {B k : ℕ} (hN : 0 < N) (hB : B ≤ N) (hk : (corrupt rep truth).card = k) : survival (randomSchedules N B) (corrupt rep truth) ≤ (((N : ℝ) - B) / N) ^ k
~~~

### 811. sc21_example

Source: ControlStack/Scenarios/EvalIntegrity.lean:324 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc21_example (rep truth : Fin 100 → ℕ) (hk : (corrupt rep truth).card = 5) : survival (randomSchedules 100 10) (corrupt rep truth) ≤ 0.59049
~~~

### 812. observable_sample_nogo

Source: ControlStack/Scenarios/EvalIntegrity.lean:330 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem observable_sample_nogo {B k : ℕ} (S : Finset (Fin N)) (hS : S.card = B) (hk : k ≤ N - B) : ∃ A : Finset (Fin N), A.card = k ∧ Disjoint S A ∧ survival {S} A = 1
~~~

### 813. sc22_unreplicated_misreport

Source: ControlStack/Scenarios/EvalIntegrity.lean:337 | Family: F6 | Adversary: NON_ADAPTIVE | Status: PROVED_RECORDED

~~~lean
theorem sc22_unreplicated_misreport (rep truth : Fin N → ℕ) {B k : ℕ} (hk : (corrupt rep truth).card = k) : survival (randomSchedules N B) (corrupt rep truth) = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

## ControlStack/Scenarios/EvalIntegrityAdaptive.lean

### 814. sc21_adaptive

Source: ControlStack/Scenarios/EvalIntegrityAdaptive.lean:47 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc21_adaptive (k B : ℕ) (hB : B ≤ N) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (hiddenK σ S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

### 815. sc21_adaptive_content

Source: ControlStack/Scenarios/EvalIntegrityAdaptive.lean:55 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc21_adaptive_content {Y : Type} [Fintype Y] (k B : ℕ) (hB : B ≤ N) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1) (hmarg : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h (a : Bool), ∑ y, ∑ c : Bool, K S h (y, (a, (), c)) ≤ σ (h.map Prod.snd) a) : ∑ S : Finset (Fin N), pU N B S * val (K S) (successInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

### 816. sc21_adaptive_recall

Source: ControlStack/Scenarios/EvalIntegrityAdaptive.lean:68 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc21_adaptive_recall {Y : Type} [Fintype Y] (k B : ℕ) (hB : B ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1) (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) : ∑ S : Finset (Fin N), pU N B S * val (K S) (recallSucc (N
~~~

### 817. sc21_adaptive_example

Source: ControlStack/Scenarios/EvalIntegrityAdaptive.lean:81 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc21_adaptive_example (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) : ∑ S : Finset (Fin 100), (if S ∈ AuditBudget.randomSchedules 100 10 then (Nat.choose 100 10 : ℝ)⁻¹ else 0) * val (hiddenK σ S) (survInd 5 S) 100 [] ≤ (10104934117421 : ℝ) / 17310309456440
~~~

### 818. leaked_sample_survives

Source: ControlStack/Scenarios/EvalIntegrityAdaptive.lean:90 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem leaked_sample_survives {B k : ℕ} (S : Finset (Fin N)) (hS : S.card = B) (hk : k ≤ N - B) : ∃ A : Finset (Fin N), A.card = k ∧ Disjoint S A ∧ AuditBudget.survival {S} A = 1
~~~

## ControlStack/Scenarios/LabStack.lean

### 819. labInv_init

Source: ControlStack/Scenarios/LabStack.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem labInv_init (P : LabParams) : LabInv P labInit
~~~

### 820. payStep_inv

Source: ControlStack/Scenarios/LabStack.lean:159 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem payStep_inv (P : LabParams) (share : Bool) (s : LabSt) (p : SC26.St) (h : LabInv P s) (hp : SC26.Inv P.R26 P.cap26 p) : LabInv P (payStep P share s p)
~~~

### 821. compStep_inv

Source: ControlStack/Scenarios/LabStack.lean:170 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem compStep_inv (P : LabParams) (share : Bool) (s : LabSt) (c : SC28.St) (h : LabInv P s) (hc : SC28.Inv P.G28 c) : LabInv P (compStep P share s c)
~~~

### 822. deputyOp_legal

Source: ControlStack/Scenarios/LabStack.lean:186 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deputyOp_legal (P : LabParams) (d : SC16.St) (n : ℕ) : SC26.legal P.R26 (deputyOp P d n)
~~~

### 823. labStep_inv

Source: ControlStack/Scenarios/LabStack.lean:191 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem labStep_inv (P : LabParams) (share : Bool) (s : LabSt) (o : LabOp) (ho : labLegal P o) (h : LabInv P s) : LabInv P (labStep P share s o)
~~~

### 824. labRun_inv

Source: ControlStack/Scenarios/LabStack.lean:220 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem labRun_inv (P : LabParams) (share : Bool) (s : LabSt) (ops : List LabOp) (hops : ∀ o ∈ ops, labLegal P o) (h : LabInv P s) : LabInv P (labRun P share s ops)
~~~

### 825. bank_le_spent

Source: ControlStack/Scenarios/LabStack.lean:228 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bank_le_spent {R : SC26.Roles} {cap : ℕ} {s : SC26.St} (h : SC26.Inv R cap s) : (s.bank.map (fun e => e.2.amount)).sum ≤ s.spent
~~~

### 826. global_budget

Source: ControlStack/Scenarios/LabStack.lean:239 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem global_budget (P : LabParams) (s : LabSt) (h : LabInv P s) : (s.pay.bank.map (fun e => e.2.amount)).sum + P.price * SC28.usedT s.comp ≤ P.G
~~~

### 827. payStep_cases

Source: ControlStack/Scenarios/LabStack.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem payStep_cases (P : LabParams) (share : Bool) (s : LabSt) (p : SC26.St) : payStep P share s p = s ∨ ((payStep P share s p).pay = p ∧ (payStep P share s p).dep = s.dep ∧ (payStep P share s p).comp = s.comp)
~~~

### 828. compStep_cases

Source: ControlStack/Scenarios/LabStack.lean:258 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem compStep_cases (P : LabParams) (share : Bool) (s : LabSt) (c : SC28.St) : compStep P share s c = s ∨ ((compStep P share s c).comp = c ∧ (compStep P share s c).dep = s.dep ∧ (compStep P share s c).pay = s.pay)
~~~

### 829. labStep_parts

Source: ControlStack/Scenarios/LabStack.lean:266 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem labStep_parts (P : LabParams) (share : Bool) (s : LabSt) (o : LabOp) : let t
~~~

### 830. deputyOp_not_approve

Source: ControlStack/Scenarios/LabStack.lean:303 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deputyOp_not_approve (P : LabParams) (d : SC16.St) (n a k : ℕ) (tx : SC26.Tx) : deputyOp P d n ≠ .approve a k tx
~~~

### 831. pay_appr_step

Source: ControlStack/Scenarios/LabStack.lean:307 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pay_appr_step (P : LabParams) (share : Bool) (s : LabSt) (o : LabOp) (x : ℕ × ℕ × SC26.Tx) (hx : x ∈ (labStep P share s o).pay.approvals) : x ∈ s.pay.approvals ∨ ∃ c, labClaim o = some c ∧ (o = .pay (.approve c x.1 x.2.2) ∧ c = x.2.1)
~~~

### 832. dep_review_step

Source: ControlStack/Scenarios/LabStack.lean:321 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dep_review_step (P : LabParams) (share : Bool) (s : LabSt) (o : LabOp) (x : SC16.Review) (hx : x ∈ (labStep P share s o).dep.reviews) : x ∈ s.dep.reviews ∨ ∃ c, labClaim o = some c ∧ (o = .dep (.review c x.d) ∧ c = x.reviewer ∧ c ∈ P.R16.reviewers)
~~~

### 833. dep_appr_step

Source: ControlStack/Scenarios/LabStack.lean:331 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dep_appr_step (P : LabParams) (share : Bool) (s : LabSt) (o : LabOp) (x : SC16.Appr) (hx : x ∈ (labStep P share s o).dep.approvals) : x ∈ s.dep.approvals ∨ ∃ c, labClaim o = some c ∧ (o = .dep (.approve c x.n x.d x.target x.slot) ∧ c = x.approver ∧ c ∈ P.R16.approvers)
~~~

### 834. comp_lease_step

Source: ControlStack/Scenarios/LabStack.lean:342 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem comp_lease_step (P : LabParams) (share : Bool) (s : LabSt) (o : LabOp) (x : ℕ × ℕ) (hx : x ∈ (labStep P share s o).comp.leases) : x ∈ s.comp.leases ∨ ∃ c, labClaim o = some c ∧ (o = .comp (.issue c x.1 x.2) ∧ c ∈ P.admins28)
~~~

### 835. lab_safe

Source: ControlStack/Scenarios/LabStack.lean:354 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lab_safe (P : LabParams) (U : List ℕ) (ops : List (ℕ × LabOp)) (hlegal : ∀ io ∈ ops, labLegal P io.2) (hU26 : ∀ u ∈ U, u ∉ P.R26.approvers) (hU16r : ∀ u ∈ U, u ∉ P.R16.reviewers) (hU16a : ∀ u ∈ U, u ∉ P.R16.approvers) (hU28 : ∀ u ∈ U, u ∉ P.admins28) : SC26.Good P.R26 P.cap26 (authRun (labStep P true) labClaim labInit ops).pay ∧ SC16.Good P.R16 P.h (authRun (labStep P true) labClaim labInit ops).dep ∧ SC28.Good P.G28 (authRun (labStep P true) labClaim labInit ops).comp ∧ ((authRun (labStep P true) labClaim labInit ops).pay.bank.map (fun e => e.2.amount)).sum + P.price * SC28.usedT (authRun (labStep P true) labClaim labInit ops).comp ≤ P.G ∧ (∀ ap ∈ (authRun (labStep P true) labClaim labInit ops).pay.approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .pay (.approve c ap.1 ap.2.2) ∧ c = ap.2.1)) ∧ (∀ rv ∈ (authRun (labStep P true) labClaim labInit ops).dep.reviews, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .dep (.review c rv.d) ∧ c = rv.reviewer ∧ c ∈ P.R16.reviewers)) ∧ (∀ ap ∈ (authRun (labStep P true) labClaim labInit ops).dep.approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .dep (.approve c ap.n ap.d ap.target ap.slot) ∧ c = ap.approver ∧ c ∈ P.R16.approvers)) ∧ (∀ l ∈ (authRun (labStep P true) labClaim labInit ops).comp.leases, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .comp (.issue c l.1 l.2) ∧ c ∈ P.admins28))
~~~

### 836. arrive_step

Source: ControlStack/Scenarios/LabStack.lean:392 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem arrive_step (R : SC26.Roles) (cap : ℕ) (p : SC26.St) (k : ℕ) : (SC26.step R cap SC26.full p (.arrive k)).net = p.net ∧ (SC26.step R cap SC26.full p (.arrive k)).spent = p.spent ∧ ∀ e ∈ (SC26.step R cap SC26.full p (.arrive k)).bank, e ∈ p.bank ∨ e ∈ p.net
~~~

### 837. labStep_halted

Source: ControlStack/Scenarios/LabStack.lean:405 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem labStep_halted (P : LabParams) (s : LabSt) (o : LabOp) (hh : s.halted = true) : let t
~~~

### 838. lab_halt_freezes

Source: ControlStack/Scenarios/LabStack.lean:434 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lab_halt_freezes (P : LabParams) (s : LabSt) (ops : List LabOp) (hh : s.halted = true) : let t
~~~

### 839. component_halt_shared

Source: ControlStack/Scenarios/LabStack.lean:449 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem component_halt_shared (P : LabParams) (s : LabSt) (c : ℕ) (hh : s.halted = false) (hc : c ∈ P.R16.admins) : (labStep P true s (.dep (.halt c))).halted = true
~~~

### 840. deputy_admissible

Source: ControlStack/Scenarios/LabStack.lean:471 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deputy_admissible (P : LabParams) (n : ℕ) : Compose.BridgeAdmissible (spec16 P.R16 P.h) (SC26.spec P.R26 P.cap26) (deputyBridge P n)
~~~

### 841. separate_caps_exceed_global

Source: ControlStack/Scenarios/LabStack.lean:485 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem separate_caps_exceed_global : ((SC26.run SC26.R0 10 SC26.full SC26.init payOps).bank.map (fun e => e.2.amount)).sum + SC28.usedT (SC28.run [9] 10 SC28.full SC28.init compOps) = 20 ∧ ((labRun P0 true labInit (payOps.map .pay ++ compOps.map .comp)).pay.bank.map (fun e => e.2.amount)).sum = 10 ∧ (labRun P0 true labInit (payOps.map .pay ++ compOps.map .comp)).comp.usage = []
~~~

### 842. deputy_reuse_breaks_sc26

Source: ControlStack/Scenarios/LabStack.lean:501 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deputy_reuse_breaks_sc26 : let d
~~~

### 843. no_shared_halt_keeps_running

Source: ControlStack/Scenarios/LabStack.lean:516 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_shared_halt_keeps_running : (labRun P0 false labInit ([.dep (.halt 4)] ++ compOps.map .comp)).comp.usage = [(1, 0, 10)] ∧ (labRun P0 true labInit ([.dep (.halt 4)] ++ compOps.map .comp)).comp.usage = []
~~~

### 844. lab_ledger_eq

Source: ControlStack/Scenarios/LabStack.lean:569 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lab_ledger_eq (P : LabParams) (U : List ℕ) (ops : List (ℕ × LabOp)) : typedLedger (labStack P U ops).premises = labLedger
~~~

## ControlStack/Scenarios/RollbackInstances.lean

### 845. run_sys26

Source: ControlStack/Scenarios/RollbackInstances.lean:36 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_sys26 (R : SC26.Roles) (cap : ℕ) (l : List {o : SC26.Op // SC26.legal R o}) (s : SC26.St) : (SC26.sys R cap).run s l = SC26.run R cap SC26.full s (l.map Subtype.val)
~~~

### 846. sc26_rollback_safe

Source: ControlStack/Scenarios/RollbackInstances.lean:44 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc26_rollback_safe (R : SC26.Roles) (cap : ℕ) (ops : List (ROp {o : SC26.Op // SC26.legal R o})) : let t
~~~

### 847. sc26_rollback_without_anchor

Source: ControlStack/Scenarios/RollbackInstances.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc26_rollback_without_anchor : let t
~~~

### 848. payStep_bank

Source: ControlStack/Scenarios/RollbackInstances.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem payStep_bank (P : LabParams) (share : Bool) (s : LabSt) (p : SC26.St) (hp : s.pay.bank <+: p.bank) : s.pay.bank <+: (payStep P share s p).pay.bank
~~~

### 849. compStep_bank

Source: ControlStack/Scenarios/RollbackInstances.lean:93 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem compStep_bank (P : LabParams) (share : Bool) (s : LabSt) (c : SC28.St) : (compStep P share s c).pay.bank = s.pay.bank
~~~

### 850. lab_bank_prefix

Source: ControlStack/Scenarios/RollbackInstances.lean:98 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lab_bank_prefix (P : LabParams) (s : LabSt) (o : LabOp) : s.pay.bank <+: (labStep P true s o).pay.bank
~~~

### 851. run_lab

Source: ControlStack/Scenarios/RollbackInstances.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_lab (P : LabParams) (l : List {o : LabOp // labLegal P o}) (s : LabSt) : (labSys P).run s l = labRun P true s (l.map Subtype.val)
~~~

### 852. lab_rollback_safe

Source: ControlStack/Scenarios/RollbackInstances.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lab_rollback_safe (P : LabParams) (ops : List (ROp {o : LabOp // labLegal P o})) : let t
~~~

### 853. lab_rollback_reopens_budget

Source: ControlStack/Scenarios/RollbackInstances.lean:162 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lab_rollback_reopens_budget : let t
~~~

## ControlStack/Scenarios/SC05Signal.lean

### 854. cap_does_not_prevent

Source: ControlStack/Scenarios/SC05Signal.lean:33 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem cap_does_not_prevent : ∃ (enc : Bool → Fin 65536 → ℝ) (dec : Fin 65536 → Bool → ℝ), (∀ m, IsDist (enc m)) ∧ (∀ v, IsDist (dec v)) ∧ successView id enc dec = 1
~~~

### 855. zero_dependence_is_blind

Source: ControlStack/Scenarios/SC05Signal.lean:40 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem zero_dependence_is_blind {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V] (ρ : Ω → ℝ) (e : Ω → V → ℝ) (dec : Ω → V → M → ℝ) (hρ : IsDist ρ) (he : ∀ ω, IsDist (e ω)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ (fun ω _ => e ω) dec = (Fintype.card M : ℝ)⁻¹
~~~

### 856. forbidden_never_executes

Source: ControlStack/Scenarios/SC05Signal.lean:89 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forbidden_never_executes (forbidden : List ℕ) (ops : List Op) : ∀ a ∈ (sys forbidden).run [] ops, a ∉ forbidden
~~~

### 857. forbidden_executes_without_gate

Source: ControlStack/Scenarios/SC05Signal.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forbidden_executes_without_gate : (([Op.act 7].foldl (step [7] false) []) = [7]) ∧ (([Op.act 7].foldl (step [7] true) []) = [])
~~~

## ControlStack/Scenarios/SC06Artifacts.lean

### 858. run_cons

Source: ControlStack/Scenarios/SC06Artifacts.lean:141 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (P : Policy) (C : Checks) (s : St) (o : Op) (ops : List Op) : run P C s (o :: ops) = run P C (step P C s o) ops
~~~

### 859. inv_init

Source: ControlStack/Scenarios/SC06Artifacts.lean:159 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (P : Policy) : Inv P init
~~~

### 860. ActOk.mono

Source: ControlStack/Scenarios/SC06Artifacts.lean:161 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ActOk.mono {P : Policy} {s t : St} (h : s.confs ⊆ t.confs) {x : Act} (hx : ActOk P s x) : ActOk P t x
~~~

### 861. exec_append

Source: ControlStack/Scenarios/SC06Artifacts.lean:166 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exec_append {P : Policy} {s : St} (h : Inv P s) (x : Act) (hx : ActOk P s x) : Inv P { s with executed
~~~

### 862. step_inv

Source: ControlStack/Scenarios/SC06Artifacts.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (P : Policy) (s : St) (o : Op) (h : Inv P s) : Inv P (step P full s o)
~~~

### 863. run_inv

Source: ControlStack/Scenarios/SC06Artifacts.lean:234 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (P : Policy) (s : St) (ops : List Op) (h : Inv P s) : Inv P (run P full s ops)
~~~

### 864. sc06_safe

Source: ControlStack/Scenarios/SC06Artifacts.lean:242 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc06_safe (P : Policy) (ops : List Op) : Good P (run P full init ops)
~~~

### 865. step_halted

Source: ControlStack/Scenarios/SC06Artifacts.lean:248 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (P : Policy) (s : St) (o : Op) (hh : s.halted = true) : step P full s o = s
~~~

### 866. halt_freezes

Source: ControlStack/Scenarios/SC06Artifacts.lean:258 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (P : Policy) (s : St) (ops : List Op) (hh : s.halted = true) : run P full s ops = s
~~~

### 867. executed_prefix

Source: ControlStack/Scenarios/SC06Artifacts.lean:265 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem executed_prefix (P : Policy) (C : Checks) (s : St) (o : Op) : s.executed <+: (step P C s o).executed
~~~

### 868. honest_shared_work

Source: ControlStack/Scenarios/SC06Artifacts.lean:294 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_shared_work : (run P0 full init [.writeTyped 1 0 42 99, .read 2 0, .confirm 5 3 2 7 42, .act 2 7 42 3]).executed = [⟨2, 7, 42, true, some 3⟩]
~~~

### 869. raw_path_breaks

Source: ControlStack/Scenarios/SC06Artifacts.lean:300 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem raw_path_breaks : ((run P0 { full with singlePath
~~~

### 870. no_canonicalisation_breaks

Source: ControlStack/Scenarios/SC06Artifacts.lean:307 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_canonicalisation_breaks : ((run P0 { full with canon
~~~

### 871. no_provenance_check_breaks

Source: ControlStack/Scenarios/SC06Artifacts.lean:313 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_provenance_check_breaks : (run P0 { full with provCheck
~~~

### 872. no_halt_check_breaks

Source: ControlStack/Scenarios/SC06Artifacts.lean:320 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run P0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC06ConfirmationReuse.lean

### 873. same_confirmation_can_authorize_two_effects

Source: ControlStack/Scenarios/SC06ConfirmationReuse.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem same_confirmation_can_authorize_two_effects : let s
~~~

### 874. missing_confirmation_blocks_both

Source: ControlStack/Scenarios/SC06ConfirmationReuse.lean:40 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem missing_confirmation_blocks_both : (run P0 full init [ .writeTyped 1 0 42 99, .read 2 0, .act 2 7 42 3, .act 2 7 42 3 ]).executed = []
~~~

### 875. same_value_different_provenance_is_ambiguous

Source: ControlStack/Scenarios/SC06ConfirmationReuse.lean:62 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem same_value_different_provenance_is_ambiguous : let s
~~~

## ControlStack/Scenarios/SC06OneUse.lean

### 876. inv_init

Source: ControlStack/Scenarios/SC06OneUse.lean:122 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (R : Roles) : Inv R init
~~~

### 877. EffectOk.monoEntries

Source: ControlStack/Scenarios/SC06OneUse.lean:125 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem EffectOk.monoEntries {R : Roles} {s : State} (x : Effect) (e : Entry) (h : EffectOk R s x) : EffectOk R {s with entries
~~~

### 878. EffectOk.monoConfirmations

Source: ControlStack/Scenarios/SC06OneUse.lean:131 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem EffectOk.monoConfirmations {R : Roles} {s : State} (x : Effect) (c : Confirmation) (h : EffectOk R s x) : EffectOk R {s with confirmations
~~~

### 879. addEntry

Source: ControlStack/Scenarios/SC06OneUse.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem addEntry (R : Roles) (s : State) (h : Inv R s) (e : Entry) : Inv R {s with entries
~~~

### 880. addConfirmation

Source: ControlStack/Scenarios/SC06OneUse.lean:143 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem addConfirmation (R : Roles) (s : State) (h : Inv R s) (c : Confirmation) (hc : c.issuer ∈ R.users) : Inv R {s with confirmations
~~~

### 881. addEffect

Source: ControlStack/Scenarios/SC06OneUse.lean:154 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem addEffect (R : Roles) (s : State) (h : Inv R s) (x : Effect) (hx : EffectOk R s x) (hu : x.confId ∉ s.effects.map Effect.confId) : Inv R {s with effects
~~~

### 882. step_inv

Source: ControlStack/Scenarios/SC06OneUse.lean:165 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (R : Roles) (s : State) (op : Event) (h : Inv R s) : Inv R (step R s op)
~~~

### 883. run_inv

Source: ControlStack/Scenarios/SC06OneUse.lean:205 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (R : Roles) (s : State) (es : List Event) (h : Inv R s) : Inv R (run R s es)
~~~

### 884. scoped_safe

Source: ControlStack/Scenarios/SC06OneUse.lean:215 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem scoped_safe (R : Roles) (es : List Event) : (∀ x ∈ (run R init es).effects, EffectOk R (run R init es) x) ∧ ((run R init es).effects.map Effect.confId).Nodup
~~~

### 885. duplicate_use_blocked

Source: ControlStack/Scenarios/SC06OneUse.lean:224 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem duplicate_use_blocked : (run R0 init [ .ingest 2 1 42, .confirm 5 3 2 7 0 42, .act 2 7 0 3, .act 2 7 0 3]).effects = [⟨3, 2, 7, 0, 42⟩]
~~~

### 886. provenance_handle_not_value_alias

Source: ControlStack/Scenarios/SC06OneUse.lean:235 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem provenance_handle_not_value_alias : (run R0 init [ .ingest 2 2 42, .ingest 2 1 42, .confirm 5 3 2 7 0 42, .act 2 7 1 3]).effects = []
~~~

### 887. useful_foreign_action

Source: ControlStack/Scenarios/SC06OneUse.lean:245 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem useful_foreign_action : (run R0 init [ .ingest 2 2 42, .ingest 2 1 42, .confirm 5 3 2 7 1 42, .act 2 7 1 3]).effects = [⟨3, 2, 7, 1, 42⟩]
~~~

### 888. disabling_consumption_duplicates_effect

Source: ControlStack/Scenarios/SC06OneUse.lean:278 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem disabling_consumption_duplicates_effect : (weakRun R0 init [ .ingest 2 1 42, .confirm 5 3 2 7 0 42, .act 2 7 0 3, .act 2 7 0 3]).effects = [⟨3, 2, 7, 0, 42⟩, ⟨3, 2, 7, 0, 42⟩] ∧ (run R0 init [ .ingest 2 1 42, .confirm 5 3 2 7 0 42, .act 2 7 0 3, .act 2 7 0 3]).effects = [⟨3, 2, 7, 0, 42⟩]
~~~

### 889. distinct_confirmations_allow_two_effects

Source: ControlStack/Scenarios/SC06OneUse.lean:295 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem distinct_confirmations_allow_two_effects : (run R0 init [ .ingest 2 1 42, .confirm 5 3 2 7 0 42, .confirm 5 4 2 7 0 42, .act 2 7 0 3, .act 2 7 0 4]).effects = [⟨4, 2, 7, 0, 42⟩, ⟨3, 2, 7, 0, 42⟩]
~~~

### 890. halt_stops_foreign_action

Source: ControlStack/Scenarios/SC06OneUse.lean:306 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_stops_foreign_action : (run R0 init [ .ingest 2 1 42, .confirm 5 3 2 7 0 42, .halt 9, .act 2 7 0 3]).effects = []
~~~

## ControlStack/Scenarios/SC07Exfil.lean

### 891. capped_le

Source: ControlStack/Scenarios/SC07Exfil.lean:68 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capped_le (q : ℕ) (b : List ℕ) : ∀ x ∈ capped q b, x ≤ q
~~~

### 892. sum_le_traffic

Source: ControlStack/Scenarios/SC07Exfil.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_le_traffic (q : ℕ) (b : List ℕ) (hb : ∀ x ∈ b, x ≤ q) : b.sum ≤ q * traffic b
~~~

### 893. ceilDiv_le

Source: ControlStack/Scenarios/SC07Exfil.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ceilDiv_le (S q m : ℕ) (hq : 0 < q) (h : S ≤ q * m) : ceilDiv S q ≤ m
~~~

### 894. windows_needed

Source: ControlStack/Scenarios/SC07Exfil.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem windows_needed (S q : ℕ) (hq : 0 < q) (b : List ℕ) (hb : ∀ x ∈ b, x ≤ q) (hS : S ≤ b.sum) : ceilDiv S q ≤ traffic b
~~~

### 895. survive_nonneg

Source: ControlStack/Scenarios/SC07Exfil.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survive_nonneg (c : ℕ → ℝ) (hc : ∀ i, c i ≤ 1) (b : List ℕ) (i : ℕ) : 0 ≤ survive c b i
~~~

### 896. survive_le

Source: ControlStack/Scenarios/SC07Exfil.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survive_le (c : ℕ → ℝ) (pr : ℝ) (hc : ∀ i, pr ≤ c i ∧ c i ≤ 1) (hpr : pr ≤ 1) (b : List ℕ) (i : ℕ) : survive c b i ≤ (1 - pr) ^ traffic b
~~~

### 897. sc07_plan_bound

Source: ControlStack/Scenarios/SC07Exfil.lean:130 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc07_plan_bound (S q : ℕ) (hq : 0 < q) (c : ℕ → ℝ) (pr : ℝ) (hc : ∀ i, pr ≤ c i ∧ c i ≤ 1) (hpr0 : 0 ≤ pr) (hpr : pr ≤ 1) (b : List ℕ) (hS : S ≤ (capped q b).sum) : survive c (capped q b) 0 ≤ (1 - pr) ^ ceilDiv S q
~~~

### 898. sc07_mixed

Source: ControlStack/Scenarios/SC07Exfil.lean:139 | Family: F1 | Adversary: NON_ADAPTIVE | Status: PROVED_RECORDED

~~~lean
theorem sc07_mixed {Ω : Type} [Fintype Ω] (S q : ℕ) (hq : 0 < q) (c : ℕ → ℝ) (pr : ℝ) (hc : ∀ i, pr ≤ c i ∧ c i ≤ 1) (hpr0 : 0 ≤ pr) (hpr : pr ≤ 1) (w : Ω → ℝ) (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1) (plan : Ω → List ℕ) : ∑ ω, w ω * (if S ≤ (capped q (plan ω)).sum then survive c (capped q (plan ω)) 0 else 0) ≤ (1 - pr) ^ ceilDiv S q
~~~

### 899. sc07_fixed_budget

Source: ControlStack/Scenarios/SC07Exfil.lean:158 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc07_fixed_budget {N : ℕ} {Y : Type} [Fintype Y] (S q B : ℕ) (hB : B ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : Finset (Fin N) → List (Y × Leakage.AOut Unit) → Y × Leakage.AOut Unit → ℝ) (σ : List (Leakage.AOut Unit) → Bool → ℝ) (hσ : ∀ g, Covert.IsDist (σ g)) (hK0 : ∀ T, T ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K T h z) (hK1 : ∀ T, T ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K T h z ≤ 1) (hrec : ∀ T, T ∈ AuditBudget.randomSchedules N B → ∀ h (a : Bool), ∑ y, K T h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if Leakage.memN T (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) : ∑ T : Finset (Fin N), ReservedAudit.pU N B T * Leakage.val (K T) (ReservedRecall.recallSucc (N
~~~

### 900. no_quota_one_window

Source: ControlStack/Scenarios/SC07Exfil.lean:174 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_quota_one_window (S q : ℕ) (hS : 0 < S) (hq : S ≤ q) (c : ℕ → ℝ) : ceilDiv S q = 1 ∧ (capped q [S]).sum = S ∧ traffic (capped q [S]) = 1 ∧ survive c (capped q [S]) 0 = 1 - c 0
~~~

### 901. observable_schedule_exfil

Source: ControlStack/Scenarios/SC07Exfil.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem observable_schedule_exfil (q : ℕ) (hq : 0 < q) : let c : ℕ → ℝ
~~~

### 902. datacenter_example

Source: ControlStack/Scenarios/SC07Exfil.lean:197 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem datacenter_example (c : ℕ → ℝ) (hc : ∀ i, (0.05 : ℝ) ≤ c i ∧ c i ≤ 1) (b : List ℕ) (hS : 800000000000 ≤ (capped 8000000000 b).sum) : ceilDiv 800000000000 8000000000 = 100 ∧ survive c (capped 8000000000 b) 0 ≤ 0.006
~~~

### 903. expLeak_nonneg

Source: ControlStack/Scenarios/SC07Exfil.lean:207 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem expLeak_nonneg (c : ℕ → ℝ) (hc : ∀ i, c i ≤ 1) (b : List ℕ) (i : ℕ) : 0 ≤ expLeak c b i
~~~

### 904. expected_leak_le

Source: ControlStack/Scenarios/SC07Exfil.lean:218 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem expected_leak_le (q : ℕ) (c : ℕ → ℝ) (pr : ℝ) (hc : ∀ i, pr ≤ c i ∧ c i ≤ 1) (hpr : 0 < pr) (b : List ℕ) : expLeak c (capped q b) 0 ≤ q / pr
~~~

## ControlStack/Scenarios/SC07Liveness.lean

### 905. run_cons

Source: ControlStack/Scenarios/SC07Liveness.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 906. inv_init

Source: ControlStack/Scenarios/SC07Liveness.lean:104 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) : Inv E init
~~~

### 907. wsum_append

Source: ControlStack/Scenarios/SC07Liveness.lean:108 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum_append (s t : St) (e : Fwd) (ht : t.log = s.log ++ [e]) (w : ℕ) : wsum t w = wsum s w + (if e.window = w then e.bits else 0)
~~~

### 908. wsum_gt

Source: ControlStack/Scenarios/SC07Liveness.lean:113 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum_gt (s : St) (h : ∀ e ∈ s.log, e.window ≤ s.window) (w : ℕ) (hw : s.window < w) : wsum s w = 0
~~~

### 909. step_inv

Source: ControlStack/Scenarios/SC07Liveness.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o)
~~~

### 910. run_inv

Source: ControlStack/Scenarios/SC07Liveness.lean:162 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 911. sc07_safe

Source: ControlStack/Scenarios/SC07Liveness.lean:169 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc07_safe (E : Env) (ops : List Op) : (∀ e ∈ (run E full init ops).log, e.dest ∈ E.allow) ∧ ∀ w, wsum (run E full init ops) w ≤ E.q
~~~

### 912. step_halted

Source: ControlStack/Scenarios/SC07Liveness.lean:178 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s
~~~

### 913. halt_freezes

Source: ControlStack/Scenarios/SC07Liveness.lean:188 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
~~~

### 914. upload_completes

Source: ControlStack/Scenarios/SC07Liveness.lean:197 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem upload_completes (E : Env) (s : St) (d : ℕ) (chunks : List ℕ) (hh : s.halted = false) (hd : d ∈ E.allow) (hq : s.used + chunks.sum ≤ E.q) : (run E full s (chunks.map (fun n => .send d n))).log = s.log ++ chunks.map (fun n => ⟨d, n, s.window⟩)
~~~

### 915. fresh_window_upload

Source: ControlStack/Scenarios/SC07Liveness.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fresh_window_upload (E : Env) (s : St) (d : ℕ) (chunks : List ℕ) (hh : s.halted = false) (hd : d ∈ E.allow) (hfresh : s.used = 0) (hq : chunks.sum ≤ E.q) : (run E full s (chunks.map (fun n => .send d n))).log = s.log ++ chunks.map (fun n => ⟨d, n, s.window⟩)
~~~

### 916. total_le

Source: ControlStack/Scenarios/SC07Liveness.lean:220 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem total_le (E : Env) (ops : List Op) : total (run E full init ops) ≤ E.q * ((run E full init ops).window + 1)
~~~

### 917. exfil_needs_windows

Source: ControlStack/Scenarios/SC07Liveness.lean:228 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exfil_needs_windows (E : Env) (hq : 0 < E.q) (S : ℕ) (ops : List Op) (hS : S ≤ total (run E full init ops)) : SC07Exfil.ceilDiv S E.q ≤ (run E full init ops).window + 1
~~~

### 918. honest_upload

Source: ControlStack/Scenarios/SC07Liveness.lean:239 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_upload : (run E0 full init [.send 10 5, .send 10 3]).log = [⟨10, 5, 0⟩, ⟨10, 3, 0⟩]
~~~

### 919. quota_off_exceeds

Source: ControlStack/Scenarios/SC07Liveness.lean:243 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem quota_off_exceeds : wsum (run E0 { full with quotaCheck
~~~

### 920. allowlist_off_leaks

Source: ControlStack/Scenarios/SC07Liveness.lean:249 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem allowlist_off_leaks : (run E0 { full with allowCheck
~~~

### 921. shared_quota_blocks

Source: ControlStack/Scenarios/SC07Liveness.lean:256 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem shared_quota_blocks : (run E0 full init [.send 10 6, .send 10 4]).log = [⟨10, 6, 0⟩] ∧ (run E0 full init [.send 10 6, .tick, .send 10 4]).log = [⟨10, 6, 0⟩, ⟨10, 4, 1⟩]
~~~

### 922. halt_stops

Source: ControlStack/Scenarios/SC07Liveness.lean:262 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_stops : (run E0 full init [.send 10 2, .halt 9, .send 10 2, .tick, .send 10 2]).log = [⟨10, 2, 0⟩]
~~~

## ControlStack/Scenarios/SC07Refinement.lean

### 923. runC_cons

Source: ControlStack/Scenarios/SC07Refinement.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runC_cons (K : CCfg) (s : CSt) (o : COp) (ops : List COp) : runC K s (o :: ops) = runC K (stepC K s o) ops
~~~

### 924. runC_append

Source: ControlStack/Scenarios/SC07Refinement.lean:122 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runC_append (K : CCfg) (s : CSt) (a b : List COp) : runC K s (a ++ b) = runC K (runC K s a) b
~~~

### 925. payloadIn_append

Source: ControlStack/Scenarios/SC07Refinement.lean:131 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem payloadIn_append (l : List FwdRec) (r : FwdRec) (w : ℕ) : payloadIn (l ++ [r]) w = payloadIn l w + (if r.window = w then r.payload else 0)
~~~

### 926. wireIn_append

Source: ControlStack/Scenarios/SC07Refinement.lean:135 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wireIn_append (l : List FwdRec) (r : FwdRec) (w : ℕ) : wireIn (l ++ [r]) w = wireIn l w + (if r.window = w then r.wire else 0)
~~~

### 927. payloadIn_le_wireIn

Source: ControlStack/Scenarios/SC07Refinement.lean:139 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem payloadIn_le_wireIn (l : List FwdRec) (h : ∀ r ∈ l, r.payload ≤ r.wire) (w : ℕ) : payloadIn l w ≤ wireIn l w
~~~

### 928. in_gt

Source: ControlStack/Scenarios/SC07Refinement.lean:149 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem in_gt (l : List FwdRec) (w : ℕ) (h : ∀ r ∈ l, r.window < w) : payloadIn l w = 0 ∧ wireIn l w = 0
~~~

### 929. cinv_init

Source: ControlStack/Scenarios/SC07Refinement.lean:161 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_init : CInv cinit
~~~

### 930. cinv_step

Source: ControlStack/Scenarios/SC07Refinement.lean:163 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_step (K : CCfg) (hK : K.quotaRule = true) (s : CSt) (o : COp) (h : CInv s) : CInv (stepC K s o)
~~~

### 931. cinv_run

Source: ControlStack/Scenarios/SC07Refinement.lean:190 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_run (K : CCfg) (hK : K.quotaRule = true) (s : CSt) (ops : List COp) (h : CInv s) : CInv (runC K s ops)
~~~

### 932. simulation

Source: ControlStack/Scenarios/SC07Refinement.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation (K : CCfg) (hK : K.quotaRule = true) (s : CSt) (o : COp) (h : CInv s) : α (stepC K s o) = SC07Liveness.run (envOf K) SC07Liveness.full (α s) (opsOf K s o)
~~~

### 933. simulation_run

Source: ControlStack/Scenarios/SC07Refinement.lean:253 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation_run (K : CCfg) (hK : K.quotaRule = true) (s : CSt) (ops : List COp) (h : CInv s) : α (runC K s ops) = SC07Liveness.run (envOf K) SC07Liveness.full (α s) (absTrace K s ops)
~~~

### 934. concrete_safe

Source: ControlStack/Scenarios/SC07Refinement.lean:272 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_safe (K : CCfg) (hK : K.quotaRule = true) (ops : List COp) : (∀ r ∈ (runC K cinit ops).fwd, (r.ip, r.port) ∈ K.allow) ∧ ∀ w, payloadIn (runC K cinit ops).fwd w ≤ K.Q - 1
~~~

### 935. wire_eq_payload_add_hdr

Source: ControlStack/Scenarios/SC07Refinement.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wire_eq_payload_add_hdr (K : CCfg) (ops : List COp) : ∀ r ∈ (runC K cinit ops).fwd, ∃ hd, r.wire = r.payload + hd
~~~

### 936. concrete_wire_lt

Source: ControlStack/Scenarios/SC07Refinement.lean:309 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_wire_lt (K : CCfg) (hK : K.quotaRule = true) (hQ : 0 < K.Q) (ops : List COp) (w : ℕ) : wireIn (runC K cinit ops).fwd w < K.Q
~~~

### 937. concrete_halt_freezes

Source: ControlStack/Scenarios/SC07Refinement.lean:342 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_halt_freezes (K : CCfg) (hK : K.quotaRule = true) (pre post : List COp) (hh : (runC K cinit pre).halted = true) : (runC K cinit (pre ++ post)).fwd = (runC K cinit pre).fwd
~~~

### 938. sink_within_quota

Source: ControlStack/Scenarios/SC07Refinement.lean:372 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sink_within_quota (K : CCfg) (hK : K.quotaRule = true) (ops : List COp) (w sinkBytes tol : ℕ) (hsink : sinkBytes ≤ payloadIn (runC K cinit ops).fwd w) : sinkBytes ≤ K.Q - 1 ∧ sinkBytes ≤ K.Q + tol
~~~

### 939. quota_rule_absent_breaks

Source: ControlStack/Scenarios/SC07Refinement.lean:383 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem quota_rule_absent_breaks : payloadIn (runC (K0 false) cinit [.pkt 1 8080 8 1, .pkt 1 8080 8 1, .pkt 1 8080 8 1]).fwd 0 = 24 ∧ payloadIn (runC (K0 true) cinit [.pkt 1 8080 8 1, .pkt 1 8080 8 1, .pkt 1 8080 8 1]).fwd 0 = 8
~~~

### 940. crossing_packet_dropped

Source: ControlStack/Scenarios/SC07Refinement.lean:390 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem crossing_packet_dropped : let t
~~~

### 941. halt_witness

Source: ControlStack/Scenarios/SC07Refinement.lean:396 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_witness : (runC (K0 true) cinit [.pkt 1 8080 2 1, .halt, .resetQuota, .pkt 1 8080 2 1]).fwd = [⟨1, 8080, 2, 3, 0⟩]
~~~

## ControlStack/Scenarios/SC08Exec.lean

### 942. run_cons

Source: ControlStack/Scenarios/SC08Exec.lean:103 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 943. sound_full

Source: ControlStack/Scenarios/SC08Exec.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sound_full : Sound full
~~~

### 944. execResult_ok

Source: ControlStack/Scenarios/SC08Exec.lean:121 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem execResult_ok (E : Env) {C : Checks} (hC : Sound C) (s : St) (p : ℕ) (sc : Option ℕ) (r : ℕ × Option ℕ) (h : execResult E C s p sc = some r) : RunOk E r
~~~

### 945. step_good

Source: ControlStack/Scenarios/SC08Exec.lean:139 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_good (E : Env) {C : Checks} (hC : Sound C) (s : St) (o : Op) (h : Good E s) : Good E (step E C s o)
~~~

### 946. run_good

Source: ControlStack/Scenarios/SC08Exec.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_good (E : Env) {C : Checks} (hC : Sound C) (s : St) (ops : List Op) (h : Good E s) : Good E (run E C s ops)
~~~

### 947. safe_of_sound

Source: ControlStack/Scenarios/SC08Exec.lean:164 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem safe_of_sound (E : Env) {C : Checks} (hC : Sound C) (files : List (ℕ × ℕ)) (ops : List Op) : Good E (run E C ⟨files, [], false⟩ ops)
~~~

### 948. sc08_safe

Source: ControlStack/Scenarios/SC08Exec.lean:171 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc08_safe (E : Env) (files : List (ℕ × ℕ)) (ops : List Op) : Good E (run E full ⟨files, [], false⟩ ops)
~~~

### 949. digest_design_needs_no_noexec

Source: ControlStack/Scenarios/SC08Exec.lean:175 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem digest_design_needs_no_noexec (E : Env) (files : List (ℕ × ℕ)) (ops : List Op) : Good E (run E { full with noexec
~~~

### 950. step_halted

Source: ControlStack/Scenarios/SC08Exec.lean:181 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s
~~~

### 951. halt_freezes

Source: ControlStack/Scenarios/SC08Exec.lean:191 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
~~~

### 952. ran_prefix

Source: ControlStack/Scenarios/SC08Exec.lean:198 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ran_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.ran <+: (step E C s o).ran
~~~

### 953. honest_execs

Source: ControlStack/Scenarios/SC08Exec.lean:239 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_execs : (run E0 full s0 [.exec 1 none, .exec 4 (some 5)]).ran = [(10, none), (20, some 30)]
~~~

### 954. path_allowlist_toctou_breaks

Source: ControlStack/Scenarios/SC08Exec.lean:244 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem path_allowlist_toctou_breaks : (run E0 { full with byDigest
~~~

### 955. writable_exec_mount_breaks

Source: ControlStack/Scenarios/SC08Exec.lean:250 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem writable_exec_mount_breaks : (run E0 { full with byDigest
~~~

### 956. interpreter_loophole_breaks

Source: ControlStack/Scenarios/SC08Exec.lean:257 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem interpreter_loophole_breaks : (run E0 { full with scriptCheck
~~~

### 957. interpreter_repl_breaks

Source: ControlStack/Scenarios/SC08Exec.lean:263 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem interpreter_repl_breaks : (run E0 { full with scriptCheck
~~~

### 958. no_halt_check_breaks

Source: ControlStack/Scenarios/SC08Exec.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run E0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC09Priv.lean

### 959. run_cons

Source: ControlStack/Scenarios/SC09Priv.lean:145 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (P : Policy) (C : Checks) (s : St) (o : Op) (ops : List Op) : run P C s (o :: ops) = run P C (step P C s o) ops
~~~

### 960. good_init

Source: ControlStack/Scenarios/SC09Priv.lean:158 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem good_init (P : Policy) : Good P init
~~~

### 961. procOf_mem

Source: ControlStack/Scenarios/SC09Priv.lean:160 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem procOf_mem {s : St} {pid : ℕ} {q : Proc} (h : procOf s pid = some q) : q ∈ s.procs
~~~

### 962. UseOk.mono

Source: ControlStack/Scenarios/SC09Priv.lean:163 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem UseOk.mono {P : Policy} {s t : St} (hg : s.granted ⊆ t.granted) {u : Use} (h : UseOk P s u) : UseOk P t u
~~~

### 963. use_append

Source: ControlStack/Scenarios/SC09Priv.lean:166 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem use_append {P : Policy} {s : St} (h : Good P s) (u : Use) (hu : UseOk P s u) : Good P { s with used
~~~

### 964. step_good

Source: ControlStack/Scenarios/SC09Priv.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_good (P : Policy) (s : St) (o : Op) (h : Good P s) : Good P (step P full s o)
~~~

### 965. run_good

Source: ControlStack/Scenarios/SC09Priv.lean:253 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_good (P : Policy) (s : St) (ops : List Op) (h : Good P s) : Good P (run P full s ops)
~~~

### 966. sc09_safe

Source: ControlStack/Scenarios/SC09Priv.lean:261 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc09_safe (P : Policy) (ops : List Op) : Good P (run P full init ops)
~~~

### 967. spawn_attenuates

Source: ControlStack/Scenarios/SC09Priv.lean:264 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem spawn_attenuates (P : Policy) (s : St) (p ch : ℕ) (keep : List ℕ) (q : Proc) (hh : s.halted = false) (hp : procOf s p = some q) (hc : procOf s ch = none) : ∀ r ∈ (step P full s (.spawn p ch keep)).procs, r ∉ s.procs → r.lin = q.lin ∧ r.caps ⊆ q.caps
~~~

### 968. step_halted

Source: ControlStack/Scenarios/SC09Priv.lean:276 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (P : Policy) (s : St) (o : Op) (hh : s.halted = true) : step P full s o = s
~~~

### 969. halt_freezes

Source: ControlStack/Scenarios/SC09Priv.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (P : Policy) (s : St) (ops : List Op) (hh : s.halted = true) : run P full s ops = s
~~~

### 970. used_prefix

Source: ControlStack/Scenarios/SC09Priv.lean:293 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem used_prefix (P : Policy) (C : Checks) (s : St) (o : Op) : s.used <+: (step P C s o).used
~~~

### 971. honest_privileged_work

Source: ControlStack/Scenarios/SC09Priv.lean:332 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_privileged_work : (run P0 full init [.start 9 1 1, .grant 9 1 1 7, .use 1 7, .elevate 1 50 3, .spawn 1 2 [7], .use 2 7]).used = [⟨1, 7, none⟩, ⟨1, 8, some (50, 3)⟩, ⟨1, 7, none⟩]
~~~

### 972. unrestricted_elevation_breaks

Source: ControlStack/Scenarios/SC09Priv.lean:338 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unrestricted_elevation_breaks : (run P0 { full with exactArgs
~~~

### 973. exec_without_attenuation_breaks

Source: ControlStack/Scenarios/SC09Priv.lean:344 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exec_without_attenuation_breaks : (run P0 { full with attenuate
~~~

### 974. confused_deputy_breaks

Source: ControlStack/Scenarios/SC09Priv.lean:350 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem confused_deputy_breaks : (run P0 { full with deputyCheck
~~~

### 975. no_halt_check_breaks

Source: ControlStack/Scenarios/SC09Priv.lean:356 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run P0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC10Policy.lean

### 976. run_cons

Source: ControlStack/Scenarios/SC10Policy.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 977. inv_init

Source: ControlStack/Scenarios/SC10Policy.lean:136 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) : Inv E init
~~~

### 978. DecOk.mono

Source: ControlStack/Scenarios/SC10Policy.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem DecOk.mono {E : Env} {s t : St} (hp : s.versions <+: t.versions) {d : Dec} (h : DecOk E s d) : DecOk E t d
~~~

### 979. inv_same

Source: ControlStack/Scenarios/SC10Policy.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_same {E : Env} {s t : St} (h : Inv E s) (hv : t.versions = s.versions) (hd : t.decisions = s.decisions) (hb : t.builds = s.builds) : Inv E t
~~~

### 980. step_inv

Source: ControlStack/Scenarios/SC10Policy.lean:154 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o)
~~~

### 981. run_inv

Source: ControlStack/Scenarios/SC10Policy.lean:203 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 982. sc10_safe

Source: ControlStack/Scenarios/SC10Policy.lean:212 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc10_safe (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (ops : List Op) : Good E (run E full init ops)
~~~

### 983. policy_admin_only

Source: ControlStack/Scenarios/SC10Policy.lean:217 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem policy_admin_only (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (ops : List Op) : ∀ pv ∈ (run E full init ops).versions, pv.2 ∈ E.admins
~~~

### 984. step_halted

Source: ControlStack/Scenarios/SC10Policy.lean:223 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s
~~~

### 985. halt_freezes

Source: ControlStack/Scenarios/SC10Policy.lean:233 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
~~~

### 986. decisions_prefix

Source: ControlStack/Scenarios/SC10Policy.lean:240 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem decisions_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.decisions <+: (step E C s o).decisions
~~~

### 987. honest_enforcement_and_build

Source: ControlStack/Scenarios/SC10Policy.lean:273 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_enforcement_and_build : let s
~~~

### 988. agent_writable_policy_breaks

Source: ControlStack/Scenarios/SC10Policy.lean:279 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_writable_policy_breaks : let s
~~~

### 989. stale_cache_breaks

Source: ControlStack/Scenarios/SC10Policy.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stale_cache_breaks : (run E0 { full with fresh
~~~

### 990. alternate_evaluator_breaks

Source: ControlStack/Scenarios/SC10Policy.lean:293 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem alternate_evaluator_breaks : (run E0 { full with singleEval
~~~

### 991. path_toolchain_breaks

Source: ControlStack/Scenarios/SC10Policy.lean:300 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem path_toolchain_breaks : (run E0 { full with pinnedPath
~~~

### 992. no_halt_check_breaks

Source: ControlStack/Scenarios/SC10Policy.lean:306 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run E0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC10ReadUseGap.lean

### 993. intervening_commit_stales_decision

Source: ControlStack/Scenarios/SC10ReadUseGap.lean:57 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem intervening_commit_stales_decision : let s
~~~

### 994. no_intervening_commit_matches

Source: ControlStack/Scenarios/SC10ReadUseGap.lean:67 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_intervening_commit_matches : (run [9] [.commit 9 5, .readLatest, .apply 1]).applied = (SC10.run SC10.E0 SC10.full SC10.init [.writePolicy 9 5, .decide 1]).decisions
~~~

### 995. atomic_decision_uses_latest

Source: ControlStack/Scenarios/SC10ReadUseGap.lean:75 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem atomic_decision_uses_latest : (SC10.run SC10.E0 SC10.full SC10.init [.writePolicy 9 5, .writePolicy 9 6, .decide 1]).decisions = [⟨1, some 1, 6, 2⟩]
~~~

## ControlStack/Scenarios/SC10Refinement.lean

### 996. simulation_step

Source: ControlStack/Scenarios/SC10Refinement.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation_step (K : Config) (s : CSt) (e : Event) : alpha (stepC K s e) = SC10.step (envOf K) SC10.full (alpha s) (abstractEvent e)
~~~

### 997. simulation_run

Source: ControlStack/Scenarios/SC10Refinement.lean:123 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation_run (K : Config) (s : CSt) (events : List Event) : alpha (runC K s events) = SC10.run (envOf K) SC10.full (alpha s) (events.map abstractEvent)
~~~

### 998. alpha_init

Source: ControlStack/Scenarios/SC10Refinement.lean:135 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem alpha_init : alpha cinit = SC10.init
~~~

### 999. concrete_safe

Source: ControlStack/Scenarios/SC10Refinement.lean:139 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_safe (K : Config) (hpin : K.digest K.pinnedBinary = K.pinnedDigest) (events : List Event) : SC10.Good (envOf K) (alpha (runC K cinit events))
~~~

### 1000. concrete_admin_only

Source: ControlStack/Scenarios/SC10Refinement.lean:147 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_admin_only (K : Config) (hpin : K.digest K.pinnedBinary = K.pinnedDigest) (events : List Event) : ∀ v ∈ (runC K cinit events).policyLog, v.2 ∈ K.adminPids
~~~

### 1001. stale_cache_counterexample

Source: ControlStack/Scenarios/SC10Refinement.lean:176 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stale_cache_counterexample : (staleRun testConfig cinit [.commit 9 5, .readCache, .commit 9 6, .enforce 1]).decisionReceipts = [⟨1, some 0, 5, 2⟩] ∧ (runC testConfig cinit [.commit 9 5, .readCache, .commit 9 6, .enforce 1]).decisionReceipts = [⟨1, some 1, 6, 2⟩]
~~~

## ControlStack/Scenarios/SC12Persistence.lean

### 1002. run_cons

Source: ControlStack/Scenarios/SC12Persistence.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (admins : List ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) : run admins C s (o :: ops) = run admins C (step admins C s o) ops
~~~

### 1003. inv_init

Source: ControlStack/Scenarios/SC12Persistence.lean:134 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init : Inv init
~~~

### 1004. Inv.good

Source: ControlStack/Scenarios/SC12Persistence.lean:136 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {s : St} (h : Inv s) : Good s
~~~

### 1005. fireOk_mono

Source: ControlStack/Scenarios/SC12Persistence.lean:140 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fireOk_mono {s t : St} (hp : s.ended <+: t.ended) (f : ℕ × ℕ × ℕ) (h : FireOk s f) : FireOk t f
~~~

### 1006. entOf_mem

Source: ControlStack/Scenarios/SC12Persistence.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem entOf_mem {s : St} {id : ℕ} {e : Ent} (h : entOf s id = some e) : e ∈ s.live
~~~

### 1007. step_inv

Source: ControlStack/Scenarios/SC12Persistence.lean:148 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (admins : List ℕ) (s : St) (o : Op) (h : Inv s) : Inv (step admins full s o)
~~~

### 1008. run_inv

Source: ControlStack/Scenarios/SC12Persistence.lean:224 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (admins : List ℕ) (s : St) (ops : List Op) (h : Inv s) : Inv (run admins full s ops)
~~~

### 1009. sc12_safe

Source: ControlStack/Scenarios/SC12Persistence.lean:231 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc12_safe (admins : List ℕ) (ops : List Op) : Good (run admins full init ops)
~~~

### 1010. step_ended

Source: ControlStack/Scenarios/SC12Persistence.lean:234 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_ended (admins : List ℕ) (s : St) (o : Op) (h : Inv s) (sess : ℕ) (hs : sess ∈ s.ended) : sess ∈ (step admins full s o).ended ∧ (step admins full s o).fired.filter (fun f => f.2.1 = sess) = s.fired.filter (fun f => f.2.1 = sess)
~~~

### 1011. no_fire_after_end

Source: ControlStack/Scenarios/SC12Persistence.lean:264 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_fire_after_end (admins : List ℕ) (s : St) (ops : List Op) (h : Inv s) (sess : ℕ) (hs : sess ∈ s.ended) : (run admins full s ops).fired.filter (fun f => f.2.1 = sess) = s.fired.filter (fun f => f.2.1 = sess)
~~~

### 1012. step_halted

Source: ControlStack/Scenarios/SC12Persistence.lean:275 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (admins : List ℕ) (s : St) (o : Op) (hh : s.halted = true) : step admins full s o = s
~~~

### 1013. halt_freezes

Source: ControlStack/Scenarios/SC12Persistence.lean:279 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (admins : List ℕ) (s : St) (ops : List Op) (hh : s.halted = true) : run admins full s ops = s
~~~

### 1014. fired_prefix

Source: ControlStack/Scenarios/SC12Persistence.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fired_prefix (admins : List ℕ) (C : Checks) (s : St) (o : Op) : s.fired <+: (step admins C s o).fired
~~~

### 1015. honest_session_lifecycle

Source: ControlStack/Scenarios/SC12Persistence.lean:315 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_session_lifecycle : let s
~~~

### 1016. registry_bypass_survives

Source: ControlStack/Scenarios/SC12Persistence.lean:321 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem registry_bypass_survives : (run [9] { full with registryOnly
~~~

### 1017. parent_only_revocation_survives

Source: ControlStack/Scenarios/SC12Persistence.lean:328 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem parent_only_revocation_survives : (run [9] { full with revokeLineage
~~~

### 1018. foreign_registration_survives

Source: ControlStack/Scenarios/SC12Persistence.lean:335 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foreign_registration_survives : (run [9] { full with lineage
~~~

### 1019. no_halt_check_breaks

Source: ControlStack/Scenarios/SC12Persistence.lean:342 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run [9] { full with haltCheck
~~~

## ControlStack/Scenarios/SC14Runaway.lean

### 1020. run_cons

Source: ControlStack/Scenarios/SC14Runaway.lean:102 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 1021. vzero_le

Source: ControlStack/Scenarios/SC14Runaway.lean:129 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem vzero_le (v : Vec) : (0 : Vec) ≤ v
~~~

### 1022. inv_init

Source: ControlStack/Scenarios/SC14Runaway.lean:133 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) (exp : ℕ) : Inv E (init exp)
~~~

### 1023. windowSum_append

Source: ControlStack/Scenarios/SC14Runaway.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem windowSum_append (s : St) (u : Use) (t : ℕ) : windowSum { s with usage
~~~

### 1024. windowSum_gt

Source: ControlStack/Scenarios/SC14Runaway.lean:143 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem windowSum_gt {s : St} (h : ∀ u ∈ s.usage, u.2.1 ≤ s.clock) (t : ℕ) (ht : s.clock < t) : windowSum s t = 0
~~~

### 1025. Inv.good

Source: ControlStack/Scenarios/SC14Runaway.lean:148 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {E : Env} {s : St} (h : Inv E s) : Good E s
~~~

### 1026. step_inv

Source: ControlStack/Scenarios/SC14Runaway.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (s : St) (o : Op) (ho : legal o) (h : Inv E s) : Inv E (step E full s o)
~~~

### 1027. run_inv

Source: ControlStack/Scenarios/SC14Runaway.lean:204 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal o) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 1028. sc14_safe

Source: ControlStack/Scenarios/SC14Runaway.lean:215 | Family: F5 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc14_safe (E : Env) (exp : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal o) : Good E (run E full (init exp) ops)
~~~

### 1029. step_halted

Source: ControlStack/Scenarios/SC14Runaway.lean:221 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : (step E full s o).usage = s.usage ∧ (step E full s o).halted = true
~~~

### 1030. halt_freezes

Source: ControlStack/Scenarios/SC14Runaway.lean:229 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : (run E full s ops).usage = s.usage
~~~

### 1031. usage_prefix

Source: ControlStack/Scenarios/SC14Runaway.lean:240 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usage_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.usage <+: (step E C s o).usage
~~~

### 1032. honest_work

Source: ControlStack/Scenarios/SC14Runaway.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_work : (run E0 full (init 100) [.work (2, 2, 2) (2, 2, 2), .tick, .work (3, 3, 3) (3, 3, 3)]).usage = [((2, 2, 2), 0, 100), ((3, 3, 3), 1, 100)]
~~~

### 1033. aggregate_cap_breaks

Source: ControlStack/Scenarios/SC14Runaway.lean:275 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem aggregate_cap_breaks : let ops
~~~

### 1034. reported_cost_breaks

Source: ControlStack/Scenarios/SC14Runaway.lean:282 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reported_cost_breaks : let ops
~~~

### 1035. rate_burst_breaks

Source: ControlStack/Scenarios/SC14Runaway.lean:289 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rate_burst_breaks : usedTotal (run E0 { full with rate
~~~

### 1036. no_expiry_breaks

Source: ControlStack/Scenarios/SC14Runaway.lean:295 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_expiry_breaks : (run E0 { full with expiry
~~~

### 1037. rollback_double_spends

Source: ControlStack/Scenarios/SC14Runaway.lean:301 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rollback_double_spends : usedTotal (run E0 full (init 100) [.work (0, 0, 5) 0, .tick, .work (0, 0, 5) 0, .rollback, .tick, .work (0, 0, 5) 0]) = (0, 0, 15)
~~~

### 1038. no_halt_check_breaks

Source: ControlStack/Scenarios/SC14Runaway.lean:307 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run E0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC15Review.lean

### 1039. run_cons

Source: ControlStack/Scenarios/SC15Review.lean:139 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 1040. inv_init

Source: ControlStack/Scenarios/SC15Review.lean:157 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) : Inv E init
~~~

### 1041. MergeOk.mono

Source: ControlStack/Scenarios/SC15Review.lean:159 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem MergeOk.mono {E : Env} {s t : St} (hr : s.reviews ⊆ t.reviews) (hc : s.ci ⊆ t.ci) {c : Change} (h : MergeOk E s c) : MergeOk E t c
~~~

### 1042. revOk_of

Source: ControlStack/Scenarios/SC15Review.lean:166 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem revOk_of {E : Env} {s : St} (h : Inv E s) {c : Change} {sec : Bool} (hrv : Reviewed full s c sec) : ∃ r ∈ s.reviews, r.id = c.id ∧ r.content = c.content ∧ r.reviewer ≠ c.author ∧ (sec = true → r.sec = true) ∧ roleOk E r.sec r.reviewer = true
~~~

### 1043. step_inv

Source: ControlStack/Scenarios/SC15Review.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o)
~~~

### 1044. run_inv

Source: ControlStack/Scenarios/SC15Review.lean:218 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 1045. sc15_safe

Source: ControlStack/Scenarios/SC15Review.lean:227 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc15_safe (E : Env) (ops : List Op) : ∀ c ∈ (run E full init ops).merged, MergeOk E (run E full init ops) c
~~~

### 1046. step_halted

Source: ControlStack/Scenarios/SC15Review.lean:230 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s
~~~

### 1047. halt_freezes

Source: ControlStack/Scenarios/SC15Review.lean:240 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
~~~

### 1048. merged_prefix

Source: ControlStack/Scenarios/SC15Review.lean:245 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem merged_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.merged <+: (step E C s o).merged
~~~

### 1049. honest_merge

Source: ControlStack/Scenarios/SC15Review.lean:274 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_merge : (run E0 full init [.propose 1 0 7 [5] [5], .review 2 0 false, .runCI 0, .merge 0]).merged = [⟨0, 1, 7, [5], [5]⟩]
~~~

### 1050. stale_review_breaks

Source: ControlStack/Scenarios/SC15Review.lean:279 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stale_review_breaks : let ops
~~~

### 1051. declared_paths_breaks

Source: ControlStack/Scenarios/SC15Review.lean:287 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem declared_paths_breaks : let ops
~~~

### 1052. ci_other_content_breaks

Source: ControlStack/Scenarios/SC15Review.lean:294 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ci_other_content_breaks : let ops
~~~

### 1053. self_review_breaks

Source: ControlStack/Scenarios/SC15Review.lean:301 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem self_review_breaks : let E1 : Env
~~~

### 1054. no_halt_check_breaks

Source: ControlStack/Scenarios/SC15Review.lean:309 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : let ops
~~~

## ControlStack/Scenarios/SC16Deploy.lean

### 1055. run_cons

Source: ControlStack/Scenarios/SC16Deploy.lean:147 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (R : Roles) (h : ℕ → ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) : run R h C s (o :: ops) = run R h C (step R h C s o) ops
~~~

### 1056. inv_init

Source: ControlStack/Scenarios/SC16Deploy.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (R : Roles) (h : ℕ → ℕ) : Inv R h init
~~~

### 1057. Inv.good

Source: ControlStack/Scenarios/SC16Deploy.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {R : Roles} {h : ℕ → ℕ} {s : St} (hi : Inv R h s) : Good R h s
~~~

### 1058. apprOf_mem

Source: ControlStack/Scenarios/SC16Deploy.lean:178 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem apprOf_mem {s : St} {n : ℕ} {ap : Appr} (h : apprOf s n = some ap) : ap ∈ s.approvals ∧ ap.n = n
~~~

### 1059. inv_of_mono

Source: ControlStack/Scenarios/SC16Deploy.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_of_mono {R : Roles} {h : ℕ → ℕ} {s t : St} (hi : Inv R h s) (hrev : s.reviews ⊆ t.reviews) (happ : s.approvals ⊆ t.approvals) (hrevn : ∀ rv ∈ t.reviews, rv ∉ s.reviews → ReviewOk R h rv) (happn : ∀ ap ∈ t.approvals, ap ∉ s.approvals → ap.approver ∈ R.approvers) (hdep : t.deployed = s.deployed) (hused : t.used = s.used) : Inv R h t
~~~

### 1060. doDeploy_inv

Source: ControlStack/Scenarios/SC16Deploy.lean:198 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem doDeploy_inv {R : Roles} {h : ℕ → ℕ} {s : St} (hi : Inv R h s) (n t x : ℕ) (ap : Appr) (hap : apprOf s n = some ap) (hrv : ∃ rv ∈ s.reviews, rv.d = ap.d) (hn : n ∉ s.used) (ht : t = ap.target) (hx : h x = ap.d) : Inv R h (doDeploy s n t x)
~~~

### 1061. step_inv

Source: ControlStack/Scenarios/SC16Deploy.lean:218 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (R : Roles) (h : ℕ → ℕ) (s : St) (o : Op) (hi : Inv R h s) : Inv R h (step R h full s o)
~~~

### 1062. run_inv

Source: ControlStack/Scenarios/SC16Deploy.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op) (hi : Inv R h s) : Inv R h (run R h full s ops)
~~~

### 1063. sc16_safe

Source: ControlStack/Scenarios/SC16Deploy.lean:294 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc16_safe (R : Roles) (h : ℕ → ℕ) (ops : List Op) : Good R h (run R h full init ops)
~~~

### 1064. sc16_reviewed_content

Source: ControlStack/Scenarios/SC16Deploy.lean:299 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc16_reviewed_content (R : Roles) (h : ℕ → ℕ) (ops : List Op) (hinj : Set.InjOn h {c | (∃ e ∈ (run R h full init ops).deployed, e.content = c) ∨ ∃ rv ∈ (run R h full init ops).reviews, rv.content = c}) : ∀ e ∈ (run R h full init ops).deployed, ∃ rv ∈ (run R h full init ops).reviews, rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager
~~~

### 1065. step_halted

Source: ControlStack/Scenarios/SC16Deploy.lean:310 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (R : Roles) (h : ℕ → ℕ) (s : St) (o : Op) (hh : s.halted = true) : step R h full s o = s
~~~

### 1066. halt_freezes

Source: ControlStack/Scenarios/SC16Deploy.lean:321 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op) (hh : s.halted = true) : run R h full s ops = s
~~~

### 1067. deployed_prefix

Source: ControlStack/Scenarios/SC16Deploy.lean:329 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployed_prefix (R : Roles) (h : ℕ → ℕ) (C : Checks) (s : St) (o : Op) : s.deployed <+: (step R h C s o).deployed
~~~

### 1068. honest_trace_deploys

Source: ControlStack/Scenarios/SC16Deploy.lean:363 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_trace_deploys : (run R0 id full init [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]).deployed = [⟨0, 5, 7⟩]
~~~

### 1069. toctou_slot_breaks

Source: ControlStack/Scenarios/SC16Deploy.lean:369 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem toctou_slot_breaks : let s
~~~

### 1070. verify_blocks_toctou

Source: ControlStack/Scenarios/SC16Deploy.lean:376 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem verify_blocks_toctou : (run R0 id full init [.stage 1 7, .writeSlot 1 0 7, .review 2 7, .approve 3 0 7 5 0, .writeSlot 1 0 666, .deploy 1 0 5 666]).deployed = []
~~~

### 1071. collision_breaks

Source: ControlStack/Scenarios/SC16Deploy.lean:384 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem collision_breaks : let s
~~~

### 1072. no_target_binding_breaks

Source: ControlStack/Scenarios/SC16Deploy.lean:390 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_target_binding_breaks : let s
~~~

### 1073. self_review_without_distinct_check

Source: ControlStack/Scenarios/SC16Deploy.lean:399 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem self_review_without_distinct_check : let s
~~~

### 1074. distinct_blocks_self_review

Source: ControlStack/Scenarios/SC16Deploy.lean:406 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem distinct_blocks_self_review : (run R1 id full init [.stage 1 7, .review 1 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]).deployed = []
~~~

### 1075. no_nonce_redeploys

Source: ControlStack/Scenarios/SC16Deploy.lean:411 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_nonce_redeploys : (run R0 id { full with nonce
~~~

### 1076. no_halt_check_breaks

Source: ControlStack/Scenarios/SC16Deploy.lean:418 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run R0 id { full with haltCheck
~~~

## ControlStack/Scenarios/SC16Disjoint.lean

### 1077. sc16_safe_disjoint

Source: ControlStack/Scenarios/SC16Disjoint.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc16_safe_disjoint (R : Roles) (h : ℕ → ℕ) (ops : List Op) (hrev : ∀ a ∈ R.reviewers, a ∉ R.agents) (happ : ∀ a ∈ R.approvers, a ∉ R.agents) (hinj : Set.InjOn h {c | (∃ e ∈ (run R h full init ops).deployed, e.content = c) ∨ ∃ rv ∈ (run R h full init ops).reviews, rv.content = c}) : ∀ e ∈ (run R h full init ops).deployed, (∃ rv ∈ (run R h full init ops).reviews, rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ∉ R.agents ∧ rv.reviewer ≠ rv.stager) ∧ (∃ ap ∈ (run R h full init ops).approvals, ap.n = e.n ∧ ap.target = e.target ∧ ap.approver ∈ R.approvers ∧ ap.approver ∉ R.agents)
~~~

### 1078. overlap_reviewer_is_agent

Source: ControlStack/Scenarios/SC16Disjoint.lean:46 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem overlap_reviewer_is_agent : let s
~~~

## ControlStack/Scenarios/SC16Refinement.lean

### 1079. depRes_spec

Source: ControlStack/Scenarios/SC16Refinement.lean:165 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem depRes_spec (h : ℕ → ℕ) (s : CSt) (n t : ℕ) (ap : ARow) (x : ℕ) (hd : depRes h false s n t = some (ap, x)) : s.halted = false ∧ capprOf s n = some ap ∧ n ∉ s.used ∧ t = ap.target ∧ (∃ r ∈ s.revLog, r.d = ap.d ∧ r.target = ap.target) ∧ h x = ap.d
~~~

### 1080. simulation

Source: ControlStack/Scenarios/SC16Refinement.lean:182 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation (R : Roles) (h : ℕ → ℕ) (s : CSt) (o : COp) : α (stepC R h false s o) = run R h full (α s) (opsOf R h s o)
~~~

### 1081. simulation_run

Source: ControlStack/Scenarios/SC16Refinement.lean:241 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation_run (R : Roles) (h : ℕ → ℕ) (s : CSt) (ops : List COp) : α (runC R h false s ops) = run R h full (α s) (absTrace R h s ops)
~~~

### 1082. concrete_safe

Source: ControlStack/Scenarios/SC16Refinement.lean:256 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_safe (R : Roles) (h : ℕ → ℕ) (ops : List COp) : Good R h (α (runC R h false cinit ops))
~~~

### 1083. concrete_reviewed_content

Source: ControlStack/Scenarios/SC16Refinement.lean:261 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_reviewed_content (R : Roles) (h : ℕ → ℕ) (ops : List COp) (hinj : Set.InjOn h {c | (∃ e ∈ (α (runC R h false cinit ops)).deployed, e.content = c) ∨ ∃ rv ∈ (α (runC R h false cinit ops)).reviews, rv.content = c}) : ∀ e ∈ (α (runC R h false cinit ops)).deployed, ∃ rv ∈ (α (runC R h false cinit ops)).reviews, rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager
~~~

### 1084. concrete_safe_disjoint

Source: ControlStack/Scenarios/SC16Refinement.lean:271 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_safe_disjoint (R : Roles) (h : ℕ → ℕ) (ops : List COp) (hrev : ∀ a ∈ R.reviewers, a ∉ R.agents) (happ : ∀ a ∈ R.approvers, a ∉ R.agents) (hinj : Set.InjOn h {c | (∃ e ∈ (α (runC R h false cinit ops)).deployed, e.content = c) ∨ ∃ rv ∈ (α (runC R h false cinit ops)).reviews, rv.content = c}) : ∀ e ∈ (α (runC R h false cinit ops)).deployed, (∃ rv ∈ (α (runC R h false cinit ops)).reviews, rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ∉ R.agents ∧ rv.reviewer ≠ rv.stager) ∧ (∃ ap ∈ (α (runC R h false cinit ops)).approvals, ap.n = e.n ∧ ap.target = e.target ∧ ap.approver ∈ R.approvers ∧ ap.approver ∉ R.agents)
~~~

### 1085. by_tag_breaks

Source: ControlStack/Scenarios/SC16Refinement.lean:292 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem by_tag_breaks : (runC R0 id true cinit tagTrace).depLog.map DRow.content = [666] ∧ ¬ Good R0 id (α (runC R0 id true cinit tagTrace)) ∧ (runC R0 id false cinit tagTrace).depLog.map DRow.content = [7]
~~~

## ControlStack/Scenarios/SC17Drift.lean

### 1086. run_cons

Source: ControlStack/Scenarios/SC17Drift.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (d W : ℕ) (sched : Bool) (s : St) (o : Op) (ops : List Op) : run d W sched s (o :: ops) = run d W sched (step d W sched s o) ops
~~~

### 1087. inv_init

Source: ControlStack/Scenarios/SC17Drift.lean:75 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (d W : ℕ) (hW : 0 < W) (desired : List ℕ) : Inv d W (init desired)
~~~

### 1088. step_inv

Source: ControlStack/Scenarios/SC17Drift.lean:78 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (d W : ℕ) (hW : 0 < W) (s : St) (o : Op) (h : Inv d W s) : Inv d W (step d W true s o)
~~~

### 1089. run_inv

Source: ControlStack/Scenarios/SC17Drift.lean:109 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (d W : ℕ) (hW : 0 < W) (s : St) (ops : List Op) (h : Inv d W s) : Inv d W (run d W true s ops)
~~~

### 1090. live_eq

Source: ControlStack/Scenarios/SC17Drift.lean:115 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem live_eq (d W : ℕ) (hW : 0 < W) (desired : List ℕ) (ops : List Op) : (run d W true (init desired) ops).live = (run d W true (init desired) ops).drift.map Prod.fst ++ (run d W true (init desired) ops).desired
~~~

### 1091. drift_bounded_of_inv

Source: ControlStack/Scenarios/SC17Drift.lean:120 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem drift_bounded_of_inv (d W : ℕ) (hW : 0 < W) (s : St) (h : Inv d W s) : (s.live.filter (fun g => g ∉ s.desired)).length ≤ d * W
~~~

### 1092. drift_bounded

Source: ControlStack/Scenarios/SC17Drift.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem drift_bounded (d W : ℕ) (hW : 0 < W) (desired : List ℕ) (ops : List Op) : ((run d W true (init desired) ops).live.filter (fun g => g ∉ (run d W true (init desired) ops).desired)).length ≤ d * W
~~~

### 1093. drift_lifetime

Source: ControlStack/Scenarios/SC17Drift.lean:144 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem drift_lifetime (d W : ℕ) (hW : 0 < W) (desired : List ℕ) (ops : List Op) : ∀ p ∈ (run d W true (init desired) ops).drift, (run d W true (init desired) ops).clock - p.2 < W
~~~

### 1094. ceiling_exceeded_between_reconciles

Source: ControlStack/Scenarios/SC17Drift.lean:154 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ceiling_exceeded_between_reconciles : (run 1 3 true (init []) [.oob 7]).live = [7]
~~~

### 1095. no_schedule_unbounded_lifetime

Source: ControlStack/Scenarios/SC17Drift.lean:160 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_schedule_unbounded_lifetime : (run 1 3 false (init []) ([.oob 7] ++ List.replicate 10 .tick)).live = [7] ∧ (run 1 3 false (init []) ([.oob 7] ++ List.replicate 10 .tick)).clock = 10 ∧ (run 1 3 true (init []) ([.oob 7] ++ List.replicate 10 .tick)).live = []
~~~

### 1096. tick_unscheduled_keeps_live

Source: ControlStack/Scenarios/SC17Drift.lean:166 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tick_unscheduled_keeps_live (d W : ℕ) (s : St) : (step d W false s .tick).live = s.live
~~~

## ControlStack/Scenarios/SC17Infra.lean

### 1097. run_cons

Source: ControlStack/Scenarios/SC17Infra.lean:154 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 1098. inv_init

Source: ControlStack/Scenarios/SC17Infra.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) (g0 : List G) : Inv E (init g0)
~~~

### 1099. Inv.good

Source: ControlStack/Scenarios/SC17Infra.lean:176 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {E : Env} {s : St} (h : Inv E s) : Good E s
~~~

### 1100. propOf_spec

Source: ControlStack/Scenarios/SC17Infra.lean:182 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem propOf_spec {s : St} {id : ℕ} {p : Pr} (h : propOf s id = some p) : p ∈ s.props ∧ p.id = id
~~~

### 1101. inv_same

Source: ControlStack/Scenarios/SC17Infra.lean:186 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_same {E : Env} {s t : St} (h : Inv E s) (ha : t.approvals = s.approvals) (hp : t.applied = s.applied) (hd : t.done = s.done) : Inv E t
~~~

### 1102. step_inv

Source: ControlStack/Scenarios/SC17Infra.lean:190 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o)
~~~

### 1103. run_inv

Source: ControlStack/Scenarios/SC17Infra.lean:238 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 1104. sc17_safe

Source: ControlStack/Scenarios/SC17Infra.lean:246 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc17_safe (E : Env) (g0 : List G) (ops : List Op) : Good E (run E full (init g0) ops)
~~~

### 1105. reconcile_restores

Source: ControlStack/Scenarios/SC17Infra.lean:250 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reconcile_restores (E : Env) (s : St) (hh : s.halted = false) : (step E full s .reconcile).live = (step E full s .reconcile).desired
~~~

### 1106. step_halted

Source: ControlStack/Scenarios/SC17Infra.lean:259 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : (step E full s o).applied = s.applied ∧ (step E full s o).halted = true
~~~

### 1107. halt_freezes

Source: ControlStack/Scenarios/SC17Infra.lean:267 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : (run E full s ops).applied = s.applied
~~~

### 1108. applied_prefix

Source: ControlStack/Scenarios/SC17Infra.lean:278 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem applied_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.applied <+: (step E C s o).applied
~~~

### 1109. honest_apply

Source: ControlStack/Scenarios/SC17Infra.lean:312 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_apply : (run E0 full (init []) [.propose 1 0 dA, .approve 2 0, .apply 0]).live = [(1, 1, 1)]
~~~

### 1110. text_ceiling_composition_breaks

Source: ControlStack/Scenarios/SC17Infra.lean:318 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem text_ceiling_composition_breaks : (E0.allowed (run E0 { full with resultCheck
~~~

### 1111. approve_then_amend_breaks

Source: ControlStack/Scenarios/SC17Infra.lean:326 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem approve_then_amend_breaks : let s
~~~

### 1112. no_drift_detection_breaks

Source: ControlStack/Scenarios/SC17Infra.lean:333 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_drift_detection_breaks : let s
~~~

### 1113. no_halt_check_breaks

Source: ControlStack/Scenarios/SC17Infra.lean:340 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run E0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC18Liveness.lean

### 1114. Mono.refl

Source: ControlStack/Scenarios/SC18Liveness.lean:54 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Mono.refl (s : St) : Mono s s
~~~

### 1115. Mono.trans

Source: ControlStack/Scenarios/SC18Liveness.lean:56 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Mono.trans {s t u : St} (h1 : Mono s t) (h2 : Mono t u) : Mono s u
~~~

### 1116. step_mono

Source: ControlStack/Scenarios/SC18Liveness.lean:60 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_mono (s : St) (o : Op) : Mono s (step admins trusted T full s o)
~~~

### 1117. run_mono

Source: ControlStack/Scenarios/SC18Liveness.lean:90 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_mono (s : St) (ops : List Op) : Mono s (run admins trusted T full s ops)
~~~

### 1118. not_halted_of

Source: ControlStack/Scenarios/SC18Liveness.lean:95 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem not_halted_of {s t : St} (h : Mono s t) (ht : t.halted = false) : s.halted = false
~~~

### 1119. request_fields

Source: ControlStack/Scenarios/SC18Liveness.lean:102 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem request_fields (s : St) (i : ℕ) : (step admins trusted T full s (.request i)).halted = s.halted ∧ (step admins trusted T full s (.request i)).sinkUp = s.sinkUp
~~~

### 1120. logWrite_halted

Source: ControlStack/Scenarios/SC18Liveness.lean:107 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem logWrite_halted (s : St) (i : ℕ) : (step admins trusted T full s (.logWrite i)).halted = s.halted
~~~

### 1121. request_adds

Source: ControlStack/Scenarios/SC18Liveness.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem request_adds (s : St) (i : ℕ) (hh : s.halted = false) : i ∈ (step admins trusted T full s (.request i)).reqs
~~~

### 1122. logWrite_acks

Source: ControlStack/Scenarios/SC18Liveness.lean:115 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem logWrite_acks (s : St) (i : ℕ) (hh : s.halted = false) (hr : i ∈ s.reqs) (hu : s.sinkUp = true) : i ∈ (step admins trusted T full s (.logWrite i)).acked
~~~

### 1123. release_releases

Source: ControlStack/Scenarios/SC18Liveness.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem release_releases (s : St) (i : ℕ) (hh : s.halted = false) (hr : i ∈ s.reqs) (ha : i ∈ s.acked) : i ∈ (step admins trusted T full s (.release i)).released.map Rel.id
~~~

### 1124. honest_release

Source: ControlStack/Scenarios/SC18Liveness.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_release (s : St) (i : ℕ) (hh : s.halted = false) (hu : s.sinkUp = true) : i ∈ (run admins trusted T full s [.request i, .logWrite i, .release i]).released.map Rel.id
~~~

### 1125. progress_interleaved

Source: ControlStack/Scenarios/SC18Liveness.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem progress_interleaved (s : St) (i : ℕ) (a0 a1 a2 a3 : List Op) : let t
~~~

### 1126. ticks_keep_halted

Source: ControlStack/Scenarios/SC18Liveness.lean:184 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ticks_keep_halted (m : ℕ) (t : St) (ht : t.halted = true) : (run admins trusted T full t (List.replicate m .tick)).halted = true
~~~

### 1127. silent_ticks_halt

Source: ControlStack/Scenarios/SC18Liveness.lean:192 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem silent_ticks_halt (s : St) (n : ℕ) (hinv : s.halted = false → s.clock ≤ s.lastAck + T) (hn : s.lastAck + T < s.clock + n) : (run admins trusted T full s (List.replicate n .tick)).halted = true
~~~

### 1128. outage_fail_closed

Source: ControlStack/Scenarios/SC18Liveness.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem outage_fail_closed : (run [9] 0 2 full (init 0) [.request 0, .logWrite 0, .sinkDown, .tick, .tick, .tick]).halted = true ∧ (run [9] 0 2 full (init 0) [.request 0, .logWrite 0, .sinkDown, .tick, .tick, .tick, .sinkRestore, .request 1, .logWrite 1, .release 1]).released = []
~~~

### 1129. run_cons

Source: ControlStack/Scenarios/SC18Liveness.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (admins : List ℕ) (T : ℕ) (s : St) (o : Op) (ops : List Op) : run admins T s (o :: ops) = run admins T (step admins T s o) ops
~~~

### 1130. inv_init

Source: ControlStack/Scenarios/SC18Liveness.lean:281 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (T : ℕ) : Inv T init
~~~

### 1131. RelOk.mono

Source: ControlStack/Scenarios/SC18Liveness.lean:283 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem RelOk.mono {T : ℕ} {s t : St} (hp : s.logged <+: t.logged) {r : SC18.Rel} (h : RelOk T s r) : RelOk T t r
~~~

### 1132. step_inv

Source: ControlStack/Scenarios/SC18Liveness.lean:289 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (admins : List ℕ) (T : ℕ) (s : St) (o : Op) (h : Inv T s) : Inv T (step admins T s o)
~~~

### 1133. run_inv

Source: ControlStack/Scenarios/SC18Liveness.lean:331 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (admins : List ℕ) (T : ℕ) (s : St) (ops : List Op) (h : Inv T s) : Inv T (run admins T s ops)
~~~

### 1134. resume_safe

Source: ControlStack/Scenarios/SC18Liveness.lean:338 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem resume_safe (admins : List ℕ) (T : ℕ) (ops : List Op) : (∀ r ∈ (run admins T init ops).released, RelOk T (run admins T init ops) r) ∧ ((run admins T init ops).released.map SC18.Rel.id).Nodup
~~~

### 1135. paused_no_release

Source: ControlStack/Scenarios/SC18Liveness.lean:345 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem paused_no_release (admins : List ℕ) (T : ℕ) (s : St) (id : ℕ) (hp : s.paused = true) : step admins T s (.release id) = s
~~~

### 1136. resume_progress

Source: ControlStack/Scenarios/SC18Liveness.lean:351 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem resume_progress (admins : List ℕ) (T : ℕ) (s : St) (i : ℕ) (hh : s.halted = false) (hu : s.sinkUp = true) (hr : i ∈ s.reqs) : i ∈ (run admins T s [.logWrite i, .release i]).released.map SC18.Rel.id
~~~

### 1137. pause_then_resume

Source: ControlStack/Scenarios/SC18Liveness.lean:363 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pause_then_resume : (run [9] 2 init [.request 0, .logWrite 0, .sinkDown, .tick, .tick, .tick, .release 0]).released = [] ∧ (run [9] 2 init [.request 0, .logWrite 0, .sinkDown, .tick, .tick, .tick, .release 0]).paused = true ∧ (run [9] 2 init [.request 0, .logWrite 0, .sinkDown, .tick, .tick, .tick, .release 0, .sinkRestore, .logWrite 0, .release 0]).released.map SC18.Rel.id = [0]
~~~

## ControlStack/Scenarios/SC18Logging.lean

### 1138. run_cons

Source: ControlStack/Scenarios/SC18Logging.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (admins : List ℕ) (trusted T : ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) : run admins trusted T C s (o :: ops) = run admins trusted T C (step admins trusted T C s o) ops
~~~

### 1139. inv_init

Source: ControlStack/Scenarios/SC18Logging.lean:133 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (trusted T : ℕ) : Inv trusted T (init trusted)
~~~

### 1140. RelOk.mono

Source: ControlStack/Scenarios/SC18Logging.lean:136 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem RelOk.mono {T : ℕ} {s t : St} (hp : s.logged <+: t.logged) {r : Rel} (h : RelOk T s r) : RelOk T t r
~~~

### 1141. step_inv

Source: ControlStack/Scenarios/SC18Logging.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (admins : List ℕ) (trusted T : ℕ) (s : St) (o : Op) (ho : legal admins trusted o) (h : Inv trusted T s) : Inv trusted T (step admins trusted T full s o)
~~~

### 1142. run_inv

Source: ControlStack/Scenarios/SC18Logging.lean:207 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (admins : List ℕ) (trusted T : ℕ) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal admins trusted o) (h : Inv trusted T s) : Inv trusted T (run admins trusted T full s ops)
~~~

### 1143. sc18_safe

Source: ControlStack/Scenarios/SC18Logging.lean:219 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc18_safe (admins : List ℕ) (trusted T : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal admins trusted o) : Good T (run admins trusted T full (init trusted) ops)
~~~

### 1144. config_untampered

Source: ControlStack/Scenarios/SC18Logging.lean:225 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem config_untampered (admins : List ℕ) (trusted T : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal admins trusted o) : (run admins trusted T full (init trusted) ops).cfg = trusted
~~~

### 1145. step_halted

Source: ControlStack/Scenarios/SC18Logging.lean:231 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (admins : List ℕ) (trusted T : ℕ) (s : St) (o : Op) (hh : s.halted = true) : (step admins trusted T full s o).released = s.released ∧ (step admins trusted T full s o).halted = true
~~~

### 1146. halt_freezes

Source: ControlStack/Scenarios/SC18Logging.lean:240 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (admins : List ℕ) (trusted T : ℕ) (s : St) (ops : List Op) (hh : s.halted = true) : (run admins trusted T full s ops).released = s.released
~~~

### 1147. released_prefix

Source: ControlStack/Scenarios/SC18Logging.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem released_prefix (admins : List ℕ) (trusted T : ℕ) (C : Checks) (s : St) (o : Op) : s.released <+: (step admins trusted T C s o).released
~~~

### 1148. honest_logged_release

Source: ControlStack/Scenarios/SC18Logging.lean:283 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_logged_release : let s
~~~

### 1149. release_before_log_breaks

Source: ControlStack/Scenarios/SC18Logging.lean:289 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem release_before_log_breaks : let s
~~~

### 1150. agent_writable_config_breaks

Source: ControlStack/Scenarios/SC18Logging.lean:297 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_writable_config_breaks : let s
~~~

### 1151. fail_open_outage_breaks

Source: ControlStack/Scenarios/SC18Logging.lean:304 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fail_open_outage_breaks : (run [9] 0 2 { full with failOpen
~~~

### 1152. watchdog_off_silent_release

Source: ControlStack/Scenarios/SC18Logging.lean:312 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem watchdog_off_silent_release : (run [9] 0 2 { full with watchdog
~~~

### 1153. no_halt_check_breaks

Source: ControlStack/Scenarios/SC18Logging.lean:319 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run [9] 0 2 { full with haltCheck
~~~

## ControlStack/Scenarios/SC18Refinement.lean

### 1154. runC_cons

Source: ControlStack/Scenarios/SC18Refinement.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runC_cons (F : CFlags) (T : ℕ) (s : CSt) (o : COp) (ops : List COp) : runC F T s (o :: ops) = runC F T (stepC F T s o) ops
~~~

### 1155. cinv_init

Source: ControlStack/Scenarios/SC18Refinement.lean:164 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_init : CInv cinit
~~~

### 1156. CInv.ack_seen

Source: ControlStack/Scenarios/SC18Refinement.lean:167 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem CInv.ack_seen {s : CSt} (h : CInv s) {p : ℕ × ℕ} (hp : p ∈ s.ackd) : p.1 ∈ s.seen
~~~

### 1157. cinv_step

Source: ControlStack/Scenarios/SC18Refinement.lean:170 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_step (T : ℕ) (s : CSt) (o : COp) (h : CInv s) : CInv (stepC real T s o)
~~~

### 1158. cinv_run

Source: ControlStack/Scenarios/SC18Refinement.lean:235 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_run (T : ℕ) (s : CSt) (ops : List COp) (h : CInv s) : CInv (runC real T s ops)
~~~

### 1159. simulation

Source: ControlStack/Scenarios/SC18Refinement.lean:255 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation (admins : List ℕ) (T : ℕ) (s : CSt) (o : COp) (h : CInv s) : α T (stepC real T s o) = Resume.run admins T (α T s) (opsOf T s o)
~~~

### 1160. simulation_run

Source: ControlStack/Scenarios/SC18Refinement.lean:310 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation_run (admins : List ℕ) (T : ℕ) (s : CSt) (ops : List COp) (h : CInv s) : α T (runC real T s ops) = Resume.run admins T (α T s) (absTrace T s ops)
~~~

### 1161. concrete_safe

Source: ControlStack/Scenarios/SC18Refinement.lean:327 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_safe (T : ℕ) (ops : List COp) : (∀ r ∈ (runC real T cinit ops).released, Resume.RelOk T (α T (runC real T cinit ops)) r) ∧ ((runC real T cinit ops).released.map SC18.Rel.id).Nodup
~~~

### 1162. concrete_durable

Source: ControlStack/Scenarios/SC18Refinement.lean:338 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_durable (T : ℕ) (ops : List COp) : ∀ r ∈ (runC real T cinit ops).released, r.id ∈ ((runC real T cinit ops).ackd.map Prod.fst).take r.llen ∧ r.id ∈ (runC real T cinit ops).sinkLog ∧ r.clock ≤ r.lastAck + T
~~~

### 1163. fresh_facts

Source: ControlStack/Scenarios/SC18Refinement.lean:351 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fresh_facts {s : CSt} (h : CInv s) {i : ℕ} (hi : i ∉ s.seen) : i ∉ s.sent ∧ i ∉ s.sinkLog ∧ i ∉ s.ackd.map Prod.fst ∧ i ∉ s.failed ∧ i ∉ s.released.map SC18.Rel.id
~~~

### 1164. honest_path

Source: ControlStack/Scenarios/SC18Refinement.lean:363 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_path (T : ℕ) (s : CSt) (i : ℕ) (h : CInv s) (hs : s.serving = true) (hu : s.sinkUp = true) (hi : i ∉ s.seen) : i ∈ (runC real T s [.arrive i, .send i, .commit i, .ack i, .release i]).released.map SC18.Rel.id
~~~

### 1165. resume_then_serve

Source: ControlStack/Scenarios/SC18Refinement.lean:371 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem resume_then_serve (T : ℕ) (s : CSt) (i : ℕ) (h : CInv s) (hu : s.sinkUp = true) (hi : i ∉ s.seen) : i ∈ (runC real T s [.ping, .arrive i, .send i, .commit i, .ack i, .release i]).released.map SC18.Rel.id
~~~

### 1166. honest_path_abstract

Source: ControlStack/Scenarios/SC18Refinement.lean:380 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_path_abstract (T : ℕ) (s : CSt) (i : ℕ) (h : CInv s) (hs : s.serving = true) (hu : s.sinkUp = true) (hi : i ∉ s.seen) : absTrace T s [.arrive i, .send i, .commit i, .ack i, .release i] = [.request i, .logWrite i, .release i]
~~~

### 1167. fail_open_breaks

Source: ControlStack/Scenarios/SC18Refinement.lean:391 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fail_open_breaks : let t
~~~

### 1168. late_reply_breaks_timing

Source: ControlStack/Scenarios/SC18Refinement.lean:402 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem late_reply_breaks_timing : let ops : List COp
~~~

### 1169. pause_resume_witness

Source: ControlStack/Scenarios/SC18Refinement.lean:410 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pause_resume_witness : let pre : List COp
~~~

## ControlStack/Scenarios/SC19Prod.lean

### 1170. run_cons

Source: ControlStack/Scenarios/SC19Prod.lean:141 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 1171. inv_init

Source: ControlStack/Scenarios/SC19Prod.lean:159 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) : Inv E init
~~~

### 1172. Inv.good

Source: ControlStack/Scenarios/SC19Prod.lean:161 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {E : Env} {s : St} (h : Inv E s) : Good E s
~~~

### 1173. inv_mono

Source: ControlStack/Scenarios/SC19Prod.lean:168 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_mono {E : Env} {s t : St} (h : Inv E s) (hs : s.snaps <+: t.snaps) (hv : s.verified ⊆ t.verified) (ha : s.approvals ⊆ t.approvals) (han : ∀ a ∈ t.approvals, a ∉ s.approvals → a.2.1 ∈ E.approvers ∧ a.2.1 ≠ a.2.2) (hd : t.destroyed = s.destroyed) (hdn : t.done = s.done) : Inv E t
~~~

### 1174. inv_same

Source: ControlStack/Scenarios/SC19Prod.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_same {E : Env} {s t : St} (h : Inv E s) (hs : t.snaps = s.snaps) (hv : t.verified = s.verified) (ha : t.approvals = s.approvals) (hd : t.destroyed = s.destroyed) (hdn : t.done = s.done) : Inv E t
~~~

### 1175. step_inv

Source: ControlStack/Scenarios/SC19Prod.lean:191 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o)
~~~

### 1176. run_inv

Source: ControlStack/Scenarios/SC19Prod.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 1177. sc19_safe

Source: ControlStack/Scenarios/SC19Prod.lean:259 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc19_safe (E : Env) (ops : List Op) : Good E (run E full init ops)
~~~

### 1178. step_halted

Source: ControlStack/Scenarios/SC19Prod.lean:263 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s
~~~

### 1179. halt_freezes

Source: ControlStack/Scenarios/SC19Prod.lean:273 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
~~~

### 1180. destroyed_prefix

Source: ControlStack/Scenarios/SC19Prod.lean:280 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem destroyed_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.destroyed <+: (step E C s o).destroyed
~~~

### 1181. honest_destructive_change

Source: ControlStack/Scenarios/SC19Prod.lean:309 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_destructive_change : (run E0 full init [.write 7 5, .snapshot 7, .verify 3 0, .prepare 1 0 7, .approve 2 0, .commit 0 0]).destroyed = [⟨0, 1, 7, 1, 5, 0⟩]
~~~

### 1182. stale_snapshot_breaks

Source: ControlStack/Scenarios/SC19Prod.lean:315 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stale_snapshot_breaks : let ops
~~~

### 1183. unverified_snapshot_breaks

Source: ControlStack/Scenarios/SC19Prod.lean:323 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unverified_snapshot_breaks : (run E0 { full with verified
~~~

### 1184. blast_radius_race_breaks

Source: ControlStack/Scenarios/SC19Prod.lean:330 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem blast_radius_race_breaks : let ops
~~~

### 1185. no_halt_check_breaks

Source: ControlStack/Scenarios/SC19Prod.lean:337 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : let ops
~~~

## ControlStack/Scenarios/SC20Data.lean

### 1186. run_cons

Source: ControlStack/Scenarios/SC20Data.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 1187. inv_init

Source: ControlStack/Scenarios/SC20Data.lean:144 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) : Inv E init
~~~

### 1188. Adm.mono

Source: ControlStack/Scenarios/SC20Data.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Adm.mono {E : Env} {s t : St} (hp : s.promoted ⊆ t.promoted) {i d : ℕ} (h : Adm E s i d) : Adm E t i d
~~~

### 1189. exOf_spec

Source: ControlStack/Scenarios/SC20Data.lean:149 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exOf_spec {s : St} {i : ℕ} {e : Ex} (h : exOf s i = some e) : e.id = i
~~~

### 1190. manifestOf_adm

Source: ControlStack/Scenarios/SC20Data.lean:151 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem manifestOf_adm (E : Env) (s : St) (hi : Inv E s) (ids : List ℕ) : ∀ q ∈ manifestOf E full s ids, Adm E s q.1 q.2
~~~

### 1191. step_inv

Source: ControlStack/Scenarios/SC20Data.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o)
~~~

### 1192. run_inv

Source: ControlStack/Scenarios/SC20Data.lean:238 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 1193. sc20_safe

Source: ControlStack/Scenarios/SC20Data.lean:247 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc20_safe (E : Env) (ops : List Op) : Good E (run E full init ops)
~~~

### 1194. step_halted

Source: ControlStack/Scenarios/SC20Data.lean:249 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s
~~~

### 1195. halt_freezes

Source: ControlStack/Scenarios/SC20Data.lean:259 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
~~~

### 1196. trained_prefix

Source: ControlStack/Scenarios/SC20Data.lean:264 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem trained_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.trained <+: (step E C s o).trained
~~~

### 1197. honest_training

Source: ControlStack/Scenarios/SC20Data.lean:293 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_training : (run E0 full init [.ingest 50 0 7, .freeze 9 [0], .train]).trained = [[(0, 7)]]
~~~

### 1198. reviewed_promotion

Source: ControlStack/Scenarios/SC20Data.lean:298 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reviewed_promotion : (run E0 full init [.agentWrite 1 1 66, .promote 2 1, .freeze 9 [1], .train]).trained = [[(1, 66)]]
~~~

### 1199. no_quarantine_breaks

Source: ControlStack/Scenarios/SC20Data.lean:303 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_quarantine_breaks : (run E0 { full with quarantine
~~~

### 1200. edit_after_freeze_breaks

Source: ControlStack/Scenarios/SC20Data.lean:310 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem edit_after_freeze_breaks : (run E0 { full with recheck
~~~

### 1201. unlisted_source_breaks

Source: ControlStack/Scenarios/SC20Data.lean:317 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unlisted_source_breaks : (run E0 { full with sourceCheck
~~~

### 1202. self_promotion_refused

Source: ControlStack/Scenarios/SC20Data.lean:323 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem self_promotion_refused : (run E0 full init [.agentWrite 2 1 66, .promote 2 1]).promoted = []
~~~

### 1203. no_halt_check_breaks

Source: ControlStack/Scenarios/SC20Data.lean:328 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run E0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC23Injection.lean

### 1204. run_cons

Source: ControlStack/Scenarios/SC23Injection.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (P : Policy) (C : Checks) (s : St) (o : Op) (ops : List Op) : run P C s (o :: ops) = run P C (step P C s o) ops
~~~

### 1205. inv_init

Source: ControlStack/Scenarios/SC23Injection.lean:158 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (P : Policy) : Inv P init
~~~

### 1206. Inv.good

Source: ControlStack/Scenarios/SC23Injection.lean:160 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {P : Policy} {s : St} (hi : Inv P s) : Good P s
~~~

### 1207. argsOf_mem

Source: ControlStack/Scenarios/SC23Injection.lean:165 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem argsOf_mem {s : St} {args : List ℕ} {x : Val} (h : x ∈ argsOf s args) : x ∈ s.store
~~~

### 1208. anyLabel_eq

Source: ControlStack/Scenarios/SC23Injection.lean:169 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem anyLabel_eq {xs : List Val} (h : ∀ x ∈ xs, x.label = x.prov) : anyLabel xs = anyProv xs
~~~

### 1209. inv_of_mono

Source: ControlStack/Scenarios/SC23Injection.lean:177 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_of_mono {P : Policy} {s t : St} (hi : Inv P s) (hst : ∀ x ∈ t.store, x.label = x.prov) (hc : s.confs ⊆ t.confs) (hcn : ∀ cf ∈ t.confs, cf.by_ ∈ P.users) (he : t.executed = s.executed) (hu : t.used = s.used) : Inv P t
~~~

### 1210. store_append

Source: ControlStack/Scenarios/SC23Injection.lean:186 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem store_append {P : Policy} {s : St} (hi : Inv P s) (x : Val) (hx : x.label = x.prov) : Inv P { s with store
~~~

### 1211. exec_free

Source: ControlStack/Scenarios/SC23Injection.lean:193 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exec_free {P : Policy} {s : St} (hi : Inv P s) (tool : ℕ) (args : List ℕ) (hc : tool ∉ P.sensitive ∨ anyLabel (argsOf s args) = false) : Inv P (doExec s ⟨tool, (argsOf s args).map Val.v, anyProv (argsOf s args), none⟩ [])
~~~

### 1212. exec_conf

Source: ControlStack/Scenarios/SC23Injection.lean:214 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exec_conf {P : Policy} {s : St} (hi : Inv P s) (tool : ℕ) (args : List ℕ) (n : ℕ) (cf : Conf) (hcf : confOf s n = some cf) (ht : cf.tool = tool) (hv : cf.vals = (argsOf s args).map Val.v) (hu : n ∉ s.used) : Inv P (doExec s ⟨tool, (argsOf s args).map Val.v, anyProv (argsOf s args), some n⟩ [n])
~~~

### 1213. step_inv

Source: ControlStack/Scenarios/SC23Injection.lean:236 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (P : Policy) (s : St) (o : Op) (hi : Inv P s) : Inv P (step P full s o)
~~~

### 1214. run_inv

Source: ControlStack/Scenarios/SC23Injection.lean:292 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (P : Policy) (s : St) (ops : List Op) (hi : Inv P s) : Inv P (run P full s ops)
~~~

### 1215. sc23_safe

Source: ControlStack/Scenarios/SC23Injection.lean:300 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc23_safe (P : Policy) (ops : List Op) : Good P (run P full init ops)
~~~

### 1216. step_halted

Source: ControlStack/Scenarios/SC23Injection.lean:305 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (P : Policy) (s : St) (o : Op) (hh : s.halted = true) : step P full s o = s
~~~

### 1217. halt_freezes

Source: ControlStack/Scenarios/SC23Injection.lean:315 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (P : Policy) (s : St) (ops : List Op) (hh : s.halted = true) : run P full s ops = s
~~~

### 1218. executed_prefix

Source: ControlStack/Scenarios/SC23Injection.lean:322 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem executed_prefix (P : Policy) (C : Checks) (s : St) (o : Op) : s.executed <+: (step P C s o).executed
~~~

### 1219. honest_untainted

Source: ControlStack/Scenarios/SC23Injection.lean:351 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_untainted : (run P0 full init [.userInput 0 42, .act 5 [0] 0]).executed = [⟨5, [42], false, none⟩]
~~~

### 1220. honest_confirmed

Source: ControlStack/Scenarios/SC23Injection.lean:356 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_confirmed : (run P0 full init [.toolResult 0 66, .confirm 1 7 5 [66], .act 5 [0] 7]).executed = [⟨5, [66], true, some 7⟩]
~~~

### 1221. tainted_unconfirmed_blocked

Source: ControlStack/Scenarios/SC23Injection.lean:361 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tainted_unconfirmed_blocked : (run P0 full init [.toolResult 0 66, .act 5 [0] 0]).executed = []
~~~

### 1222. summarizer_drops_taint

Source: ControlStack/Scenarios/SC23Injection.lean:367 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem summarizer_drops_taint : (run P0 { full with propagate
~~~

### 1223. paraphrase_confirmation_breaks

Source: ControlStack/Scenarios/SC23Injection.lean:374 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem paraphrase_confirmation_breaks : let s
~~~

### 1224. no_taint_check_breaks

Source: ControlStack/Scenarios/SC23Injection.lean:381 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_taint_check_breaks : (run P0 { full with taintCheck
~~~

### 1225. confirmation_reuse_breaks

Source: ControlStack/Scenarios/SC23Injection.lean:387 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem confirmation_reuse_breaks : (run P0 { full with oneUse
~~~

### 1226. non_user_confirmation_refused

Source: ControlStack/Scenarios/SC23Injection.lean:396 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem non_user_confirmation_refused : (run P0 full init [.toolResult 0 66, .confirm 2 7 5 [66], .act 5 [0] 7]).executed = []
~~~

## ControlStack/Scenarios/SC23Isolation.lean

### 1227. run_cons

Source: ControlStack/Scenarios/SC23Isolation.lean:156 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 1228. step_rel

Source: ControlStack/Scenarios/SC23Isolation.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_rel (E : Env) (s t : St) (o o' : Op) (ho : SameExceptContent o o') (h : Rel s t) : Rel (step E full s o) (step E full t o')
~~~

### 1229. noninterference

Source: ControlStack/Scenarios/SC23Isolation.lean:235 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem noninterference (E : Env) (ops ops' : List Op) (h : List.Forall₂ SameExceptContent ops ops') : Rel (run E full init ops) (run E full init ops')
~~~

### 1230. derive_ignores_tool_content

Source: ControlStack/Scenarios/SC23Isolation.lean:244 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem derive_ignores_tool_content (E : Env) (v : ℕ) : (run E full init [.toolResult v, .derive]).pvals = [.handle 0, .trusted (E.plan [] 1)]
~~~

### 1231. inv_init

Source: ControlStack/Scenarios/SC23Isolation.lean:258 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) : Inv E init
~~~

### 1232. ActOk.mono

Source: ControlStack/Scenarios/SC23Isolation.lean:260 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ActOk.mono {E : Env} {s t : St} (h : s.confs ⊆ t.confs) {x : Act} (hx : ActOk E s x) : ActOk E t x
~~~

### 1233. exec_append

Source: ControlStack/Scenarios/SC23Isolation.lean:265 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exec_append {E : Env} {s : St} (h : Inv E s) (x : Act) (hx : ActOk E s x) : Inv E { s with executed
~~~

### 1234. step_inv

Source: ControlStack/Scenarios/SC23Isolation.lean:272 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o)
~~~

### 1235. run_inv

Source: ControlStack/Scenarios/SC23Isolation.lean:306 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 1236. sc23_isolated_safe

Source: ControlStack/Scenarios/SC23Isolation.lean:314 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc23_isolated_safe (E : Env) (ops : List Op) : ∀ x ∈ (run E full init ops).executed, ActOk E (run E full init ops) x
~~~

### 1237. step_halted

Source: ControlStack/Scenarios/SC23Isolation.lean:317 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s
~~~

### 1238. halt_freezes

Source: ControlStack/Scenarios/SC23Isolation.lean:327 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
~~~

### 1239. executed_prefix

Source: ControlStack/Scenarios/SC23Isolation.lean:332 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem executed_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.executed <+: (step E C s o).executed
~~~

### 1240. honest_untainted

Source: ControlStack/Scenarios/SC23Isolation.lean:361 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_untainted : (run E0 full init [.userInput 42, .act 5 [0] 0]).executed = [⟨5, [42], false, none⟩]
~~~

### 1241. honest_confirmed

Source: ControlStack/Scenarios/SC23Isolation.lean:366 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_confirmed : (run E0 full init [.toolResult 66, .confirm 1 7 5 [66], .act 5 [0] 7]).executed = [⟨5, [66], true, some 7⟩]
~~~

### 1242. tainted_unconfirmed_blocked

Source: ControlStack/Scenarios/SC23Isolation.lean:371 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tainted_unconfirmed_blocked : (run E0 full init [.toolResult 66, .act 5 [0] 0]).executed = []
~~~

### 1243. w1_impossible

Source: ControlStack/Scenarios/SC23Isolation.lean:376 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w1_impossible : (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed = (run E0 full init [.toolResult 0, .derive, .act 5 [1] 0]).executed ∧ (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed = [⟨5, [41], false, none⟩]
~~~

### 1244. no_isolation_launders

Source: ControlStack/Scenarios/SC23Isolation.lean:384 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_isolation_launders : (run E0 { full with isolation
~~~

## ControlStack/Scenarios/SC23IsolationV2.lean

### 1245. run_cons

Source: ControlStack/Scenarios/SC23IsolationV2.lean:154 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 1246. raw_run

Source: ControlStack/Scenarios/SC23IsolationV2.lean:160 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem raw_run (E : Env) (s : St) (ops : List Op) : (raw E).run s ops = run E full s ops
~~~

### 1247. view_full

Source: ControlStack/Scenarios/SC23IsolationV2.lean:179 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem view_full (s : St) : view full s = s.pvals
~~~

### 1248. step_rel_same

Source: ControlStack/Scenarios/SC23IsolationV2.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_rel_same (E : Env) (s t : St) (o : Op) (h : Rel s t) : Rel (step E full s o) (step E full t o)
~~~

### 1249. step_rel

Source: ControlStack/Scenarios/SC23IsolationV2.lean:231 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_rel (E : Env) (s t : St) (o o' : Op) (ho : SameExceptContent o o') (h : Rel s t) : Rel (step E full s o) (step E full t o')
~~~

### 1250. run_rel

Source: ControlStack/Scenarios/SC23IsolationV2.lean:241 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_rel (E : Env) (ops ops' : List Op) (h : List.Forall₂ SameExceptContent ops ops') : ∀ s t, Rel s t → Rel (run E full s ops) (run E full t ops')
~~~

### 1251. noninterference

Source: ControlStack/Scenarios/SC23IsolationV2.lean:248 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem noninterference (E : Env) (ops ops' : List Op) (h : List.Forall₂ SameExceptContent ops ops') : Rel (run E full init ops) (run E full init ops')
~~~

### 1252. claim_same

Source: ControlStack/Scenarios/SC23IsolationV2.lean:252 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_same {o o' : Op} (h : SameExceptContent o o') : claim o = claim o'
~~~

### 1253. noninterference_authed

Source: ControlStack/Scenarios/SC23IsolationV2.lean:272 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem noninterference_authed (E : Env) (ops ops' : List (ℕ × Op)) (h : List.Forall₂ (fun io io' => io.1 = io'.1 ∧ SameExceptContent io.2 io'.2) ops ops') : Rel ((authed (raw E) claim).run init ops) ((authed (raw E) claim).run init ops')
~~~

### 1254. inv_init

Source: ControlStack/Scenarios/SC23IsolationV2.lean:288 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) : Inv E init
~~~

### 1255. ActOk.mono

Source: ControlStack/Scenarios/SC23IsolationV2.lean:290 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ActOk.mono {E : Env} {s t : St} (h : s.confs ⊆ t.confs) {x : Act} (hx : ActOk E s x) : ActOk E t x
~~~

### 1256. exec_append

Source: ControlStack/Scenarios/SC23IsolationV2.lean:295 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exec_append {E : Env} {s : St} (h : Inv E s) (x : Act) (hx : ActOk E s x) : Inv E { s with executed
~~~

### 1257. step_inv

Source: ControlStack/Scenarios/SC23IsolationV2.lean:302 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o)
~~~

### 1258. run_inv

Source: ControlStack/Scenarios/SC23IsolationV2.lean:336 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 1259. step_confs

Source: ControlStack/Scenarios/SC23IsolationV2.lean:342 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_confs (E : Env) (s : St) (o : Op) (x : Conf) (hx : x ∈ (step E full s o).confs) : x ∈ s.confs ∨ o = .confirm x.by_ x.n x.tool x.vals
~~~

### 1260. run_confs

Source: ControlStack/Scenarios/SC23IsolationV2.lean:359 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_confs (E : Env) (ops : List Op) (s : St) (x : Conf) (hx : x ∈ (run E full s ops).confs) : x ∈ s.confs ∨ Op.confirm x.by_ x.n x.tool x.vals ∈ ops
~~~

### 1261. sc23v2_safe_authenticated

Source: ControlStack/Scenarios/SC23IsolationV2.lean:374 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc23v2_safe_authenticated (E : Env) (U : List ℕ) (hU : ∀ u ∈ U, u ∉ E.users) (ops : List (ℕ × Op)) : ∀ x ∈ ((authed (raw E) claim).run init ops).executed, x.tool ∈ E.sensitive → x.tainted = true → ∃ c n, c ∈ E.users ∧ c ∉ U ∧ (c, Op.confirm c n x.tool x.vals) ∈ ops
~~~

### 1262. step_halted

Source: ControlStack/Scenarios/SC23IsolationV2.lean:387 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s
~~~

### 1263. halt_freezes

Source: ControlStack/Scenarios/SC23IsolationV2.lean:397 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
~~~

### 1264. executed_prefix

Source: ControlStack/Scenarios/SC23IsolationV2.lean:402 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem executed_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.executed <+: (step E C s o).executed
~~~

### 1265. honest_planner_reads_state

Source: ControlStack/Scenarios/SC23IsolationV2.lean:436 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_planner_reads_state : (run E0 full init [.userInput 1 40, .userInput 1 2, .derive, .act 5 [2] 0]).executed = [⟨5, [42], false, none⟩]
~~~

### 1266. w1_impossible_v2

Source: ControlStack/Scenarios/SC23IsolationV2.lean:442 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w1_impossible_v2 : (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed = (run E0 full init [.toolResult 0, .derive, .act 5 [1] 0]).executed ∧ (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed = [⟨5, [0], false, none⟩]
~~~

### 1267. leaky_view_launders

Source: ControlStack/Scenarios/SC23IsolationV2.lean:450 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem leaky_view_launders : (run E0 { full with opaqueView
~~~

### 1268. forged_confirmation_without_auth

Source: ControlStack/Scenarios/SC23IsolationV2.lean:460 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forged_confirmation_without_auth : ((authed (raw E0) (fun _ => none)).run init forged).executed = [⟨5, [66], true, some 7⟩] ∧ ((authed (raw E0) claim).run init forged).executed = []
~~~

## ControlStack/Scenarios/SC25Audit.lean

### 1269. run_cons

Source: ControlStack/Scenarios/SC25Audit.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (C : Checks) (s : St) (o : Op) (ops : List Op) : run R h cls C s (o :: ops) = run R h cls C (step R h cls C s o) ops
~~~

### 1270. inv_init

Source: ControlStack/Scenarios/SC25Audit.lean:196 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) : Inv R h cls init
~~~

### 1271. Inv.good

Source: ControlStack/Scenarios/SC25Audit.lean:199 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s : St} (hi : Inv R h cls s) : Good R h cls s
~~~

### 1272. take_prefix

Source: ControlStack/Scenarios/SC25Audit.lean:206 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem take_prefix {α : Type} {l m : List α} (hp : l <+: m) {n : ℕ} (hn : n ≤ l.length) : m.take n = l.take n
~~~

### 1273. inv_of_mono

Source: ControlStack/Scenarios/SC25Audit.lean:211 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_of_mono {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s t : St} (hi : Inv R h cls s) (hv : s.verdicts <+: t.verdicts) (ha : s.approvals <+: t.approvals) (hvn : ∀ v ∈ t.verdicts, v ∉ s.verdicts → ∃ a, v.by_ = some a ∧ a ∈ R.auditors) (han : ∀ ap ∈ t.approvals, ap ∉ s.approvals → ap.approver ∈ R.approvers) (he : t.executed = s.executed) : Inv R h cls t
~~~

### 1274. mono_same

Source: ControlStack/Scenarios/SC25Audit.lean:229 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mono_same {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s t : St} (hi : Inv R h cls s) (hv : t.verdicts = s.verdicts) (ha : t.approvals = s.approvals) (he : t.executed = s.executed) : Inv R h cls t
~~~

### 1275. audit_inv

Source: ControlStack/Scenarios/SC25Audit.lean:235 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem audit_inv {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s : St} (hi : Inv R h cls s) (v : Verdict) (hv : ∃ a, v.by_ = some a ∧ a ∈ R.auditors) : Inv R h cls { s with verdicts
~~~

### 1276. approve_inv

Source: ControlStack/Scenarios/SC25Audit.lean:243 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem approve_inv {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s : St} (hi : Inv R h cls s) (ap : Appr) (ha : ap.approver ∈ R.approvers) : Inv R h cls { s with approvals
~~~

### 1277. itemOf_id

Source: ControlStack/Scenarios/SC25Audit.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem itemOf_id {s : St} {id : ℕ} {it : Item} (h : itemOf s id = some it) : it.id = id
~~~

### 1278. fire_inv

Source: ControlStack/Scenarios/SC25Audit.lean:254 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fire_inv {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s : St} (hi : Inv R h cls s) (id : ℕ) (it : Item) (hit : itemOf s id = some it) (hn : id ∉ s.executed.map Exec.id) (hval : Valid h cls full s it) : Inv R h cls { s with executed
~~~

### 1279. step_inv

Source: ControlStack/Scenarios/SC25Audit.lean:279 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) (hi : Inv R h cls s) : Inv R h cls (step R h cls full s o)
~~~

### 1280. run_inv

Source: ControlStack/Scenarios/SC25Audit.lean:304 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List Op) (hi : Inv R h cls s) : Inv R h cls (run R h cls full s ops)
~~~

### 1281. sc25_safe

Source: ControlStack/Scenarios/SC25Audit.lean:314 | Family: F6 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc25_safe (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) : Good R h cls (run R h cls full init ops)
~~~

### 1282. step_expired

Source: ControlStack/Scenarios/SC25Audit.lean:320 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_expired (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) (id : ℕ) (hx : id ∈ s.expired) (hn : id ∉ s.executed.map Exec.id) : id ∈ (step R h cls full s o).expired ∧ id ∉ (step R h cls full s o).executed.map Exec.id
~~~

### 1283. expired_never_executes

Source: ControlStack/Scenarios/SC25Audit.lean:345 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem expired_never_executes (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List Op) (id : ℕ) (hx : id ∈ s.expired) (hn : id ∉ s.executed.map Exec.id) : id ∉ (run R h cls full s ops).executed.map Exec.id
~~~

### 1284. step_halted

Source: ControlStack/Scenarios/SC25Audit.lean:355 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) (hh : s.halted = true) : (step R h cls full s o).executed = s.executed ∧ (step R h cls full s o).halted = true
~~~

### 1285. halt_freezes

Source: ControlStack/Scenarios/SC25Audit.lean:363 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List Op) (hh : s.halted = true) : (run R h cls full s ops).executed = s.executed
~~~

### 1286. executed_prefix

Source: ControlStack/Scenarios/SC25Audit.lean:374 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem executed_prefix (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (C : Checks) (s : St) (o : Op) : s.executed <+: (step R h cls C s o).executed
~~~

### 1287. honest_reversible

Source: ControlStack/Scenarios/SC25Audit.lean:407 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_reversible : ((run R0 id cls0 full init [.submit 1 0 7 false, .audit 2 0 true, .check 0, .fire 0]).executed.map Exec.content) = [7]
~~~

### 1288. honest_irreversible_with_crash

Source: ControlStack/Scenarios/SC25Audit.lean:414 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_irreversible_with_crash : ((run R0 id cls0 full init [.submit 1 0 100 true, .audit 2 0 true, .approve 3 0, .check 0, .crash, .fire 0, .check 0, .fire 0, .fire 0]).executed.map Exec.content) = [100]
~~~

### 1289. audit_fail_blocks

Source: ControlStack/Scenarios/SC25Audit.lean:420 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem audit_fail_blocks : (run R0 id cls0 full init [.submit 1 0 7 false, .audit 2 0 false, .check 0, .fire 0]).executed = []
~~~

### 1290. fail_open_timeout_breaks

Source: ControlStack/Scenarios/SC25Audit.lean:426 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fail_open_timeout_breaks : let s
~~~

### 1291. digest_unchecked_breaks

Source: ControlStack/Scenarios/SC25Audit.lean:433 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem digest_unchecked_breaks : let s
~~~

### 1292. nonatomic_check_race_breaks

Source: ControlStack/Scenarios/SC25Audit.lean:441 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nonatomic_check_race_breaks : (run R0 id cls0 { full with atomic
~~~

### 1293. agent_declared_class_breaks

Source: ControlStack/Scenarios/SC25Audit.lean:450 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_declared_class_breaks : let s
~~~

### 1294. no_halt_check_breaks

Source: ControlStack/Scenarios/SC25Audit.lean:458 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run R0 id cls0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC25Content.lean

### 1295. gfold_fst

Source: ControlStack/Scenarios/SC25Content.lean:52 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gfold_fst (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) (sg : St × List ARec) : (ops.foldl (gstep R h cls) sg).1 = run R h cls full sg.1 ops
~~~

### 1296. grun_fst

Source: ControlStack/Scenarios/SC25Content.lean:59 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem grun_fst (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) : (grun R h cls ops).1 = run R h cls full init ops
~~~

### 1297. mem_of_itemOf

Source: ControlStack/Scenarios/SC25Content.lean:62 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mem_of_itemOf {s : St} {id : ℕ} {it : Item} (hi : itemOf s id = some it) : it ∈ s.queue
~~~

### 1298. queue_mono

Source: ControlStack/Scenarios/SC25Content.lean:66 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem queue_mono (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) : ∀ it ∈ s.queue, it ∈ (step R h cls full s o).queue
~~~

### 1299. verdict_step

Source: ControlStack/Scenarios/SC25Content.lean:72 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem verdict_step (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) : ∀ v ∈ (step R h cls full s o).verdicts, v ∈ s.verdicts ∨ ∃ x ∈ auditRec R s o, x.1 = v.id ∧ h x.2.1 = v.d ∧ x.2.2.1 = v.pass ∧ v.by_ = some x.2.2.2
~~~

### 1300. auditRec_in_queue

Source: ControlStack/Scenarios/SC25Content.lean:80 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem auditRec_in_queue (R : Roles) (s : St) (o : Op) : ∀ x ∈ auditRec R s o, ∃ it ∈ s.queue, it.content = x.2.1
~~~

### 1301. executed_step

Source: ControlStack/Scenarios/SC25Content.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem executed_step (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) : ∀ e ∈ (step R h cls full s o).executed, e ∈ s.executed ∨ ∃ it ∈ s.queue, it.content = e.content
~~~

### 1302. J_step

Source: ControlStack/Scenarios/SC25Content.lean:103 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem J_step (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (g : List ARec) (o : Op) (hJ : J h s g) : J h (step R h cls full s o) (g ++ auditRec R s o) where verd v hv
~~~

### 1303. J_fold

Source: ControlStack/Scenarios/SC25Content.lean:122 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem J_fold (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) (sg : St × List ARec) (hJ : J h sg.1 sg.2) : J h (ops.foldl (gstep R h cls) sg).1 (ops.foldl (gstep R h cls) sg).2
~~~

### 1304. J_grun

Source: ControlStack/Scenarios/SC25Content.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem J_grun (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) : J h (grun R h cls ops).1 (grun R h cls ops).2
~~~

### 1305. ghost_in_queue

Source: ControlStack/Scenarios/SC25Content.lean:133 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ghost_in_queue (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) : ∀ x ∈ (grun R h cls ops).2, ∃ it ∈ (run R h cls full init ops).queue, it.content = x.2.1
~~~

### 1306. executed_in_queue

Source: ControlStack/Scenarios/SC25Content.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem executed_in_queue (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) : ∀ e ∈ (run R h cls full init ops).executed, ∃ it ∈ (run R h cls full init ops).queue, it.content = e.content
~~~

### 1307. sc25_content_safe

Source: ControlStack/Scenarios/SC25Content.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc25_content_safe (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) (hinj : Set.InjOn h {c | ∃ it ∈ (run R h cls full init ops).queue, it.content = c}) : ∀ e ∈ (run R h cls full init ops).executed, ∃ x ∈ (grun R h cls ops).2, x.1 = e.id ∧ x.2.1 = e.content ∧ x.2.2.1 = true ∧ x.2.2.2 ∈ R.auditors
~~~

### 1308. digest_only_executes_unaudited

Source: ControlStack/Scenarios/SC25Content.lean:165 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem digest_only_executes_unaudited : let ops : List Op
~~~

## ControlStack/Scenarios/SC25Refinement.lean

### 1309. valid_iff

Source: ControlStack/Scenarios/SC25Refinement.lean:201 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem valid_iff (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (it : CItem) : Valid h cls full (α s) (toItem it) ↔ ValidC h cls s it (h it.content)
~~~

### 1310. exec_ids

Source: ControlStack/Scenarios/SC25Refinement.lean:214 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exec_ids (s : CSt) : (α s).executed.map Exec.id = s.effects.map ERow.id
~~~

### 1311. verdict_ex

Source: ControlStack/Scenarios/SC25Refinement.lean:217 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem verdict_ex (s : CSt) (id : ℕ) : (∃ v ∈ (α s).verdicts, v.id = id) ↔ ∃ v ∈ s.auditLog, v.id = id
~~~

### 1312. step_check_valid

Source: ControlStack/Scenarios/SC25Refinement.lean:220 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_check_valid (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (id : ℕ) (it : CItem) (hn : (α s).halted = false) (hi : citemOf s id = some it) (hv : Valid h cls full (α s) (toItem it)) : step R h cls full (α s) (.check id) = { α s with checked
~~~

### 1313. step_fire_valid

Source: ControlStack/Scenarios/SC25Refinement.lean:230 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_fire_valid (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (id : ℕ) (it : CItem) (hn : (α s).halted = false) (hi : citemOf s id = some it) (hv : Valid h cls full (α s) (toItem it)) (hx : id ∉ s.effects.map ERow.id) : step R h cls full { α s with checked
~~~

### 1314. simulation

Source: ControlStack/Scenarios/SC25Refinement.lean:247 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (o : COp) : α (stepC R h cls false s o) = run R h cls full (α s) (opsOf h cls s o)
~~~

### 1315. simulation_run

Source: ControlStack/Scenarios/SC25Refinement.lean:350 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation_run (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (ops : List COp) : α (runC R h cls false s ops) = run R h cls full (α s) (absTrace h cls R s ops)
~~~

### 1316. concrete_safe

Source: ControlStack/Scenarios/SC25Refinement.lean:365 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_safe (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp) : Good R h cls (α (runC R h cls false cinit ops))
~~~

### 1317. cinv_init

Source: ControlStack/Scenarios/SC25Refinement.lean:378 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_init (h : ℕ → ℕ) : CInv h cinit
~~~

### 1318. citemOf_mem

Source: ControlStack/Scenarios/SC25Refinement.lean:380 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem citemOf_mem {s : CSt} {id : ℕ} {it : CItem} (hi : citemOf s id = some it) : it ∈ s.items
~~~

### 1319. cinv_step

Source: ControlStack/Scenarios/SC25Refinement.lean:383 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_step (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (o : COp) (hs : CInv h s) : CInv h (stepC R h cls false s o)
~~~

### 1320. cinv_run

Source: ControlStack/Scenarios/SC25Refinement.lean:431 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_run (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (ops : List COp) (hs : CInv h s) : CInv h (runC R h cls false s ops)
~~~

### 1321. concrete_content_safe

Source: ControlStack/Scenarios/SC25Refinement.lean:439 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_content_safe (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp) (hinj : Set.InjOn h {c | ∃ it ∈ (runC R h cls false cinit ops).items, it.content = c}) : ∀ e ∈ (runC R h cls false cinit ops).effects, ∃ a ∈ (runC R h cls false cinit ops).auditLog, a.id = e.id ∧ a.content = e.content ∧ a.pass = true ∧ a.by_ ∈ R.auditors
~~~

### 1322. cached_digest_breaks

Source: ControlStack/Scenarios/SC25Refinement.lean:460 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cached_digest_breaks : let ops
~~~

### 1323. honest_concrete

Source: ControlStack/Scenarios/SC25Refinement.lean:479 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_concrete : (runC R0 id cls0 false cinit [.submit 1 0 7 false, .audit 2 0 true, .fire 0, .submit 1 1 100 true, .audit 2 1 true, .approve 3 1, .crash, .restart, .fire 1]).effects.map ERow.content = [7, 100]
~~~

## ControlStack/Scenarios/SC26Authenticated.lean

### 1324. raw_run

Source: ControlStack/Scenarios/SC26Authenticated.lean:34 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem raw_run (R : Roles) (cap : ℕ) (s : St) (ops : List Op) : (raw R cap).run s ops = run R cap full s ops
~~~

### 1325. step_approvals

Source: ControlStack/Scenarios/SC26Authenticated.lean:47 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_approvals (R : Roles) (cap : ℕ) (s : St) (o : Op) (x : ℕ × ℕ × Tx) (hx : x ∈ (step R cap full s o).approvals) : x ∈ s.approvals ∨ o = .approve x.2.1 x.1 x.2.2
~~~

### 1326. run_approvals

Source: ControlStack/Scenarios/SC26Authenticated.lean:52 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_approvals (R : Roles) (cap : ℕ) (ops : List Op) (s : St) (x : ℕ × ℕ × Tx) (hx : x ∈ (run R cap full s ops).approvals) : x ∈ s.approvals ∨ Op.approve x.2.1 x.1 x.2.2 ∈ ops
~~~

### 1327. sc26_safe_authenticated

Source: ControlStack/Scenarios/SC26Authenticated.lean:65 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc26_safe_authenticated (R : Roles) (cap : ℕ) (U : List ℕ) (ops : List (ℕ × Op)) (hU : ∀ u ∈ U, u ∉ R.approvers) (hgate : ∀ io ∈ ops, ∀ c k tx, io.2 = .bankCall c k tx → io.1 ≠ R.gate) : Good R cap ((authed (raw R cap) claim).run init ops) ∧ ∀ e ∈ ((authed (raw R cap) claim).run init ops).bank, ∃ a, a ∈ R.approvers ∧ a ∉ U ∧ (a, Op.approve a e.1 e.2) ∈ ops
~~~

### 1328. forged_approval_pays_without_auth

Source: ControlStack/Scenarios/SC26Authenticated.lean:95 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forged_approval_pays_without_auth : ((authed (raw R0 20) (fun _ => none)).run init forged).bank = [(0, tx1)] ∧ (¬ ∃ a ∈ R0.approvers, (a, Op.approve a 0 tx1) ∈ forged) ∧ ((authed (raw R0 20) claim).run init forged).bank = []
~~~

## ControlStack/Scenarios/SC26Liveness.lean

### 1329. Mono.refl

Source: ControlStack/Scenarios/SC26Liveness.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Mono.refl (s : St) : Mono s s
~~~

### 1330. Mono.trans

Source: ControlStack/Scenarios/SC26Liveness.lean:53 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Mono.trans {s t u : St} (h1 : Mono s t) (h2 : Mono t u) : Mono s u
~~~

### 1331. bankAppend_mono

Source: ControlStack/Scenarios/SC26Liveness.lean:57 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bankAppend_mono (C : Checks) (s : St) (k : ℕ) (tx : Tx) : Mono s (bankAppend C s k tx)
~~~

### 1332. step_mono

Source: ControlStack/Scenarios/SC26Liveness.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_mono (R : Roles) (cap : ℕ) (s : St) (o : Op) : Mono s (step R cap full s o)
~~~

### 1333. run_mono

Source: ControlStack/Scenarios/SC26Liveness.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_mono (R : Roles) (cap : ℕ) (s : St) (ops : List Op) : Mono s (run R cap full s ops)
~~~

### 1334. Mono.reqOf

Source: ControlStack/Scenarios/SC26Liveness.lean:101 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Mono.reqOf {s t : St} (h : Mono s t) {k : ℕ} {r : Req} (hr : reqOf s k = some r) : reqOf t k = some r
~~~

### 1335. not_halted_of

Source: ControlStack/Scenarios/SC26Liveness.lean:107 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem not_halted_of {s t : St} (h : Mono s t) (ht : t.halted = false) : s.halted = false
~~~

### 1336. execute_reserves

Source: ControlStack/Scenarios/SC26Liveness.lean:114 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem execute_reserves (R : Roles) (cap : ℕ) (s : St) (c k : ℕ) (r : Req) (hh : s.halted = false) (hr : reqOf s k = some r) (happ : ∃ ap ∈ s.approvals, ap.1 = k) (hok : ¬ (k ∉ s.reserved ∧ cap < s.spent + r.tx.amount)) : k ∈ (step R cap full s (.execute c k)).reserved
~~~

### 1337. deliver_sends

Source: ControlStack/Scenarios/SC26Liveness.lean:126 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deliver_sends (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req) (hh : s.halted = false) (hk : k ∈ s.reserved) (hr : reqOf s k = some r) : (k, r.tx) ∈ (step R cap full s (.deliver k)).net
~~~

### 1338. arrive_pays

Source: ControlStack/Scenarios/SC26Liveness.lean:130 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem arrive_pays (R : Roles) (cap : ℕ) (s : St) (h : Inv R cap s) (k : ℕ) (r : Req) (tx : Tx) (hm : (k, tx) ∈ s.net) (hr : reqOf s k = some r) : (k, r.tx) ∈ (step R cap full s (.arrive k)).bank
~~~

### 1339. honest_progress

Source: ControlStack/Scenarios/SC26Liveness.lean:156 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_progress (R : Roles) (cap : ℕ) (s : St) (h : Inv R cap s) (c k : ℕ) (r : Req) (hh : s.halted = false) (hr : reqOf s k = some r) (happ : Approved R s k r) (_hres : k ∉ s.reserved) (hcap : s.spent + r.tx.amount ≤ cap) : (k, r.tx) ∈ (run R cap full s [.execute c k, .deliver k, .arrive k]).bank
~~~

### 1340. paid_once

Source: ControlStack/Scenarios/SC26Liveness.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem paid_once (R : Roles) (cap : ℕ) (s : St) (h : Inv R cap s) (k : ℕ) (tx : Tx) (hk : (k, tx) ∈ s.bank) : (s.bank.map Prod.fst).count k = 1
~~~

### 1341. progress_interleaved

Source: ControlStack/Scenarios/SC26Liveness.lean:181 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem progress_interleaved (R : Roles) (cap : ℕ) (s : St) (h : Inv R cap s) (c k : ℕ) (r : Req) (hr : reqOf s k = some r) (happ : Approved R s k r) (a0 a1 a2 a3 : List Op) (hleg : ∀ o ∈ a0 ++ a1 ++ a2 ++ a3, legal R o) : let t
~~~

### 1342. halted_blocks

Source: ControlStack/Scenarios/SC26Liveness.lean:240 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halted_blocks (R : Roles) (cap : ℕ) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) (hh : s.halted = true) (k : ℕ) (hb : k ∉ s.bank.map Prod.fst) (hn : k ∉ s.net.map Prod.fst) : k ∉ (run R cap full s ops).bank.map Prod.fst
~~~

### 1343. unreserved_step

Source: ControlStack/Scenarios/SC26Liveness.lean:249 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unreserved_step (R : Roles) (cap : ℕ) (s : St) (o : Op) (k : ℕ) (r : Req) (hk : k ∉ s.reserved) (hr : reqOf s k = some r) (hc : cap < s.spent + r.tx.amount) : k ∉ (step R cap full s o).reserved
~~~

### 1344. cap_exhausted_blocks

Source: ControlStack/Scenarios/SC26Liveness.lean:284 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cap_exhausted_blocks (R : Roles) (cap : ℕ) (s : St) (h : Inv R cap s) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) (k : ℕ) (r : Req) (hr : reqOf s k = some r) (hk : k ∉ s.reserved) (hc : cap < s.spent + r.tx.amount) : k ∉ (run R cap full s ops).reserved ∧ k ∉ (run R cap full s ops).bank.map Prod.fst
~~~

### 1345. bankApply_keys

Source: ControlStack/Scenarios/SC26Liveness.lean:307 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bankApply_keys (b : List (ℕ × Tx)) (k : ℕ) (tx : Tx) : (∀ x ∈ b.map Prod.fst, x ∈ (bankApply b k tx).map Prod.fst) ∧ k ∈ (bankApply b k tx).map Prod.fst
~~~

### 1346. CMono.refl

Source: ControlStack/Scenarios/SC26Liveness.lean:322 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem CMono.refl (s : CSt) : CMono s s
~~~

### 1347. CMono.trans

Source: ControlStack/Scenarios/SC26Liveness.lean:325 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem CMono.trans {s t u : CSt} (h1 : CMono s t) (h2 : CMono t u) : CMono s u
~~~

### 1348. set_persist

Source: ControlStack/Scenarios/SC26Liveness.lean:331 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem set_persist (l : List DRow) (i : ℕ) (d : DRow) (hd : l[i]? = some d) : ∀ x ∈ l, ∃ y ∈ l.set i { d with acked
~~~

### 1349. step_cmono

Source: ControlStack/Scenarios/SC26Liveness.lean:343 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_cmono (R : Roles) (cap : ℕ) (s : CSt) (o : COp) (ho : legalC R o) : CMono s (stepC R cap true s o)
~~~

### 1350. run_cmono

Source: ControlStack/Scenarios/SC26Liveness.lean:399 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cmono (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp) (hops : ∀ o ∈ ops, legalC R o) : CMono s (runC R cap true s ops)
~~~

### 1351. ackinv_same

Source: ControlStack/Scenarios/SC26Liveness.lean:410 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ackinv_same {s t : CSt} (h : AckInv s) (hd : t.delivery = s.delivery) (hb : t.bank = s.bank) : AckInv t
~~~

### 1352. step_ackinv

Source: ControlStack/Scenarios/SC26Liveness.lean:414 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_ackinv (R : Roles) (cap : ℕ) (s : CSt) (o : COp) (ho : legalC R o) (h : AckInv s) : AckInv (stepC R cap true s o)
~~~

### 1353. runC_append

Source: ControlStack/Scenarios/SC26Liveness.lean:469 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runC_append (R : Roles) (cap : ℕ) (s : CSt) (a b : List COp) : runC R cap true s (a ++ b) = runC R cap true (runC R cap true s a) b
~~~

### 1354. runC_cons

Source: ControlStack/Scenarios/SC26Liveness.lean:473 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runC_cons (R : Roles) (cap : ℕ) (s : CSt) (o : COp) (ops : List COp) : runC R cap true s (o :: ops) = runC R cap true (stepC R cap true s o) ops
~~~

### 1355. run_ackinv

Source: ControlStack/Scenarios/SC26Liveness.lean:476 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_ackinv (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp) (hops : ∀ o ∈ ops, legalC R o) (h : AckInv s) : AckInv (runC R cap true s ops)
~~~

### 1356. ackinv_init

Source: ControlStack/Scenarios/SC26Liveness.lean:483 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ackinv_init : AckInv cinit
~~~

### 1357. crash_tolerant_progress

Source: ControlStack/Scenarios/SC26Liveness.lean:489 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem crash_tolerant_progress (R : Roles) (cap : ℕ) (ops0 : List COp) (hops0 : ∀ o ∈ ops0, legalC R o) (k : ℕ) (d : DRow) (hd : d ∈ (runC R cap true cinit ops0).delivery) (hk : d.id = k) (pre mid post : List COp) (hleg : ∀ o ∈ pre ++ mid ++ post, legalC R o) (hh : (runC R cap true (runC R cap true cinit ops0) pre).halted = false) : k ∈ (runC R cap true (runC R cap true cinit ops0) (pre ++ .recover :: mid ++ .bankProcess k :: post)).bank.map Prod.fst ∧ ((runC R cap true (runC R cap true cinit ops0) (pre ++ .recover :: mid ++ .bankProcess k :: post)).bank.map Prod.fst).count k = 1
~~~

### 1358. crashes_forever_no_progress

Source: ControlStack/Scenarios/SC26Liveness.lean:560 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem crashes_forever_no_progress : (runC R0 10 true loggedState [.crash, .bankProcess 0, .crash, .bankProcess 0, .crash]).bank = [] ∧ (runC R0 10 true loggedState [.crash, .recover, .crash, .bankProcess 0]).bank = [(0, wTx)]
~~~

### 1359. halted_concrete_no_progress

Source: ControlStack/Scenarios/SC26Liveness.lean:567 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halted_concrete_no_progress : (runC R0 10 true strandedState [.recover, .bankProcess 0, .crash, .recover, .bankProcess 0]).bank = []
~~~

## ControlStack/Scenarios/SC26LossyHalt.lean

### 1360. bankApply_mem

Source: ControlStack/Scenarios/SC26LossyHalt.lean:42 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bankApply_mem (b : List (ℕ × Tx)) (k : ℕ) (tx : Tx) (e : ℕ × Tx) (he : e ∈ bankApply b k tx) : e ∈ b ∨ e = (k, tx)
~~~

### 1361. stepL_halted

Source: ControlStack/Scenarios/SC26LossyHalt.lean:52 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stepL_halted (R : Roles) (cap : ℕ) (s : CSt) (o : LOp) (ho : legalL R o) (hh : s.halted = true) : (stepL R cap true s o).halted = true ∧ (∀ m ∈ (stepL R cap true s o).wire, m ∈ s.wire) ∧ ∀ e ∈ (stepL R cap true s o).bank, e ∈ s.bank ∨ e ∈ s.wire
~~~

### 1362. lossy_halt

Source: ControlStack/Scenarios/SC26LossyHalt.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lossy_halt (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o) (hh : s.halted = true) : (runL R cap true s ops).halted = true ∧ (∀ m ∈ (runL R cap true s ops).wire, m ∈ s.wire) ∧ ∀ e ∈ (runL R cap true s ops).bank, e ∈ s.bank ∨ e ∈ s.wire
~~~

### 1363. lossy_halt_keys

Source: ControlStack/Scenarios/SC26LossyHalt.lean:99 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lossy_halt_keys (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o) (hh : s.halted = true) (x : ℕ) (hx : x ∈ (runL R cap true s ops).bank.map Prod.fst) : x ∈ s.bank.map Prod.fst ∨ x ∈ s.wire.map Prod.fst
~~~

### 1364. recover_ignores_halt_lossy

Source: ControlStack/Scenarios/SC26LossyHalt.lean:117 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recover_ignores_halt_lossy : strandedState.halted = true ∧ strandedState.wire = [] ∧ strandedState.bank = [] ∧ (runLH R0 10 false strandedState [.base .recover, .drop 0, .base .recover, .base (.bankProcess 0)]).bank = [(0, wTx)] ∧ (runLH R0 10 true strandedState [.base .recover, .drop 0, .base .recover, .base (.bankProcess 0)]).bank = []
~~~

### 1365. runT_append

Source: ControlStack/Scenarios/SC26LossyHalt.lean:153 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runT_append (R : Roles) (cap : ℕ) (st : TSt) (a b : List LOp) : runT R cap st (a ++ b) = runT R cap (runT R cap st a) b
~~~

### 1366. runT_cons

Source: ControlStack/Scenarios/SC26LossyHalt.lean:157 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runT_cons (R : Roles) (cap : ℕ) (st : TSt) (o : LOp) (ops : List LOp) : runT R cap st (o :: ops) = runT R cap (stepT R cap st o) ops
~~~

### 1367. stepT_c

Source: ControlStack/Scenarios/SC26LossyHalt.lean:160 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stepT_c (R : Roles) (cap : ℕ) (st : TSt) (o : LOp) : (stepT R cap st o).c = stepL R cap true st.c o
~~~

### 1368. runT_c

Source: ControlStack/Scenarios/SC26LossyHalt.lean:164 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runT_c (R : Roles) (cap : ℕ) (st : TSt) (ops : List LOp) : (runT R cap st ops).c = runL R cap true st.c ops
~~~

### 1369. tagNew_snd

Source: ControlStack/Scenarios/SC26LossyHalt.lean:169 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tagNew_snd (fresh : ℕ) (l : List (ℕ × Tx)) : (tagNew fresh l).map Prod.snd = l
~~~

### 1370. mem_tagNew

Source: ControlStack/Scenarios/SC26LossyHalt.lean:174 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mem_tagNew (fresh : ℕ) (l : List (ℕ × Tx)) (e : ℕ × (ℕ × Tx)) (he : e ∈ tagNew fresh l) : ∃ i, ∃ h : i < l.length, e = (fresh + i, l[i])
~~~

### 1371. tinv_init

Source: ControlStack/Scenarios/SC26LossyHalt.lean:184 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tinv_init : TInv tinit
~~~

### 1372. wire_deliverAt

Source: ControlStack/Scenarios/SC26LossyHalt.lean:186 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wire_deliverAt (R : Roles) (cap : ℕ) (s : CSt) (j : ℕ) : (stepL R cap true s (.deliverAt j)).wire = s.wire
~~~

### 1373. stepT_fresh

Source: ControlStack/Scenarios/SC26LossyHalt.lean:189 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stepT_fresh (R : Roles) (cap : ℕ) (st : TSt) (o : LOp) : st.fresh ≤ (stepT R cap st o).fresh
~~~

### 1374. step_tinv

Source: ControlStack/Scenarios/SC26LossyHalt.lean:192 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_tinv (R : Roles) (cap : ℕ) (st : TSt) (o : LOp) (ho : legalL R o) (h : TInv st) : TInv (stepT R cap st o)
~~~

### 1375. run_tinv

Source: ControlStack/Scenarios/SC26LossyHalt.lean:227 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_tinv (R : Roles) (cap : ℕ) (st : TSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o) (h : TInv st) : TInv (runT R cap st ops)
~~~

### 1376. step_tagIs

Source: ControlStack/Scenarios/SC26LossyHalt.lean:237 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_tagIs (R : Roles) (cap : ℕ) (st : TSt) (o : LOp) (t : ℕ) (m : ℕ × Tx) (ht : TagIs st t m) : TagIs (stepT R cap st o) t m
~~~

### 1377. tag_persists

Source: ControlStack/Scenarios/SC26LossyHalt.lean:259 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tag_persists (R : Roles) (cap : ℕ) (st : TSt) (ops : List LOp) (t : ℕ) (m : ℕ × Tx) (ht : TagIs st t m) : TagIs (runT R cap st ops) t m
~~~

### 1378. batch_tagIs

Source: ControlStack/Scenarios/SC26LossyHalt.lean:271 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem batch_tagIs (R : Roles) (cap : ℕ) (st : TSt) (o : COp) (h : TInv st) (e : ℕ × (ℕ × Tx)) (he : e ∈ batch R cap st (.base o)) : TagIs (stepT R cap st (.base o)) e.1 e.2
~~~

### 1379. recover_batch_has_k

Source: ControlStack/Scenarios/SC26LossyHalt.lean:285 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recover_batch_has_k (R : Roles) (cap : ℕ) (st : TSt) (hh : st.c.halted = false) (k : ℕ) (d : DRow) (hd : d ∈ st.c.delivery) (hk : d.id = k) (hack : d.acked = false) : ∃ e ∈ batch R cap st (.base .recover), e.2.1 = k
~~~

### 1380. tagged_progress

Source: ControlStack/Scenarios/SC26LossyHalt.lean:307 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tagged_progress (R : Roles) (cap : ℕ) (ops0 : List LOp) (hops0 : ∀ o ∈ ops0, legalL R o) (k : ℕ) (pre mid post : List LOp) (hleg : ∀ o ∈ pre ++ mid ++ post, legalL R o) (hdel : ∃ e ∈ batch R cap (runT R cap (runT R cap tinit ops0) pre) (.base .recover), e.2.1 = k ∧ DeliveredIn R cap (stepT R cap (runT R cap (runT R cap tinit ops0) pre) (.base .recover)) e.1 mid) : let fin
~~~

### 1381. tagged_rounds

Source: ControlStack/Scenarios/SC26LossyHalt.lean:376 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tagged_rounds (R : Roles) (cap : ℕ) (ops0 : List LOp) (hops0 : ∀ o ∈ ops0, legalL R o) (k : ℕ) (rounds : List (List LOp × List LOp)) (post : List LOp) (hleg : ∀ r ∈ rounds, ∀ o ∈ r.1 ++ r.2, legalL R o) (hpost : ∀ o ∈ post, legalL R o) (hfair : ∃ j, ∃ hj : j < rounds.length, DeliversT R cap k (runT R cap (runT R cap tinit ops0) ((rounds.take j).map roundOps).flatten) rounds[j]) : k ∈ (runT R cap (runT R cap tinit ops0) (rounds.map roundOps).flatten).c.bank.map Prod.fst ∧ ((runT R cap (runT R cap tinit ops0) ((rounds.map roundOps).flatten ++ post)).c.bank.map Prod.fst).count k = 1
~~~

### 1382. per_copy_weaker

Source: ControlStack/Scenarios/SC26LossyHalt.lean:433 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem per_copy_weaker : ¬ Delivers 0 pcRound ∧ DeliversT R0 10 0 tLogged pcRound ∧ (runT R0 10 tLogged (roundOps pcRound)).c.bank = [(0, wTx)]
~~~

## ControlStack/Scenarios/SC26LossyLiveness.lean

### 1383. runL_append

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runL_append (R : Roles) (cap : ℕ) (dd : Bool) (s : CSt) (a b : List LOp) : runL R cap dd s (a ++ b) = runL R cap dd (runL R cap dd s a) b
~~~

### 1384. runL_cons

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:78 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runL_cons (R : Roles) (cap : ℕ) (dd : Bool) (s : CSt) (o : LOp) (ops : List LOp) : runL R cap dd s (o :: ops) = runL R cap dd (stepL R cap dd s o) ops
~~~

### 1385. simulationL

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:97 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulationL (R : Roles) (cap : ℕ) (s : CSt) (o : LOp) (ho : legalL R o) (h : CInv s) : α (stepL R cap true s o) = run R cap full (α s) (opsOfL s o) ∧ CInv (stepL R cap true s o)
~~~

### 1386. simulation_runL

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:131 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation_runL (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o) (h : CInv s) : α (runL R cap true s ops) = run R cap full (α s) (absTraceL R cap s ops) ∧ CInv (runL R cap true s ops)
~~~

### 1387. opsOfL_legal

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:144 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem opsOfL_legal (R : Roles) (s : CSt) (o : LOp) (ho : legalL R o) : ∀ a ∈ opsOfL s o, legal R a
~~~

### 1388. absTraceL_legal

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:156 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem absTraceL_legal (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o) : ∀ a ∈ absTraceL R cap s ops, legal R a
~~~

### 1389. lossy_safe

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:168 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lossy_safe (R : Roles) (cap : ℕ) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o) : Good R cap (α (runL R cap true cinit ops))
~~~

### 1390. LMono.refl

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:181 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem LMono.refl (s : CSt) : LMono s s
~~~

### 1391. LMono.trans

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem LMono.trans {s t u : CSt} (h1 : LMono s t) (h2 : LMono t u) : LMono s u
~~~

### 1392. step_lmono

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:189 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_lmono (R : Roles) (cap : ℕ) (s : CSt) (o : LOp) (ho : legalL R o) : LMono s (stepL R cap true s o)
~~~

### 1393. run_lmono

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:203 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_lmono (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o) : LMono s (runL R cap true s ops)
~~~

### 1394. step_ackinvL

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:211 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_ackinvL (R : Roles) (cap : ℕ) (s : CSt) (o : LOp) (ho : legalL R o) (h : AckInv s) : AckInv (stepL R cap true s o)
~~~

### 1395. run_ackinvL

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:226 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_ackinvL (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o) (h : AckInv s) : AckInv (runL R cap true s ops)
~~~

### 1396. step_wire

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:238 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_wire (R : Roles) (cap : ℕ) (s : CSt) (o : LOp) (ho : legalL R o) (hd : ∀ j, o ≠ .drop j) : s.wire <+: (stepL R cap true s o).wire
~~~

### 1397. run_wire

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:252 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_wire (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o) (hd : DropFree ops) : s.wire <+: (runL R cap true s ops).wire
~~~

### 1398. lossy_progress

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:265 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lossy_progress (R : Roles) (cap : ℕ) (ops0 : List LOp) (hops0 : ∀ o ∈ ops0, legalL R o) (k : ℕ) (d : DRow) (hd : d ∈ (runL R cap true cinit ops0).delivery) (hk : d.id = k) (pre nd post : List LOp) (hleg : ∀ o ∈ pre ++ nd ++ post, legalL R o) (hnd : DropFree nd) (hh : (runL R cap true (runL R cap true cinit ops0) pre).halted = false) : let fin
~~~

### 1399. lossy_rounds

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:339 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lossy_rounds (R : Roles) (cap : ℕ) (ops0 : List LOp) (hops0 : ∀ o ∈ ops0, legalL R o) (k : ℕ) (d : DRow) (hd : d ∈ (runL R cap true cinit ops0).delivery) (hk : d.id = k) (rounds : List (List LOp × List LOp)) (post : List LOp) (hleg : ∀ r ∈ rounds, ∀ o ∈ r.1 ++ r.2, legalL R o) (hpost : ∀ o ∈ post, legalL R o) (hfair : ∃ j, ∃ hj : j < rounds.length, Delivers k rounds[j]) (hh : (runL R cap true (runL R cap true cinit ops0) (rounds.map roundOps).flatten).halted = false) : k ∈ (runL R cap true (runL R cap true cinit ops0) (rounds.map roundOps).flatten).bank.map Prod.fst ∧ ((runL R cap true (runL R cap true cinit ops0) ((rounds.map roundOps).flatten ++ post)).bank.map Prod.fst).count k = 1
~~~

### 1400. setup_reaches

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:402 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem setup_reaches : runL R0 10 true cinit setupOps = loggedState
~~~

### 1401. drop_round_fixed

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:407 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem drop_round_fixed : runL R0 10 true loggedState dropRound = loggedState
~~~

### 1402. drop_all_no_progress

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:411 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem drop_all_no_progress (n : ℕ) : runL R0 10 true loggedState (List.replicate n dropRound).flatten = loggedState ∧ (runL R0 10 true loggedState (List.replicate n dropRound).flatten).bank = [] ∧ (runL R0 10 true loggedState [.base .recover, .base (.bankProcess 0)]).bank = [(0, wTx)]
~~~

### 1403. drop_all_safe

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:422 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem drop_all_safe (n : ℕ) : Good R0 10 (α (runL R0 10 true cinit (setupOps ++ (List.replicate n dropRound).flatten)))
~~~

### 1404. no_dedup_lossy_pays_twice

Source: ControlStack/Scenarios/SC26LossyLiveness.lean:443 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_dedup_lossy_pays_twice : (runL R0 10 false loggedState lossDupTrace).bank = [(0, wTx), (0, wTx)] ∧ ((runL R0 10 false loggedState lossDupTrace).bank.map (fun e => e.2.amount)).sum = 20 ∧ (runL R0 10 true loggedState lossDupTrace).bank = [(0, wTx)] ∧ (run R0 20 { full with bankDedup
~~~

## ControlStack/Scenarios/SC26Refinement.lean

### 1405. cinv_init

Source: ControlStack/Scenarios/SC26Refinement.lean:193 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_init : CInv cinit
~~~

### 1406. creqOf_eq

Source: ControlStack/Scenarios/SC26Refinement.lean:195 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem creqOf_eq (s : CSt) (id : ℕ) : creqOf s id = reqOf (α s) id
~~~

### 1407. find_net

Source: ControlStack/Scenarios/SC26Refinement.lean:198 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem find_net (net : List (ℕ × Tx)) (s : St) (m : ℕ × Tx) (hm : m ∈ net) (hp : ∀ e ∈ net, ∃ r, reqOf s e.1 = some r ∧ r.tx = e.2) : net.find? (fun e => e.1 = m.1) = some m
~~~

### 1408. simulation

Source: ControlStack/Scenarios/SC26Refinement.lean:223 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation (R : Roles) (cap : ℕ) (s : CSt) (o : COp) (ho : legalC R o) (h : CInv s) : α (stepC R cap true s o) = run R cap full (α s) (opsOf s o) ∧ CInv (stepC R cap true s o)
~~~

### 1409. run_append

Source: ControlStack/Scenarios/SC26Refinement.lean:429 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_append (R : Roles) (cap : ℕ) (C : Checks) (s : St) (a b : List Op) : run R cap C s (a ++ b) = run R cap C (run R cap C s a) b
~~~

### 1410. simulation_run

Source: ControlStack/Scenarios/SC26Refinement.lean:433 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation_run (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp) (hops : ∀ o ∈ ops, legalC R o) (h : CInv s) : α (runC R cap true s ops) = run R cap full (α s) (absTrace R cap s ops) ∧ CInv (runC R cap true s ops)
~~~

### 1411. opsOf_legal

Source: ControlStack/Scenarios/SC26Refinement.lean:445 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem opsOf_legal (R : Roles) (s : CSt) (o : COp) (ho : legalC R o) : ∀ a ∈ opsOf s o, legal R a
~~~

### 1412. absTrace_legal

Source: ControlStack/Scenarios/SC26Refinement.lean:453 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem absTrace_legal (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp) (hops : ∀ o ∈ ops, legalC R o) : ∀ a ∈ absTrace R cap s ops, legal R a
~~~

### 1413. concrete_safe

Source: ControlStack/Scenarios/SC26Refinement.lean:470 | Family: F8 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem concrete_safe (R : Roles) (cap : ℕ) (ops : List COp) (hops : ∀ o ∈ ops, legalC R o) : Good R cap (α (runC R cap true cinit ops))
~~~

### 1414. stepC_halted

Source: ControlStack/Scenarios/SC26Refinement.lean:477 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stepC_halted (R : Roles) (cap : ℕ) (s : CSt) (o : COp) (ho : legalC R o) (hh : s.halted = true) : (stepC R cap true s o).halted = true ∧ (stepC R cap true s o).wire = s.wire ∧ ∀ e ∈ (stepC R cap true s o).bank, e ∈ s.bank ∨ e ∈ s.wire
~~~

### 1415. concrete_halt

Source: ControlStack/Scenarios/SC26Refinement.lean:515 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_halt (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp) (hops : ∀ o ∈ ops, legalC R o) (hh : s.halted = true) : (runC R cap true s ops).wire = s.wire ∧ ∀ e ∈ (runC R cap true s ops).bank, e ∈ s.bank ∨ e ∈ s.wire
~~~

### 1416. recover_halt_witness

Source: ControlStack/Scenarios/SC26Refinement.lean:540 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recover_halt_witness : (runC R0 10 false strandedState [.recover, .bankProcess 0]).bank = [(0, wTx)] ∧ (0, wTx) ∉ strandedState.bank ∧ (0, wTx) ∉ strandedState.wire ∧ (runC R0 10 true strandedState [.recover, .bankProcess 0]).bank = []
~~~

## ControlStack/Scenarios/SC26Transaction.lean

### 1417. sound_full

Source: ControlStack/Scenarios/SC26Transaction.lean:124 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sound_full : Sound full
~~~

### 1418. reqOf_append

Source: ControlStack/Scenarios/SC26Transaction.lean:198 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reqOf_append (s : St) (l : List Req) (k : ℕ) (r : Req) (h : reqOf s k = some r) : reqOf { s with reqs
~~~

### 1419. inv_init

Source: ControlStack/Scenarios/SC26Transaction.lean:203 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (R : Roles) (cap : ℕ) : Inv R cap init
~~~

### 1420. Approved.mono

Source: ControlStack/Scenarios/SC26Transaction.lean:211 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Approved.mono {R : Roles} {s t : St} {k : ℕ} {r : Req} (h : Ext s t) (ha : Approved R s k r) : Approved R t k r
~~~

### 1421. amt_ext

Source: ControlStack/Scenarios/SC26Transaction.lean:216 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem amt_ext {s t : St} (h : Ext s t) (k : ℕ) (hk : ∃ r, reqOf s k = some r) : amt t k = amt s k
~~~

### 1422. sum_ext

Source: ControlStack/Scenarios/SC26Transaction.lean:220 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_ext {s t : St} (h : Ext s t) (l : List ℕ) (hl : ∀ k ∈ l, ∃ r, reqOf s k = some r) : (l.map (amt t)).sum = (l.map (amt s)).sum
~~~

### 1423. bank_sum

Source: ControlStack/Scenarios/SC26Transaction.lean:226 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bank_sum (s : St) (hb : ∀ e ∈ s.bank, ∃ r, reqOf s e.1 = some r ∧ r.tx = e.2) : (s.bank.map (fun e => e.2.amount)).sum = ((s.bank.map Prod.fst).map (amt s)).sum
~~~

### 1424. sum_le_of_subperm

Source: ControlStack/Scenarios/SC26Transaction.lean:235 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_le_of_subperm (f : ℕ → ℕ) (l₁ l₂ : List ℕ) (h : List.Subperm l₁ l₂) : (l₁.map f).sum ≤ (l₂.map f).sum
~~~

### 1425. Inv.good

Source: ControlStack/Scenarios/SC26Transaction.lean:240 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {R : Roles} {cap : ℕ} {s : St} (h : Inv R cap s) : Good R cap s
~~~

### 1426. inv_of_ext

Source: ControlStack/Scenarios/SC26Transaction.lean:258 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_of_ext {R : Roles} {cap : ℕ} {s t : St} (h : Inv R cap s) (he : Ext s t) (happr : ∀ ap ∈ t.approvals, ap ∉ s.approvals → ∃ r, reqOf t ap.1 = some r ∧ ap.2.2 = r.tx ∧ ap.2.1 ∈ R.approvers ∧ ap.2.1 ≠ r.requester) (hres : t.reserved = s.reserved) (hsp : t.spent = s.spent) (hbank : t.bank = s.bank) (hnet : t.net = s.net) : Inv R cap t
~~~

### 1427. ext_refl

Source: ControlStack/Scenarios/SC26Transaction.lean:287 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ext_refl (s : St) : Ext s s
~~~

### 1428. bankAppend_inv

Source: ControlStack/Scenarios/SC26Transaction.lean:289 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bankAppend_inv {R : Roles} {cap : ℕ} {C : Checks} (hdd : C.bankDedup = true) {s : St} (h : Inv R cap s) (k : ℕ) (r : Req) (hk : k ∈ s.reserved) (hr : reqOf s k = some r) : Inv R cap (bankAppend C s k r.tx)
~~~

### 1429. step_inv

Source: ControlStack/Scenarios/SC26Transaction.lean:307 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (R : Roles) (cap : ℕ) {C : Checks} (hC : Sound C) (s : St) (o : Op) (ho : legal R o) (h : Inv R cap s) : Inv R cap (step R cap C s o)
~~~

### 1430. run_cons

Source: ControlStack/Scenarios/SC26Transaction.lean:395 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (R : Roles) (cap : ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) : run R cap C s (o :: ops) = run R cap C (step R cap C s o) ops
~~~

### 1431. run_inv

Source: ControlStack/Scenarios/SC26Transaction.lean:398 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (R : Roles) (cap : ℕ) {C : Checks} (hC : Sound C) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) (h : Inv R cap s) : Inv R cap (run R cap C s ops)
~~~

### 1432. safe_of_sound

Source: ControlStack/Scenarios/SC26Transaction.lean:409 | Family: F8 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem safe_of_sound (R : Roles) (cap : ℕ) {C : Checks} (hC : Sound C) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) : Good R cap (run R cap C init ops)
~~~

### 1433. good_without_nonce

Source: ControlStack/Scenarios/SC26Transaction.lean:414 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem good_without_nonce (R : Roles) (cap : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) : Good R cap (run R cap { full with nonce
~~~

### 1434. sc26_safe

Source: ControlStack/Scenarios/SC26Transaction.lean:426 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc26_safe (R : Roles) (cap : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) : Good R cap (run R cap full init ops)
~~~

### 1435. sc26_safe_disjoint

Source: ControlStack/Scenarios/SC26Transaction.lean:431 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc26_safe_disjoint (R : Roles) (cap : ℕ) (hdisj : ∀ a ∈ R.approvers, a ∉ R.agents) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) : ∀ e ∈ (run R cap full init ops).bank, ∃ r a, reqOf (run R cap full init ops) e.1 = some r ∧ r.tx = e.2 ∧ (e.1, a, e.2) ∈ (run R cap full init ops).approvals ∧ a ∈ R.approvers ∧ a ∉ R.agents ∧ a ≠ r.requester
~~~

### 1436. bankAppend_reserved

Source: ControlStack/Scenarios/SC26Transaction.lean:439 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bankAppend_reserved (C : Checks) (s : St) (k : ℕ) (tx : Tx) : (bankAppend C s k tx).reserved = s.reserved
~~~

### 1437. step_res_nodup

Source: ControlStack/Scenarios/SC26Transaction.lean:443 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_res_nodup (R : Roles) (cap : ℕ) (C : Checks) (hn : C.nonce = true) (s : St) (o : Op) (h : s.reserved.Nodup) : (step R cap C s o).reserved.Nodup
~~~

### 1438. sc26_once

Source: ControlStack/Scenarios/SC26Transaction.lean:484 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc26_once (R : Roles) (cap : ℕ) (ops : List Op) : (run R cap full init ops).reserved.Nodup
~~~

### 1439. bankAppend_mem

Source: ControlStack/Scenarios/SC26Transaction.lean:492 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bankAppend_mem (C : Checks) (s : St) (k : ℕ) (tx : Tx) (e : ℕ × Tx) (he : e ∈ (bankAppend C s k tx).bank) : e ∈ s.bank ∨ e = (k, tx)
~~~

### 1440. step_halted

Source: ControlStack/Scenarios/SC26Transaction.lean:503 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (R : Roles) (cap : ℕ) (s : St) (o : Op) (ho : legal R o) (hh : s.halted = true) : (step R cap full s o).net = s.net ∧ (step R cap full s o).halted = true ∧ ∀ e ∈ (step R cap full s o).bank, e ∈ s.bank ∨ e ∈ s.net
~~~

### 1441. halt_freezes

Source: ControlStack/Scenarios/SC26Transaction.lean:532 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem halt_freezes (R : Roles) (cap : ℕ) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) (hh : s.halted = true) : (run R cap full s ops).net = s.net ∧ ∀ e ∈ (run R cap full s ops).bank, e ∈ s.bank ∨ e ∈ s.net
~~~

### 1442. halt_freezes_quiescent

Source: ControlStack/Scenarios/SC26Transaction.lean:547 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes_quiescent (R : Roles) (cap : ℕ) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) (hh : s.halted = true) (hq : ∀ m ∈ s.net, m ∈ s.bank) : ∀ e ∈ (run R cap full s ops).bank, e ∈ s.bank
~~~

### 1443. bankAppend_prefix

Source: ControlStack/Scenarios/SC26Transaction.lean:554 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bankAppend_prefix (C : Checks) (s : St) (k : ℕ) (tx : Tx) : s.bank <+: (bankAppend C s k tx).bank
~~~

### 1444. bank_prefix

Source: ControlStack/Scenarios/SC26Transaction.lean:560 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bank_prefix (R : Roles) (cap : ℕ) (C : Checks) (s : St) (o : Op) : s.bank <+: (step R cap C s o).bank
~~~

### 1445. not_good_of

Source: ControlStack/Scenarios/SC26Transaction.lean:613 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem not_good_of {R : Roles} {cap : ℕ} {s : St} (e : ℕ × Tx) (he : e ∈ s.bank) (hn : ∀ ap ∈ s.approvals, ap.1 = e.1 → ap.2.2 = e.2 → ap.2.1 ∈ R.approvers → False) : ¬ Good R cap s
~~~

### 1446. honest_trace_pays

Source: ControlStack/Scenarios/SC26Transaction.lean:620 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_trace_pays : (run R0 20 full init [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .arrive 0, .deliver 0, .arrive 0, .arrive 0]).bank = [(0, tx1)]
~~~

### 1447. payload_unchecked_breaks

Source: ControlStack/Scenarios/SC26Transaction.lean:625 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem payload_unchecked_breaks : let s
~~~

### 1448. no_dedup_retry_duplicates

Source: ControlStack/Scenarios/SC26Transaction.lean:637 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_dedup_retry_duplicates : let s
~~~

### 1449. no_dedup_breaks_cap

Source: ControlStack/Scenarios/SC26Transaction.lean:651 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_dedup_breaks_cap : let s
~~~

### 1450. no_bank_auth_breaks

Source: ControlStack/Scenarios/SC26Transaction.lean:658 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_bank_auth_breaks : let s
~~~

### 1451. same_payload_twice_is_good

Source: ControlStack/Scenarios/SC26Transaction.lean:669 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem same_payload_twice_is_good : let ops : List Op
~~~

### 1452. no_cap_breaks

Source: ControlStack/Scenarios/SC26Transaction.lean:679 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_cap_breaks : let s
~~~

### 1453. no_halt_check_breaks

Source: ControlStack/Scenarios/SC26Transaction.lean:693 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : let C
~~~

### 1454. halt_check_blocks

Source: ControlStack/Scenarios/SC26Transaction.lean:700 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_check_blocks : let s
~~~

### 1455. inflight_after_halt

Source: ControlStack/Scenarios/SC26Transaction.lean:706 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inflight_after_halt : let s
~~~

### 1456. gate_credential_leak_breaks

Source: ControlStack/Scenarios/SC26Transaction.lean:712 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gate_credential_leak_breaks : let s
~~~

### 1457. self_approval_without_distinct_check

Source: ControlStack/Scenarios/SC26Transaction.lean:724 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem self_approval_without_distinct_check : let s
~~~

### 1458. distinct_check_blocks_self_approval

Source: ControlStack/Scenarios/SC26Transaction.lean:743 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem distinct_check_blocks_self_approval : (run R1 20 full init [.request 1 tx1, .approve 1 0 tx1, .execute 1 0, .deliver 0, .arrive 0]).bank = []
~~~

### 1459. nonce_protects_budget_only

Source: ControlStack/Scenarios/SC26Transaction.lean:749 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nonce_protects_budget_only : let s
~~~

## ControlStack/Scenarios/SC27Chain.lean

### 1460. chainHead_concat

Source: ControlStack/Scenarios/SC27Chain.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem chainHead_concat (H : ℕ → ℕ → ℕ) (h0 : ℕ) (l : List ℕ) (e : ℕ) : chainHead H h0 (l ++ [e]) = H (chainHead H h0 l) e
~~~

### 1461. chainHead_injective

Source: ControlStack/Scenarios/SC27Chain.lean:53 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem chainHead_injective (H : ℕ → ℕ → ℕ) (h0 : ℕ) (hinj : ∀ a b c d, H a b = H c d → a = c ∧ b = d) (hne : ∀ a b, H a b ≠ h0) : Function.Injective (chainHead H h0)
~~~

### 1462. run_cons

Source: ControlStack/Scenarios/SC27Chain.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 1463. inv_init

Source: ControlStack/Scenarios/SC27Chain.lean:140 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) : Inv E init
~~~

### 1464. AccOk.mono

Source: ControlStack/Scenarios/SC27Chain.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem AccOk.mono {E : Env} {s t : St} (ha : s.anchors ⊆ t.anchors) {m : List ℕ} (h : AccOk E s m) : AccOk E t m
~~~

### 1465. step_inv

Source: ControlStack/Scenarios/SC27Chain.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o)
~~~

### 1466. run_inv

Source: ControlStack/Scenarios/SC27Chain.lean:182 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 1467. sc27_safe

Source: ControlStack/Scenarios/SC27Chain.lean:191 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc27_safe (E : Env) (ops : List Op) (hinj : Set.InjOn (chainHead E.H E.h0) {l | l ∈ (run E full init ops).accepted ∨ ∃ a ∈ (run E full init ops).anchors, a.2 = some l}) : ∀ m ∈ (run E full init ops).accepted, ∃ a ∈ (run E full init ops).anchors, a.2 = some m
~~~

### 1468. step_halted

Source: ControlStack/Scenarios/SC27Chain.lean:202 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s
~~~

### 1469. halt_freezes

Source: ControlStack/Scenarios/SC27Chain.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
~~~

### 1470. accepted_prefix

Source: ControlStack/Scenarios/SC27Chain.lean:219 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem accepted_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.accepted <+: (step E C s o).accepted
~~~

### 1471. honest_accept

Source: ControlStack/Scenarios/SC27Chain.lean:247 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_accept : (run E0 full init [.append 5, .append 6, .anchor, .verify [5, 6]]).accepted = [[5, 6]]
~~~

### 1472. tamper_after_anchor_detected

Source: ControlStack/Scenarios/SC27Chain.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tamper_after_anchor_detected : (run E0 full init [.append 5, .anchor, .rewrite [7], .verify [7]]).accepted = [] ∧ (run E0 full init [.append 5, .append 6, .anchor, .rewrite [6, 5], .verify [6, 5]]).accepted = []
~~~

### 1473. no_anchor_rollback_breaks

Source: ControlStack/Scenarios/SC27Chain.lean:257 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_anchor_rollback_breaks : let s
~~~

### 1474. self_signed_breaks

Source: ControlStack/Scenarios/SC27Chain.lean:263 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem self_signed_breaks : (run E0 { full with independentOnly
~~~

### 1475. unanchored_suffix_breaks

Source: ControlStack/Scenarios/SC27Chain.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unanchored_suffix_breaks : (run E0 { full with noSuffix
~~~

### 1476. collision_breaks

Source: ControlStack/Scenarios/SC27Chain.lean:275 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem collision_breaks : (run ⟨fun h e => (h + e) % 10, 0, [9]⟩ full init [.append 5, .anchor, .verify [2, 3]]).accepted = [[2, 3]]
~~~

### 1477. rewrite_before_anchor_window

Source: ControlStack/Scenarios/SC27Chain.lean:280 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rewrite_before_anchor_window : let s
~~~

### 1478. no_halt_check_breaks

Source: ControlStack/Scenarios/SC27Chain.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run E0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC27ExtensionOnly.lean

### 1479. run_cons

Source: ControlStack/Scenarios/SC27ExtensionOnly.lean:84 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (b : Bool) (s : St) (o : Op) (ops : List Op) : run E b s (o :: ops) = run E b (step E b s o) ops
~~~

### 1480. extendsLast_iff

Source: ControlStack/Scenarios/SC27ExtensionOnly.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem extendsLast_iff (s : St) : extendsLast s = true ↔ ∀ l0, s.last = some l0 → l0 <+: s.log
~~~

### 1481. inv_init

Source: ControlStack/Scenarios/SC27ExtensionOnly.lean:102 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) : Inv E init
~~~

### 1482. step_inv

Source: ControlStack/Scenarios/SC27ExtensionOnly.lean:104 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E true s o)
~~~

### 1483. run_inv

Source: ControlStack/Scenarios/SC27ExtensionOnly.lean:140 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E true s ops)
~~~

### 1484. anchors_chain

Source: ControlStack/Scenarios/SC27ExtensionOnly.lean:149 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem anchors_chain (E : Env) (ops : List Op) : (run E true init ops).anchors.Pairwise (fun a b => a.2 <+: b.2) ∧ ∀ a ∈ (run E true init ops).anchors, ∃ l, (run E true init ops).last = some l ∧ a.2 <+: l
~~~

### 1485. sc27_ext_safe

Source: ControlStack/Scenarios/SC27ExtensionOnly.lean:159 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc27_ext_safe (E : Env) (ops : List Op) (hinj : Set.InjOn (chainHead E.H E.h0) {l | l ∈ (run E true init ops).accepted ∨ ∃ a ∈ (run E true init ops).anchors, a.2 = l}) : ∀ m ∈ (run E true init ops).accepted, (∃ a ∈ (run E true init ops).anchors, a.2 = m) ∧ ∃ l, (run E true init ops).last = some l ∧ m <+: l
~~~

### 1486. tampered_never_anchored

Source: ControlStack/Scenarios/SC27ExtensionOnly.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tampered_never_anchored (E : Env) (s : St) (hs : Inv E s) (ops : List Op) (l : List ℕ) (hl : ∃ a ∈ s.anchors, a.2 = l) : ∀ a ∈ (run E true s ops).anchors, a ∈ s.anchors ∨ l <+: a.2
~~~

### 1487. alarm_iff

Source: ControlStack/Scenarios/SC27ExtensionOnly.lean:214 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem alarm_iff (E : Env) (s : St) : ((step E true s .anchor).alarms = s.alarms ++ [s.log] ↔ extendsLast s = false) ∧ (extendsLast s = false → (step E true s .anchor).anchors = s.anchors)
~~~

### 1488. honest_liveness

Source: ControlStack/Scenarios/SC27ExtensionOnly.lean:226 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_liveness (E : Env) (s : St) (hx : extendsLast s = true) : s.log ∈ (run E true s [.anchor, .verify s.log]).accepted ∧ (run E true s [.anchor, .verify s.log]).last = some s.log
~~~

### 1489. append_extends

Source: ControlStack/Scenarios/SC27ExtensionOnly.lean:231 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem append_extends (s : St) (e : ℕ) (hx : extendsLast s = true) : extendsLast { s with log
~~~

### 1490. head_check_iff_prefix

Source: ControlStack/Scenarios/SC27ExtensionOnly.lean:241 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem head_check_iff_prefix (H : ℕ → ℕ → ℕ) (h0 : ℕ) (l0 l : List ℕ) (hinj : Set.InjOn (chainHead H h0) {l0, l.take l0.length}) : (l0.length ≤ l.length ∧ chainHead H h0 (l.take l0.length) = chainHead H h0 l0) ↔ l0 <+: l
~~~

### 1491. periodic_anchor_launders

Source: ControlStack/Scenarios/SC27ExtensionOnly.lean:259 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem periodic_anchor_launders : (run E0 false init [.append 5, .anchor, .rewrite [7], .anchor, .verify [7]]).accepted = [[7]] ∧ (run E0 true init [.append 5, .anchor, .rewrite [7], .anchor, .verify [7]]).accepted = [] ∧ (run E0 true init [.append 5, .anchor, .rewrite [7], .anchor, .verify [7]]).alarms = [[7]]
~~~

### 1492. honest_periods

Source: ControlStack/Scenarios/SC27ExtensionOnly.lean:266 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_periods : (run E0 true init [.append 5, .anchor, .verify [5], .append 6, .anchor, .verify [5, 6]]).accepted = [[5], [5, 6]]
~~~

## ControlStack/Scenarios/SC27Refinement.lean

### 1493. ancs_anc

Source: ControlStack/Scenarios/SC27Refinement.lean:116 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem ancs_anc (l : List WRec) (h n : ℕ) (g : List ℕ) : ancs (l ++ [.anc h n g]) = ancs l ++ [(h, g)]
~~~

### 1494. ancs_fork

Source: ControlStack/Scenarios/SC27Refinement.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem ancs_fork (l : List WRec) (h n ah an : ℕ) (g : List ℕ) : ancs (l ++ [.fork h n ah an g]) = ancs l
~~~

### 1495. forks_anc

Source: ControlStack/Scenarios/SC27Refinement.lean:121 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem forks_anc (l : List WRec) (h n : ℕ) (g : List ℕ) : forks (l ++ [.anc h n g]) = forks l
~~~

### 1496. forks_fork

Source: ControlStack/Scenarios/SC27Refinement.lean:123 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem forks_fork (l : List WRec) (h n ah an : ℕ) (g : List ℕ) : forks (l ++ [.fork h n ah an g]) = forks l ++ [g]
~~~

### 1497. runC_cons

Source: ControlStack/Scenarios/SC27Refinement.lean:157 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runC_cons (E : Env) (b : Bool) (s : CSt) (o : COp) (ops : List COp) : runC E b s (o :: ops) = runC E b (stepC E b s o) ops
~~~

### 1498. runC_append

Source: ControlStack/Scenarios/SC27Refinement.lean:160 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runC_append (E : Env) (b : Bool) (s : CSt) (x y : List COp) : runC E b s (x ++ y) = runC E b (runC E b s x) y
~~~

### 1499. cinv_init

Source: ControlStack/Scenarios/SC27Refinement.lean:169 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_init (E : Env) : CInv E cinit
~~~

### 1500. cinv_step

Source: ControlStack/Scenarios/SC27Refinement.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_step (E : Env) (b : Bool) (s : CSt) (o : COp) (h : CInv E s) : CInv E (stepC E b s o)
~~~

### 1501. cinv_run

Source: ControlStack/Scenarios/SC27Refinement.lean:189 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_run (E : Env) (b : Bool) (s : CSt) (ops : List COp) (h : CInv E s) : CInv E (runC E b s ops)
~~~

### 1502. traceInj_append

Source: ControlStack/Scenarios/SC27Refinement.lean:203 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem traceInj_append (E : Env) (s : CSt) (x y : List COp) : TraceInj E s (x ++ y) ↔ TraceInj E s x ∧ TraceInj E (runC E false s x) y
~~~

### 1503. extends_of_prefix

Source: ControlStack/Scenarios/SC27Refinement.lean:224 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem extends_of_prefix {s : CSt} {l0 : List ℕ} (hg : s.ghostLast = some l0) (hp : l0 <+: s.store) : SC27ExtensionOnly.extendsLast (α s) = true
~~~

### 1504. not_extends_of_not_prefix

Source: ControlStack/Scenarios/SC27Refinement.lean:228 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem not_extends_of_not_prefix {s : CSt} {l0 : List ℕ} (hg : s.ghostLast = some l0) (hp : ¬ l0 <+: s.store) : SC27ExtensionOnly.extendsLast (α s) = false
~~~

### 1505. simulation

Source: ControlStack/Scenarios/SC27Refinement.lean:235 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation (E : Env) (s : CSt) (o : COp) (h : CInv E s) (hinj : o = .examine → ExamInj E s) : α (stepC E false s o) = SC27ExtensionOnly.run E true (α s) (opsOf E s o)
~~~

### 1506. simulation_run

Source: ControlStack/Scenarios/SC27Refinement.lean:300 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation_run (E : Env) (s : CSt) (ops : List COp) (h : CInv E s) (ht : TraceInj E s ops) : α (runC E false s ops) = SC27ExtensionOnly.run E true (α s) (absTrace E s ops)
~~~

### 1507. concrete_ext_safe

Source: ControlStack/Scenarios/SC27Refinement.lean:316 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_ext_safe (E : Env) (ops : List COp) (ht : TraceInj E cinit ops) (hinj : Set.InjOn (chainHead E.H E.h0) {l | l ∈ (runC E false cinit ops).accepted ∨ ∃ a ∈ ancs (runC E false cinit ops).wlog, a.2 = l}) : ∀ m ∈ (runC E false cinit ops).accepted, (∃ a ∈ ancs (runC E false cinit ops).wlog, a.2 = m) ∧ ∃ l, (runC E false cinit ops).ghostLast = some l ∧ m <+: l
~~~

### 1508. concrete_tampered_never_anchored

Source: ControlStack/Scenarios/SC27Refinement.lean:330 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_tampered_never_anchored (E : Env) (pre post : List COp) (ht : TraceInj E cinit (pre ++ post)) (l : List ℕ) (hl : ∃ a ∈ ancs (runC E false cinit pre).wlog, a.2 = l) : ∀ a ∈ ancs (runC E false cinit (pre ++ post)).wlog, a ∈ ancs (runC E false cinit pre).wlog ∨ l <+: a.2
~~~

### 1509. concrete_alarm_iff

Source: ControlStack/Scenarios/SC27Refinement.lean:351 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_alarm_iff (E : Env) (s : CSt) (h : CInv E s) (hI : ExamInj E s) (hne : s.store ≠ []) (l0 : List ℕ) (hg : s.ghostLast = some l0) : (forks (stepC E false s .examine).wlog = forks s.wlog ++ [s.store] ↔ ¬ l0 <+: s.store) ∧ (¬ l0 <+: s.store → ancs (stepC E false s .examine).wlog = ancs s.wlog)
~~~

### 1510. empty_truncation_silent

Source: ControlStack/Scenarios/SC27Refinement.lean:396 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem empty_truncation_silent : forks (runC E0 false cinit [.append 5, .examine, .rewrite [], .examine]).wlog = [] ∧ (SC27ExtensionOnly.run E0 true SC27ExtensionOnly.init [.append 5, .anchor, .rewrite [], .anchor]).alarms = [[]] ∧ ancs (runC E0 false cinit [.append 5, .examine, .rewrite [], .examine]).wlog = [(1 * 0 + 5 + 1, [5])]
~~~

### 1511. writer_heads_breaks

Source: ControlStack/Scenarios/SC27Refinement.lean:405 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem writer_heads_breaks : let ops : List COp
~~~

### 1512. honest_concrete

Source: ControlStack/Scenarios/SC27Refinement.lean:413 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_concrete : let t
~~~

## ControlStack/Scenarios/SC28Budget.lean

### 1513. forkUpd_full_leases

Source: ControlStack/Scenarios/SC28Budget.lean:105 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forkUpd_full_leases (s : St) (p ch nl : ℕ) : (forkUpd full s p ch nl).1 = s.leases
~~~

### 1514. run_cons

Source: ControlStack/Scenarios/SC28Budget.lean:139 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) : run admins G C s (o :: ops) = run admins G C (step admins G C s o) ops
~~~

### 1515. Inv.good

Source: ControlStack/Scenarios/SC28Budget.lean:160 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {G : ℕ} {s : St} (h : Inv G s) : Good G s
~~~

### 1516. inv_init

Source: ControlStack/Scenarios/SC28Budget.lean:163 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (G : ℕ) : Inv G init
~~~

### 1517. budgetOf_append

Source: ControlStack/Scenarios/SC28Budget.lean:167 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem budgetOf_append (s : St) (lid b : ℕ) (hfresh : budgetOf s lid = none) (l : ℕ) : budgetOf { s with leases
~~~

### 1518. inv_of_same

Source: ControlStack/Scenarios/SC28Budget.lean:178 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_of_same {G : ℕ} {s t : St} (h : Inv G s) (hl : t.ledger = s.ledger) (hu : t.usage = s.usage) (hb : ∀ lid, (budgetOf s lid).getD 0 ≤ (budgetOf t lid).getD 0 ∨ spentL s lid = 0) : Inv G t
~~~

### 1519. work_inv

Source: ControlStack/Scenarios/SC28Budget.lean:191 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem work_inv {G : ℕ} {s : St} (h : Inv G s) (w lid a b ch : ℕ) (hch : a ≤ ch) (h1 : 1 ≤ ch) (hb : budgetOf s lid = some b) (hcl : spentL s lid + ch ≤ b) (hcg : spentT s + ch ≤ G) : Inv G { s with ledger
~~~

### 1520. step_inv

Source: ControlStack/Scenarios/SC28Budget.lean:225 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (admins : List ℕ) (G : ℕ) (s : St) (o : Op) (ho : legal o) (h : Inv G s) : Inv G (step admins G full s o)
~~~

### 1521. run_inv

Source: ControlStack/Scenarios/SC28Budget.lean:283 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal o) (h : Inv G s) : Inv G (run admins G full s ops)
~~~

### 1522. sc28_safe

Source: ControlStack/Scenarios/SC28Budget.lean:294 | Family: F5 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc28_safe (admins : List ℕ) (G : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal o) : Good G (run admins G full init ops)
~~~

### 1523. step_revoked

Source: ControlStack/Scenarios/SC28Budget.lean:300 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_revoked (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (o : Op) (lid : ℕ) (hr : lid ∈ s.revoked) : lid ∈ (step admins G C s o).revoked ∧ usedL (step admins G C s o) lid = usedL s lid
~~~

### 1524. revoked_lease_stops

Source: ControlStack/Scenarios/SC28Budget.lean:326 | Family: F5 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem revoked_lease_stops (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (ops : List Op) (lid : ℕ) (hr : lid ∈ s.revoked) : usedL (run admins G C s ops) lid = usedL s lid
~~~

### 1525. fork_shares_lease

Source: ControlStack/Scenarios/SC28Budget.lean:337 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fork_shares_lease (admins : List ℕ) (G : ℕ) (s : St) (c p ch nl lid : ℕ) (hh : s.halted = false) (hp : leaseOf s p = some lid) (hfresh : ch ∉ s.assign.map Prod.fst) : leaseOf (step admins G full s (.fork c p ch nl)) ch = some lid
~~~

### 1526. step_halted

Source: ControlStack/Scenarios/SC28Budget.lean:346 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (admins : List ℕ) (G : ℕ) (s : St) (o : Op) (hh : s.halted = true) : (step admins G full s o).usage = s.usage ∧ (step admins G full s o).halted = true
~~~

### 1527. halt_freezes

Source: ControlStack/Scenarios/SC28Budget.lean:356 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op) (hh : s.halted = true) : (run admins G full s ops).usage = s.usage
~~~

### 1528. usage_prefix

Source: ControlStack/Scenarios/SC28Budget.lean:367 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usage_prefix (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (o : Op) : s.usage <+: (step admins G C s o).usage
~~~

### 1529. Good.entry

Source: ControlStack/Scenarios/SC28Budget.lean:381 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Good.entry {G : ℕ} {s : St} (h : Good G s) (e : ℕ × ℕ × ℕ) (he : e ∈ s.usage) : EntryOk s e
~~~

### 1530. honest_trace_works

Source: ControlStack/Scenarios/SC28Budget.lean:402 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_trace_works : (run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0, .work 1 3 3, .restart, .work 1 4 4]).usage = [(1, 0, 3), (1, 0, 4)]
~~~

### 1531. no_global_counter_breaks

Source: ControlStack/Scenarios/SC28Budget.lean:408 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_global_counter_breaks : usedT (run [9] 10 { full with global
~~~

### 1532. fresh_fork_exceeds_parent

Source: ControlStack/Scenarios/SC28Budget.lean:416 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fresh_fork_exceeds_parent : (run [9] 100 { full with share
~~~

### 1533. fresh_fork_escapes_revocation

Source: ControlStack/Scenarios/SC28Budget.lean:425 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fresh_fork_escapes_revocation : (run [9] 100 { full with share
~~~

### 1534. reported_cost_breaks

Source: ControlStack/Scenarios/SC28Budget.lean:433 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reported_cost_breaks : let s
~~~

### 1535. rollback_double_spends

Source: ControlStack/Scenarios/SC28Budget.lean:440 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rollback_double_spends : usedT (run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0, .work 1 10 0, .rollback 0, .work 1 10 0]) = 20
~~~

### 1536. no_halt_check_breaks

Source: ControlStack/Scenarios/SC28Budget.lean:445 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run [9] 10 { full with haltCheck
~~~

## ControlStack/Scenarios/SC28Liveness.lean

### 1537. work_accepted

Source: ControlStack/Scenarios/SC28Liveness.lean:42 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem work_accepted (s : St) (w a r lid b : ℕ) (hh : s.halted = false) (hl : leaseOf s w = some lid) (hb : budgetOf s lid = some b) (hr : lid ∉ s.revoked) (hcl : spentL s lid + charge full a r ≤ b) (hcg : spentT s + charge full a r ≤ G) : step admins G full s (.work w a r) = { s with ledger
~~~

### 1538. work_refused_reasons

Source: ControlStack/Scenarios/SC28Liveness.lean:51 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem work_refused_reasons (s : St) (w a r : ℕ) (href : (step admins G full s (.work w a r)).usage = s.usage) : s.halted = true ∨ leaseOf s w = none ∨ ∃ lid, leaseOf s w = some lid ∧ (budgetOf s lid = none ∨ lid ∈ s.revoked ∨ ∃ b, budgetOf s lid = some b ∧ (b < spentL s lid + charge full a r ∨ G < spentT s + charge full a r))
~~~

### 1539. spentL_append

Source: ControlStack/Scenarios/SC28Liveness.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem spentL_append {s t : St} {lid ch : ℕ} (ht : t.ledger = s.ledger ++ [(lid, ch)]) (l : ℕ) : spentL t l = spentL s l + (if lid = l then ch else 0)
~~~

### 1540. spentT_append

Source: ControlStack/Scenarios/SC28Liveness.lean:80 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem spentT_append {s t : St} {lid ch : ℕ} (ht : t.ledger = s.ledger ++ [(lid, ch)]) : spentT t = spentT s + ch
~~~

### 1541. honest_steps_progress

Source: ControlStack/Scenarios/SC28Liveness.lean:89 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_steps_progress (s : St) (w lid b : ℕ) (as : List ℕ) (hh : s.halted = false) (hl : leaseOf s w = some lid) (hb : budgetOf s lid = some b) (hr : lid ∉ s.revoked) (hcl : spentL s lid + charges as ≤ b) (hcg : spentT s + charges as ≤ G) : (run admins G full s (as.map (fun a => .work w a a))).usage = s.usage ++ as.map (fun a => (w, lid, a))
~~~

### 1542. budget_step

Source: ControlStack/Scenarios/SC28Liveness.lean:105 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem budget_step (s : St) (o : Op) (lid b : ℕ) (hb : budgetOf s lid = some b) : budgetOf (step admins G full s o) lid = some b
~~~

### 1543. budget_run

Source: ControlStack/Scenarios/SC28Liveness.lean:126 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem budget_run (s : St) (ops : List Op) (lid b : ℕ) (hb : budgetOf s lid = some b) : budgetOf (run admins G full s ops) lid = some b
~~~

### 1544. progress_interleaved

Source: ControlStack/Scenarios/SC28Liveness.lean:135 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem progress_interleaved (s : St) (w a lid b : ℕ) (_hl : leaseOf s w = some lid) (hb : budgetOf s lid = some b) (hcl : spentL s lid + charge full a a ≤ b) (hcg : spentT s + charge full a a ≤ G) (p : List Op) : let t
~~~

### 1545. global_cap_blocks_honest

Source: ControlStack/Scenarios/SC28Liveness.lean:161 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem global_cap_blocks_honest : let s
~~~

### 1546. descendant_consumes_lease

Source: ControlStack/Scenarios/SC28Liveness.lean:168 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem descendant_consumes_lease : let s
~~~

### 1547. honest_example

Source: ControlStack/Scenarios/SC28Liveness.lean:174 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_example : (run [9] 10 full (run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0]) ([2, 3, 1].map (fun a => .work 1 a a))).usage = [(1, 0, 2), (1, 0, 3), (1, 0, 1)]
~~~

## ControlStack/Scenarios/SC28Refinement.lean

### 1548. runC_cons

Source: ControlStack/Scenarios/SC28Refinement.lean:175 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runC_cons (G : ℕ) (s : CSt) (o : COp) (ops : List COp) : runC G s (o :: ops) = runC G (stepC G s o) ops
~~~

### 1549. runC_append

Source: ControlStack/Scenarios/SC28Refinement.lean:178 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem runC_append (G : ℕ) (s : CSt) (a b : List COp) : runC G s (a ++ b) = runC G (runC G s a) b
~~~

### 1550. procOf_mem

Source: ControlStack/Scenarios/SC28Refinement.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem procOf_mem {s : CSt} {pid : ℕ} {q : PR} (h : procOf s pid = some q) : q ∈ s.procs ∧ q.pid = pid
~~~

### 1551. consumeLease_spec

Source: ControlStack/Scenarios/SC28Refinement.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem consumeLease_spec {G : ℕ} {s : CSt} {pid x lid : ℕ} (h : consumeLease G s pid x = some lid) : ∃ q, procOf s pid = some q ∧ q.alive = true ∧ q.cg = some lid ∧ 1 ≤ x ∧ ∃ b, limitOf s lid = some b ∧ counter s lid + x ≤ b ∧ runCounter s + x ≤ G
~~~

### 1552. consumeOutside_spec

Source: ControlStack/Scenarios/SC28Refinement.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem consumeOutside_spec {s : CSt} {pid x : ℕ} (h : consumeOutside s pid x = true) : ∃ q, procOf s pid = some q ∧ q.cg = none
~~~

### 1553. forkCg_spec

Source: ControlStack/Scenarios/SC28Refinement.lean:221 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forkCg_spec {s : CSt} {p ch : ℕ} {c : Option ℕ} (h : forkCg s p ch = some c) : ∃ q, procOf s p = some q ∧ q.alive = true ∧ q.cg = c ∧ ch ∉ s.procs.map PR.pid
~~~

### 1554. cinv_init

Source: ControlStack/Scenarios/SC28Refinement.lean:240 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_init : CInv cinit
~~~

### 1555. kill_pid

Source: ControlStack/Scenarios/SC28Refinement.lean:242 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem kill_pid (lid : ℕ) (q : PR) : (kill lid q).pid = q.pid
~~~

### 1556. kill_cg

Source: ControlStack/Scenarios/SC28Refinement.lean:243 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem kill_cg (lid : ℕ) (q : PR) : (kill lid q).cg = q.cg
~~~

### 1557. killPlaced_pid

Source: ControlStack/Scenarios/SC28Refinement.lean:244 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem killPlaced_pid (q : PR) : (killPlaced q).pid = q.pid
~~~

### 1558. killPlaced_cg

Source: ControlStack/Scenarios/SC28Refinement.lean:245 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem killPlaced_cg (q : PR) : (killPlaced q).cg = q.cg
~~~

### 1559. kill_dead

Source: ControlStack/Scenarios/SC28Refinement.lean:247 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem kill_dead {lid : ℕ} {q : PR} (hk : q.cg = some lid) : (kill lid q).alive = false
~~~

### 1560. kill_other

Source: ControlStack/Scenarios/SC28Refinement.lean:248 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem kill_other {lid : ℕ} {q : PR} (hk : ¬ q.cg = some lid) : kill lid q = q
~~~

### 1561. killPlaced_dead

Source: ControlStack/Scenarios/SC28Refinement.lean:249 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem killPlaced_dead {q : PR} (hk : q.cg.isSome = true) : (killPlaced q).alive = false
~~~

### 1562. killPlaced_other

Source: ControlStack/Scenarios/SC28Refinement.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem killPlaced_other {q : PR} (hk : ¬ q.cg.isSome = true) : killPlaced q = q
~~~

### 1563. map_kill_pid

Source: ControlStack/Scenarios/SC28Refinement.lean:253 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem map_kill_pid (lid : ℕ) (l : List PR) : (l.map (kill lid)).map PR.pid = l.map PR.pid
~~~

### 1564. map_killPlaced_pid

Source: ControlStack/Scenarios/SC28Refinement.lean:256 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem map_killPlaced_pid (l : List PR) : (l.map killPlaced).map PR.pid = l.map PR.pid
~~~

### 1565. cinv_step

Source: ControlStack/Scenarios/SC28Refinement.lean:259 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_step (G : ℕ) (s : CSt) (o : COp) (h : CInv s) : CInv (stepC G s o)
~~~

### 1566. cinv_run

Source: ControlStack/Scenarios/SC28Refinement.lean:340 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cinv_run (G : ℕ) (s : CSt) (ops : List COp) (h : CInv s) : CInv (runC G s ops)
~~~

### 1567. placed_fst_sub

Source: ControlStack/Scenarios/SC28Refinement.lean:353 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem placed_fst_sub (l : List PR) (w : ℕ) (hw : w ∉ l.map PR.pid) : w ∉ (placed l).map Prod.fst
~~~

### 1568. leaseOf_placed

Source: ControlStack/Scenarios/SC28Refinement.lean:366 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem leaseOf_placed (l : List PR) (hnd : (l.map PR.pid).Nodup) (w : ℕ) : ((placed l).find? (fun e => e.1 = w)).map Prod.snd = (l.find? (fun q => q.pid = w)).bind PR.cg
~~~

### 1569. placed_kill

Source: ControlStack/Scenarios/SC28Refinement.lean:402 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem placed_kill (lid : ℕ) (l : List PR) : placed (l.map (kill lid)) = placed l
~~~

### 1570. placed_killPlaced

Source: ControlStack/Scenarios/SC28Refinement.lean:405 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem placed_killPlaced (l : List PR) : placed (l.map killPlaced) = placed l
~~~

### 1571. simulation

Source: ControlStack/Scenarios/SC28Refinement.lean:429 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation (G : ℕ) (s : CSt) (o : COp) (h : CInv s) : α (stepC G s o) = SC28.run [0] G SC28.full (α s) (opsOf G s o)
~~~

### 1572. simulation_run

Source: ControlStack/Scenarios/SC28Refinement.lean:511 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem simulation_run (G : ℕ) (s : CSt) (ops : List COp) (h : CInv s) : α (runC G s ops) = SC28.run [0] G SC28.full (α s) (absTrace G s ops)
~~~

### 1573. opsOf_legal

Source: ControlStack/Scenarios/SC28Refinement.lean:520 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem opsOf_legal (G : ℕ) (s : CSt) (o : COp) : ∀ a ∈ opsOf G s o, SC28.legal a
~~~

### 1574. absTrace_legal

Source: ControlStack/Scenarios/SC28Refinement.lean:523 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem absTrace_legal (G : ℕ) (s : CSt) (ops : List COp) : ∀ a ∈ absTrace G s ops, SC28.legal a
~~~

### 1575. concrete_safe

Source: ControlStack/Scenarios/SC28Refinement.lean:539 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_safe (G : ℕ) (ops : List COp) : SC28.Good G (α (runC G cinit ops))
~~~

### 1576. concrete_counters_safe

Source: ControlStack/Scenarios/SC28Refinement.lean:545 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_counters_safe (G : ℕ) (ops : List COp) : runCounter (runC G cinit ops) ≤ G ∧ (∀ lid, counter (runC G cinit ops) lid ≤ (limitOf (runC G cinit ops) lid).getD 0) ∧ (runC G cinit ops).acct.length ≤ G
~~~

### 1577. concrete_revoked_stops

Source: ControlStack/Scenarios/SC28Refinement.lean:553 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_revoked_stops (G : ℕ) (pre post : List COp) (lid : ℕ) (hr : lid ∈ (runC G cinit pre).revoked) : counter (runC G cinit (pre ++ post)) lid = counter (runC G cinit pre) lid
~~~

### 1578. concrete_halt_freezes

Source: ControlStack/Scenarios/SC28Refinement.lean:560 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem concrete_halt_freezes (G : ℕ) (pre post : List COp) (hh : (runC G cinit pre).halted = true) : (runC G cinit (pre ++ post)).acct = (runC G cinit pre).acct
~~~

### 1579. step_placed

Source: ControlStack/Scenarios/SC28Refinement.lean:573 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_placed (G : ℕ) (s : CSt) (o : COp) (hu : isUnplaced o = false) (hall : ∀ q ∈ s.procs, q.cg ≠ none) (hout : s.outside = []) : (∀ q ∈ (stepC G s o).procs, q.cg ≠ none) ∧ (stepC G s o).outside = []
~~~

### 1580. exclusive_placement_safe

Source: ControlStack/Scenarios/SC28Refinement.lean:619 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exclusive_placement_safe (G : ℕ) (ops : List COp) (hu : ∀ o ∈ ops, isUnplaced o = false) : (runC G cinit ops).outside = [] ∧ realTotal (runC G cinit ops) ≤ G
~~~

### 1581. unplaced_invisible

Source: ControlStack/Scenarios/SC28Refinement.lean:648 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unplaced_invisible : realTotal (runC 10 cinit unplacedTrace) = 100 ∧ (α (runC 10 cinit unplacedTrace)).usage = [] ∧ (α (runC 10 cinit unplacedTrace)).ledger = [] ∧ (runC 10 cinit placedTrace).acct = [(7, 1, 10)] ∧ realTotal (runC 10 cinit placedTrace) = 10 ∧ (procOf (runC 10 cinit placedTrace) 8).bind PR.cg = some 1
~~~

### 1582. revoke_witness

Source: ControlStack/Scenarios/SC28Refinement.lean:656 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem revoke_witness : let t
~~~

## ControlStack/SideChannel.lean

### 1583. per_seed_side

Source: ControlStack/SideChannel.lean:31 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem per_seed_side {M V S O : Type} [Fintype M] [Fintype V] [Fintype S] [Fintype O] (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (enc : M → V × S → ℝ) (dec : V × O → M → ℝ) (henc : ∀ m, IsDist (enc m)) (hdec : ∀ y, IsDist (dec y)) : ∑ m, ∑ x : V × S, enc m x * ∑ o, W x.2 o * dec (x.1, o) m ≤ (Fintype.card V : ℝ) * ∑ o, c o
~~~

### 1584. side_bound

Source: ControlStack/SideChannel.lean:78 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem side_bound {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O] [Nonempty M] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ W enc dec ≤ (Fintype.card V : ℝ) * (∑ o, c o) / (Fintype.card M : ℝ)
~~~

### 1585. side_bound_uninfluenced

Source: ControlStack/SideChannel.lean:95 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem side_bound_uninfluenced {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O] [Nonempty M] (ρ : Ω → ℝ) (w : O → ℝ) (hw : IsDist w) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ (fun _ => w) enc dec ≤ (Fintype.card V : ℝ) / (Fintype.card M : ℝ)
~~~

### 1586. side_bound_trivial

Source: ControlStack/SideChannel.lean:104 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem side_bound_trivial {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O] [Nonempty M] (ρ : Ω → ℝ) (W : S → O → ℝ) (hW : ∀ s, IsDist (W s)) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ W enc dec ≤ (Fintype.card V : ℝ) * (Fintype.card O : ℝ) / (Fintype.card M : ℝ)
~~~

### 1587. dom_pi

Source: ControlStack/SideChannel.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dom_pi {E : ℕ} {S O : Fin E → Type} [∀ e, Fintype (O e)] (W : (e : Fin E) → S e → O e → ℝ) (c : (e : Fin E) → O e → ℝ) (hW0 : ∀ e s o, 0 ≤ W e s o) (hc : ∀ e s o, W e s o ≤ c e o) : (∀ (s : (e : Fin E) → S e) (o : (e : Fin E) → O e), ∏ e, W e (s e) (o e) ≤ ∏ e, c e (o e)) ∧ ∑ o : ((e : Fin E) → O e), ∏ e, c e (o e) = ∏ e, ∑ o, c e o
~~~

### 1588. side_as_covert

Source: ControlStack/SideChannel.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem side_as_covert {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) : sideSuccess ρ W enc dec = successProb ρ (fun ω m y => ∑ s, enc ω m (y.1, s) * W s y.2) dec
~~~

### 1589. bsc_dom

Source: ControlStack/SideChannel.lean:147 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bsc_dom (q : ℝ) (hq : q ≤ 1 / 2) : ∀ s o, bsc q s o ≤ 1 - q
~~~

### 1590. bsc_dist

Source: ControlStack/SideChannel.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bsc_dist (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (s : Bool) : IsDist (bsc q s)
~~~

## ControlStack/SoftHockey.lean

### 1591. viewLaw_nonneg

Source: ControlStack/SoftHockey.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem viewLaw_nonneg {Z : Type} [Fintype Z] (c : ProbComp Z) (z : Z) : 0 ≤ viewLaw c z
~~~

### 1592. viewLaw_sum

Source: ControlStack/SoftHockey.lean:22 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem viewLaw_sum {Z : Type} [Fintype Z] (c : ProbComp Z) : ∑ z, viewLaw c z = 1
~~~

### 1593. passRule_isRule

Source: ControlStack/SoftHockey.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem passRule_isRule {Z : Type} (D : Z → ProbComp Bool) : isRule (fun z => (Pr[= true | D z]).toReal)
~~~

### 1594. viewLaw_pass

Source: ControlStack/SoftHockey.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem viewLaw_pass {Z : Type} [Fintype Z] (c : ProbComp Z) (D : Z → ProbComp Bool) : ∑ z, viewLaw c z * (Pr[= true | D z]).toReal = (Pr[= true | c >>= D]).toReal
~~~

### 1595. hockey_pass_bound

Source: ControlStack/SoftHockey.lean:38 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hockey_pass_bound {Z : Type} [Fintype Z] (η : ℝ) (P Q : Z → ℝ) (D : Z → ProbComp Bool) : (∑ z, P z * (Pr[= true | D z]).toReal) ≤ Real.exp η * (∑ z, Q z * (Pr[= true | D z]).toReal) + hs η P Q
~~~

### 1596. operational_hockey_bound

Source: ControlStack/SoftHockey.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem operational_hockey_bound {Z : Type} [Fintype Z] (η δ : ℝ) (H : ProbComp Z) (X : ProbComp Z) (D : Z → ProbComp Bool) (hδ : hs η (viewLaw X) (viewLaw H) ≤ δ) : (Pr[= true | X >>= D]).toReal ≤ Real.exp η * (Pr[= true | H >>= D]).toReal + δ
~~~

### 1597. softEndToEndHockey

Source: ControlStack/SoftHockey.lean:71 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem softEndToEndHockey {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) (r η δ : ℝ) (hns : 1 ≤ ns) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hδ0 : 0 ≤ δ) (hrec : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) (hhs : ∀ x, Bad x → hs η (viewLaw (M x)) (viewLaw (H >>= M)) ≤ δ) : (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal ≤ (1 - r) + r * (δ + Real.exp η * ((ns : ℝ) / ((nh : ℝ) + 1)))
~~~

## ControlStack/SoftSlack.lean

### 1598. rejection_rate

Source: ControlStack/SoftSlack.lean:32 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rejection_rate (d : ℕ) : (Pr[= true | rejectionCoin d]).toReal = 1 / ((d + 1 : ℕ) : ℝ)
~~~

### 1599. survives_step

Source: ControlStack/SoftSlack.lean:39 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survives_step {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (d n : ℕ) : Pr[= true | survives H M D d (n + 1)] = Pr[= true | H >>= M >>= D] * Pr[= false | rejectionCoin d] * Pr[= true | survives H M D d n] + Pr[= false | H >>= M >>= D] * Pr[= true | survives H M D d n]
~~~

### 1600. survives_step_real

Source: ControlStack/SoftSlack.lean:58 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survives_step_real {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (d n : ℕ) : (Pr[= true | survives H M D d (n + 1)]).toReal = (1 - (Pr[= true | H >>= M >>= D]).toReal / ((d + 1 : ℕ) : ℝ)) * (Pr[= true | survives H M D d n]).toReal
~~~

### 1601. bridge

Source: ControlStack/SoftSlack.lean:75 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bridge : BridgeClaim
~~~

### 1602. geom_poly_bound

Source: ControlStack/SoftSlack.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem geom_poly_bound (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (1 + (n : ℝ) * x) * (1 - x) ^ n ≤ 1
~~~

### 1603. soft_survival_first_moment

Source: ControlStack/SoftSlack.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem soft_survival_first_moment (nh ns : ℕ) (h : ℝ) (hns : 1 ≤ ns) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : h * (1 - h / (ns : ℝ)) ^ nh ≤ (ns : ℝ) / ((nh : ℝ) + 1)
~~~

### 1604. protocol_factorization

Source: ControlStack/SoftSlack.lean:147 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem protocol_factorization {X Z Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) : (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal = ∑ ω, (Pr[= ω | ρ]).toReal * (Pr[= true | survives H M (D ω) (ns - 1) nh]).toReal * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
~~~

### 1605. protocol_survival_formula

Source: ControlStack/SoftSlack.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem protocol_survival_formula {X Z Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) (hns : 1 ≤ ns) : (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal = ∑ ω, (Pr[= ω | ρ]).toReal * (1 - (Pr[= true | H >>= M >>= D ω]).toReal / (ns : ℝ)) ^ nh * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
~~~

### 1606. softEndToEnd

Source: ControlStack/SoftSlack.lean:188 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem softEndToEnd {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) (r L : ℝ) (hns : 1 ≤ ns) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hrec : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) (hdom : ∀ x, Bad x → ∀ z, (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) : (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal ≤ (1 - r) + r * (L * ((ns : ℝ) / ((nh : ℝ) + 1)))
~~~

## ControlStack/Spike.lean

### 1607. distinguish_le_tv

Source: ControlStack/Spike.lean:17 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem distinguish_le_tv {X Z : Type} (M : X → ProbComp Z) (PA PH : ProbComp X) (D : Z → ProbComp Bool) : |Pr[= true | PA >>= M >>= D].toReal - Pr[= true | PH >>= M >>= D].toReal| ≤ tvDist (PA >>= M) (PH >>= M)
~~~

### 1608. mediated_tv_le

Source: ControlStack/Spike.lean:24 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mediated_tv_le {X Z : Type} (M : X → ProbComp Z) (PA PH : ProbComp X) : tvDist (PA >>= M) (PH >>= M) ≤ tvDist PA PH
~~~

## ControlStack/StratifiedGame.lean

### 1609. classPasses_bridge

Source: ControlStack/StratifiedGame.lean:28 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classPasses_bridge {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (m sc : ℕ) : (Pr[= true | classPasses H M D m sc]).toReal = binCDF m sc (Pr[= true | H >>= M >>= D]).toReal
~~~

### 1610. stratifiedSurvives_prob

Source: ControlStack/StratifiedGame.lean:37 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedSurvives_prob {X Z C : Type} (H : C → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (m sc : ℕ) (classes : List C) : (Pr[= true | stratifiedSurvives H M D m sc classes]).toReal = (classes.map fun e => (Pr[= true | classPasses (H e) M D m sc]).toReal).prod
~~~

### 1611. stratifiedSurvives_binomial

Source: ControlStack/StratifiedGame.lean:54 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedSurvives_binomial {X Z C : Type} (H : C → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (m sc : ℕ) (classes : List C) : (Pr[= true | stratifiedSurvives H M D m sc classes]).toReal = (classes.map fun e => binCDF m sc (Pr[= true | H e >>= M >>= D]).toReal).prod
~~~

### 1612. stratifiedProtocol_factorization

Source: ControlStack/StratifiedGame.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedProtocol_factorization {X Z C Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : Ω → C → ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (classes : List C) (m sc b N : ℕ) : (Pr[= true | stratifiedProtocolGame Bad ρ H M D π A classes m sc b N]).toReal = ∑ ω, (Pr[= ω | ρ]).toReal * (Pr[= true | stratifiedSurvives (H ω) M (D ω) m sc classes]).toReal * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
~~~

### 1613. stratifiedProtocol_binomial

Source: ControlStack/StratifiedGame.lean:103 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedProtocol_binomial {X Z C Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : Ω → C → ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (classes : List C) (m sc b N : ℕ) : (Pr[= true | stratifiedProtocolGame Bad ρ H M D π A classes m sc b N]).toReal = ∑ ω, (Pr[= ω | ρ]).toReal * (classes.map fun e => binCDF m sc (Pr[= true | H ω e >>= M >>= D ω]).toReal).prod * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
~~~

### 1614. listProduct_nonneg

Source: ControlStack/StratifiedGame.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem listProduct_nonneg {C : Type} (classes : List C) (f : C → ℝ) (hf0 : ∀ e ∈ classes, 0 ≤ f e) : 0 ≤ (classes.map f).prod
~~~

### 1615. listProduct_le_one

Source: ControlStack/StratifiedGame.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem listProduct_le_one {C : Type} (classes : List C) (f : C → ℝ) (hf0 : ∀ e ∈ classes, 0 ≤ f e) (hf1 : ∀ e ∈ classes, f e ≤ 1) : (classes.map f).prod ≤ 1
~~~

### 1616. listProduct_le_factor

Source: ControlStack/StratifiedGame.lean:148 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem listProduct_le_factor {C : Type} (classes : List C) (f : C → ℝ) (hf0 : ∀ e ∈ classes, 0 ≤ f e) (hf1 : ∀ e ∈ classes, f e ≤ 1) (e : C) (he : e ∈ classes) : (classes.map f).prod ≤ f e
~~~

### 1617. stratifiedProtocolEndToEnd

Source: ControlStack/StratifiedGame.lean:179 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedProtocolEndToEnd {X Z C Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (classOf : X → C) (classes : List C) (ρ : ProbComp Ω) (H : Ω → C → ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (m sc b N : ℕ) (r L : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hrec : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) (hclass : ∀ x, Bad x → classOf x ∈ classes) (hdom : ∀ ω x z, Bad x → (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H ω (classOf x) >>= M]).toReal) : (Pr[= true | stratifiedProtocolGame Bad ρ H M D π A classes m sc b N]).toReal ≤ (1 - r) + r * (L * (((sc : ℝ) + 1) / ((m : ℝ) + 1)))
~~~

## ControlStack/TrustedBroker.lean

### 1618. initial_safe

Source: ControlStack/TrustedBroker.lean:69 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem initial_safe (cap : Nat) : Safe (initial cap)
~~~

### 1619. initial_coherent

Source: ControlStack/TrustedBroker.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem initial_coherent (cap : Nat) : Coherent (initial cap)
~~~

### 1620. nonce_history_redundant

Source: ControlStack/TrustedBroker.lean:80 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nonce_history_redundant (s : State) (coherent : Coherent s) (nonce : Nat) (a : Approval) (lookup : s.approvals nonce = some a) (unused : a.used = false) : nonce ∉ s.consumed
~~~

### 1621. committed_nonce_unusable

Source: ControlStack/TrustedBroker.lean:112 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem committed_nonce_unusable (roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease) (now : Nat) (r' : Request) (a' : Approval) (l' : Lease) (sameNonce : r'.nonce = r.nonce) : ¬ Allowed roles (committed s r a l) now r' a' l'
~~~

### 1622. transaction_preserves

Source: ControlStack/TrustedBroker.lean:158 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem transaction_preserves (roles : Roles) (s t : State) (safe : Safe s) (step : Step roles s t) : Safe t
~~~

### 1623. halted_absorbing

Source: ControlStack/TrustedBroker.lean:196 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halted_absorbing (roles : Roles) (s t : State) (halted : s.halted = true) (step : Step roles s t) : t.halted = true ∧ t.releases = s.releases
~~~

### 1624. transaction_coherent

Source: ControlStack/TrustedBroker.lean:201 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem transaction_coherent (roles : Roles) (s t : State) (coherent : Coherent s) (step : Step roles s t) : Coherent t
~~~

### 1625. trace_preserves

Source: ControlStack/TrustedBroker.lean:233 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem trace_preserves (roles : Roles) (s t : State) (safe : Safe s) (trace : Trace roles s t) : Safe t
~~~

### 1626. trace_coherent

Source: ControlStack/TrustedBroker.lean:239 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem trace_coherent (roles : Roles) (s t : State) (coherent : Coherent s) (trace : Trace roles s t) : Coherent t
~~~

### 1627. trace_halt_absorbing

Source: ControlStack/TrustedBroker.lean:245 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem trace_halt_absorbing (roles : Roles) (s t : State) (halted : s.halted = true) (trace : Trace roles s t) : t.halted = true ∧ t.releases = s.releases
~~~

## ControlStack/UseQ.lean

### 1628. foldl_add_eq

Source: ControlStack/UseQ.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_add_eq {m : ℕ} (f : Fin m → ℚ) : ∀ (l : List (Fin m)) (acc : ℚ), l.foldl (fun acc i => acc + f i) acc = acc + (l.map f).sum
~~~

### 1629. sumQ_eq

Source: ControlStack/UseQ.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sumQ_eq (m : ℕ) (f : Fin m → ℚ) : sumQ m f = ∑ i, f i
~~~

### 1630. checkUseQ_spec

Source: ControlStack/UseQ.lean:33 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkUseQ_spec {N m t : ℕ} {rew : Fin t → Fin N → Fin m → ℚ} {K : Fin t → Fin N → Fin m → Fin m → ℚ} {adm : Fin t → Fin N → Fin m → Bool} {W : Fin (N + 1) → Fin m → ℚ} {s₀ : Fin m} {floor : ℚ} (hc : checkUseQ N m t rew K adm W s₀ floor = true) : 0 < t ∧ floor ≤ W (Fin.last N) s₀ ∧ (∀ s, W 0 s ≤ 0) ∧ (∀ i s, ∃ th, adm th i s = true) ∧ (∀ th i s, adm th i s = true → W i.succ s ≤ rew th i s + ∑ s', K th i s s' * W i.castSucc s')
~~~

### 1631. selector_exists

Source: ControlStack/UseQ.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem selector_exists {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ) (K : Fin t → Fin N → Fin m → Fin m → ℚ) (adm : Fin t → Fin N → Fin m → Bool) (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ) (hc : checkUseQ N m t rew K adm W s₀ floor = true) : ∃ θ : ℕ → List (Fin m) → Fin m → Fin t, ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true
~~~

### 1632. checkUseQ_sound

Source: ControlStack/UseQ.lean:76 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkUseQ_sound {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ) (K : Fin t → Fin N → Fin m → Fin m → ℚ) (adm : Fin t → Fin N → Fin m → Bool) (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ) (θ : ℕ → List (Fin m) → Fin m → Fin t) (hc : checkUseQ N m t rew K adm W s₀ floor = true) (hK : ∀ th i s, adm th i s = true → ∀ s', 0 ≤ K th i s s') (hθ : ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true) : (floor : ℝ) ≤ honestValue rew K θ N s₀ []
~~~

### 1633. claim

Source: ControlStack/UseQ.lean:156 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 1634. witness

Source: ControlStack/UseQ.lean:163 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## ControlStack/Witnesses/DeputyBridge.lean

### 1635. payment_deputy_breaks_deploy_gate

Source: ControlStack/Witnesses/DeputyBridge.lean:40 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem payment_deputy_breaks_deploy_gate : let p
~~~

### 1636. approved_inv

Source: ControlStack/Witnesses/DeputyBridge.lean:53 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem approved_inv : SC26.Inv SC26.R0 20 (SC26.run SC26.R0 20 SC26.full SC26.init [.request 1 SC26.tx1, .approve 2 0 SC26.tx1])
~~~

### 1637. payment_deputy_not_admissible

Source: ControlStack/Witnesses/DeputyBridge.lean:58 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem payment_deputy_not_admissible : ¬ BridgeAdmissible (SC26.spec SC26.R0 20) (SC16.spec R16 id) paymentDeputy
~~~

### 1638. gated_deputy_admissible

Source: ControlStack/Witnesses/DeputyBridge.lean:71 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gated_deputy_admissible (h : ℕ → ℕ) (cap : ℕ) (R : SC26.Roles) : BridgeAdmissible (SC26.spec R cap) (SC16.spec R16 h) (gatedDeputy h)
~~~

### 1639. gated_deputy_deploys_nothing

Source: ControlStack/Witnesses/DeputyBridge.lean:79 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gated_deputy_deploys_nothing : ((withBridge (SC26.sys SC26.R0 20) (SC16.sys R16 id) (gatedDeputy id)).run start trace).s₂.deployed = []
~~~

## ControlStack/Witnesses/LeakWitness.lean

### 1640. K_nonneg

Source: ControlStack/Witnesses/LeakWitness.lean:45 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem K_nonneg (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) (z : Unit × AOut Bool) : 0 ≤ K ε S h z
~~~

### 1641. K_sum

Source: ControlStack/Witnesses/LeakWitness.lean:49 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem K_sum (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) : ∑ z, K ε S h z ≤ 1
~~~

### 1642. K_cons

Source: ControlStack/Witnesses/LeakWitness.lean:59 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem K_cons (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) (y : Unit) (o : AOut Bool) (hK : K ε S h (y, o) ≠ 0) : o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length))
~~~

### 1643. K_dom

Source: ControlStack/Witnesses/LeakWitness.lean:67 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem K_dom (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) (o : AOut Bool) (hf : o.2.2 = false) : ∑ y, K ε S h (y, o) ≤ cl ε (h.map Prod.snd) o
~~~

### 1644. cl_nonneg

Source: ControlStack/Witnesses/LeakWitness.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cl_nonneg (g : List (AOut Bool)) (o : AOut Bool) : 0 ≤ cl ε g o
~~~

### 1645. leak_mass

Source: ControlStack/Witnesses/LeakWitness.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem leak_mass : mass (dropStop caughtFlag (cl ε)) 2 [] = 2 * (1 - ε)
~~~

### 1646. leak_bound

Source: ControlStack/Witnesses/LeakWitness.lean:93 | Family: F6 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem leak_bound : ∑ S : Finset (Fin 2), (if S ∈ AuditBudget.randomSchedules 2 1 then (Nat.choose 2 1 : ℝ)⁻¹ else 0) * val (K ε S) (survInd 1 S) 2 [] ≤ 1 - ε
~~~

## ControlStack/Witnesses/Necessity.lean

### 1647. jointSuccess_indep

Source: ControlStack/Witnesses/Necessity.lean:35 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem jointSuccess_indep {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V] (ρ : Ω → ℝ) (enc : Ω → M → V → ℝ) (dec : Ω → V → M → ℝ) : jointSuccess (fun ω _ => ρ ω * (Fintype.card M : ℝ)⁻¹) enc dec = successProb ρ enc dec
~~~

### 1648. seed_secret_breaks_covert

Source: ControlStack/Witnesses/Necessity.lean:48 | Family: F2 | Adversary: SHARED_SEED | Status: SOURCE_ONLY

~~~lean
theorem seed_secret_breaks_covert {M : Type} [Fintype M] [DecidableEq M] (hM : 2 ≤ Fintype.card M) : jointSuccess (fun (ω m : M) => if ω = m then (Fintype.card M : ℝ)⁻¹ else 0) (fun (_ _ : M) (_ : Unit) => (1 : ℝ)) (fun (ω : M) (_ : Unit) (m : M) => if m = ω then (1 : ℝ) else 0) = 1 ∧ (Fintype.card Unit : ℝ) / (Fintype.card M : ℝ) < 1
~~~

### 1649. comono_dist

Source: ControlStack/Witnesses/Necessity.lean:79 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem comono_dist (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsDist (comono p)
~~~

### 1650. comono_marginal

Source: ControlStack/Witnesses/Necessity.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem comono_marginal (p : ℝ) (i : Fin 64) : ∑ x, comono p x * (if x i = true then 1 else 0) = p
~~~

### 1651. correlated_lifetimes_break_gate

Source: ControlStack/Witnesses/Necessity.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem correlated_lifetimes_break_gate : (∀ i : Fin 64, ∑ x, comono (9 / 10) x * (if x i = true then 1 else 0) = 9 / 10) ∧ ∑ x, comono (9 / 10) x * (if 63 ≤ count x then 1 else 0) = 9 / 10 ∧ ScenarioAUsefulness.passProb (9 / 10) ≤ 1 / 80 ∧ (1 : ℝ) / 80 < 9 / 10
~~~

### 1652. marginal_certs_dont_compose

Source: ControlStack/Witnesses/Necessity.lean:117 | Family: F8 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem marginal_certs_dont_compose : (∀ m b, ∑ o : Bool × Bool, xorLaw m o * (if o.1 = b then 1 else 0) = 1 / 2) ∧ (∀ m b, ∑ o : Bool × Bool, xorLaw m o * (if o.2 = b then 1 else 0) = 1 / 2) ∧ (1 / 2 : ℝ) * ∑ m : Bool, ∑ o : Bool × Bool, xorLaw m o * (if xor o.1 o.2 = m then 1 else 0) = 1
~~~

### 1653. shared_score_product_unsound

Source: ControlStack/Witnesses/Necessity.lean:130 | Family: F8 | Adversary: SHARED_SEED | Status: SOURCE_ONLY

~~~lean
theorem shared_score_product_unsound : (∑ s : Bool, scoreLaw s * (if s = false then 1 else 0)) = 1 / 10 ∧ (∑ s : Bool, scoreLaw s * (if s = false ∧ s = false then 1 else 0)) = 1 / 10 ∧ (1 / 10 : ℝ) * (1 / 10) < 1 / 10
~~~

### 1654. exhausted_no_audit

Source: ControlStack/Witnesses/Necessity.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exhausted_no_audit {N : ℕ} (B : ℕ) (flags : Fin N → Bool) (A : Finset (Fin N)) (h : ∀ i ∈ A, B ≤ (Finset.univ.filter (fun j : Fin N => j < i ∧ flags j = true)).card) : ∀ i ∈ A, audited B flags i = false
~~~

### 1655. audited_last

Source: ControlStack/Witnesses/Necessity.lean:164 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem audited_last (b : Bool × Bool × Bool) : audited 1 (flagsOf b) 3 = (!b.1 && !b.2.1 && !b.2.2)
~~~

### 1656. fp_exhaustion_breaks_audit

Source: ControlStack/Witnesses/Necessity.lean:176 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fp_exhaustion_breaks_audit : (∑ b : Bool × Bool × Bool, (1 / 8 : ℚ) * (if audited 1 (flagsOf b) 3 = false then 1 else 0)) = 7 / 8 ∧ (Nat.choose 3 1 : ℚ) / Nat.choose 4 1 = 3 / 4
~~~

## proofs/CANONF1.lean

### 1657. k_aren_comp

Source: proofs/CANONF1.lean:4 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_aren_comp (f g : ℕ → ℕ) (a : AExp) : (a.rename f).rename g = a.rename (g ∘ f)
~~~

### 1658. k_bren_comp

Source: proofs/CANONF1.lean:7 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_bren_comp (f g : ℕ → ℕ) (b : BExp) : (b.rename f).rename g = b.rename (g ∘ f)
~~~

### 1659. k_sren_comp

Source: proofs/CANONF1.lean:10 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_sren_comp (f g : ℕ → ℕ) (s : Stmt) : (s.rename f).rename g = s.rename (g ∘ f)
~~~

### 1660. k_pren_comp

Source: proofs/CANONF1.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_pren_comp (f g : ℕ → ℕ) (p : Prog) : (p.rename f).rename g = p.rename (g ∘ f)
~~~

### 1661. k_aocc_ren

Source: proofs/CANONF1.lean:16 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_aocc_ren (f : ℕ → ℕ) (a : AExp) : (a.rename f).occ = a.occ.map f
~~~

### 1662. k_bocc_ren

Source: proofs/CANONF1.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_bocc_ren (f : ℕ → ℕ) (b : BExp) : (b.rename f).occ = b.occ.map f
~~~

### 1663. k_socc_ren

Source: proofs/CANONF1.lean:22 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_socc_ren (f : ℕ → ℕ) (s : Stmt) : (s.rename f).occ = s.occ.map f
~~~

### 1664. k_pocc_ren

Source: proofs/CANONF1.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_pocc_ren (f : ℕ → ℕ) (p : Prog) : (p.rename f).occ = p.occ.map f
~~~

### 1665. k_aren_congr

Source: proofs/CANONF1.lean:28 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_aren_congr {f g : ℕ → ℕ} (a : AExp) (h : ∀ v ∈ a.occ, f v = g v) : a.rename f = a.rename g
~~~

### 1666. k_bren_congr

Source: proofs/CANONF1.lean:43 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_bren_congr {f g : ℕ → ℕ} (b : BExp) (h : ∀ v ∈ b.occ, f v = g v) : b.rename f = b.rename g
~~~

### 1667. k_sren_congr

Source: proofs/CANONF1.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_sren_congr {f g : ℕ → ℕ} (s : Stmt) (h : ∀ v ∈ s.occ, f v = g v) : s.rename f = s.rename g
~~~

### 1668. k_pren_congr

Source: proofs/CANONF1.lean:85 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_pren_congr {f g : ℕ → ℕ} (p : Prog) (h : ∀ v ∈ p.occ, f v = g v) : p.rename f = p.rename g
~~~

### 1669. k_pren_id

Source: proofs/CANONF1.lean:91 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_pren_id (p : Prog) : p.rename id = p
~~~

### 1670. k_aeval_ren

Source: proofs/CANONF1.lean:101 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_aeval_ren {f : ℕ → ℕ} {σ τ : State} (a : AExp) (h : ∀ v ∈ a.occ, τ (f v) = σ v) : (a.rename f).eval τ = a.eval σ
~~~

### 1671. k_beval_ren

Source: proofs/CANONF1.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_beval_ren {f : ℕ → ℕ} {σ τ : State} (b : BExp) (h : ∀ v ∈ b.occ, τ (f v) = σ v) : (b.rename f).eval τ = b.eval σ
~~~

### 1672. k_exec_seq_iff

Source: proofs/CANONF1.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_exec_seq_iff {s t : Stmt} {σ σ'' : State} : Exec (.seq s t) σ σ'' ↔ ∃ σ', Exec s σ σ' ∧ Exec t σ' σ''
~~~

### 1673. k_exec_ite_iff

Source: proofs/CANONF1.lean:151 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_exec_ite_iff {b : BExp} {s t : Stmt} {σ σ' : State} : Exec (.ite b s t) σ σ' ↔ (b.eval σ = true ∧ Exec s σ σ') ∨ (b.eval σ = false ∧ Exec t σ σ')
~~~

### 1674. k_exec_cfor_iff

Source: proofs/CANONF1.lean:162 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_exec_cfor_iff {i : Stmt} {c : BExp} {st body : Stmt} {σ σ' : State} : Exec (.cfor i c st body) σ σ' ↔ Exec (.seq i (.while c (.seq body st))) σ σ'
~~~

### 1675. k_while_mono

Source: proofs/CANONF1.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_while_mono {b : BExp} {s s' : Stmt} (h : ∀ σ σ', Exec s σ σ' → Exec s' σ σ') : ∀ σ σ', Exec (.while b s) σ σ' → Exec (.while b s') σ σ'
~~~

### 1676. k_seq_congr

Source: proofs/CANONF1.lean:189 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_seq_congr {s s' t t' : Stmt} (h1 : KSEq s s') (h2 : KSEq t t') : KSEq (.seq s t) (.seq s' t')
~~~

### 1677. k_ite_congr

Source: proofs/CANONF1.lean:195 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_ite_congr {b : BExp} {s s' t t' : Stmt} (h1 : KSEq s s') (h2 : KSEq t t') : KSEq (.ite b s t) (.ite b s' t')
~~~

### 1678. k_while_congr

Source: proofs/CANONF1.lean:201 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_while_congr {b : BExp} {s s' : Stmt} (h : KSEq s s') : KSEq (.while b s) (.while b s')
~~~

### 1679. k_cfor_congr

Source: proofs/CANONF1.lean:206 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_cfor_congr {i i' : Stmt} {c : BExp} {st st' b b' : Stmt} (hi : KSEq i i') (hst : KSEq st st') (hb : KSEq b b') : KSEq (.cfor i c st b) (.cfor i' c st' b')
~~~

### 1680. k_sEq_refl

Source: proofs/CANONF1.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_sEq_refl (s : Stmt) : KSEq s s
~~~

### 1681. k_forstep_sEq

Source: proofs/CANONF1.lean:214 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_forstep_sEq {s t : Stmt} (h : ForStep s t) : KSEq s t
~~~

### 1682. k_eqv_sEq

Source: proofs/CANONF1.lean:234 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_sEq {s t : Stmt} (h : Relation.EqvGen ForStep s t) : KSEq s t
~~~

### 1683. k_exec_rename

Source: proofs/CANONF1.lean:243 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_exec_rename {f : ℕ → ℕ} {V : Set ℕ} (hf : Set.InjOn f V) {s : Stmt} {σ σ' : State} (h : Exec s σ σ') : (∀ v ∈ s.occ, v ∈ V) → ∀ τ : State, (∀ v ∈ V, τ (f v) = σ v) → ∃ τ', Exec (s.rename f) τ τ' ∧ ∀ v ∈ V, τ' (f v) = σ' v
~~~

### 1684. k_runs_rename

Source: proofs/CANONF1.lean:294 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_runs_rename {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) {ins : List ℤ} {out : ℤ} (h : Runs p ins out) : Runs (p.rename f) ins out
~~~

### 1685. k_ren_inverse

Source: proofs/CANONF1.lean:311 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_ren_inverse {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) : ∃ g, Admissible g (p.rename f) ∧ (p.rename f).rename g = p
~~~

### 1686. k_runs_rename_iff

Source: proofs/CANONF1.lean:349 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_runs_rename_iff {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) (ins : List ℤ) (out : ℤ) : Runs p ins out ↔ Runs (p.rename f) ins out
~~~

### 1687. k_append_assoc

Source: proofs/CANONF1.lean:362 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_append_assoc (a b c : Stmt) : (a.append b).append c = a.append (b.append c)
~~~

### 1688. k_FF_step

Source: proofs/CANONF1.lean:369 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_FF_step {s t : Stmt} (h : ForStep s t) : KFF s = KFF t
~~~

### 1689. k_FF_eqv

Source: proofs/CANONF1.lean:398 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_FF_eqv {s t : Stmt} (h : Relation.EqvGen ForStep s t) : KFF s = KFF t
~~~

### 1690. k_desugar_ren

Source: proofs/CANONF1.lean:405 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_desugar_ren (f : ℕ → ℕ) (s : Stmt) : desugar (s.rename f) = (desugar s).rename f
~~~

### 1691. k_append_ren

Source: proofs/CANONF1.lean:408 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_append_ren (f : ℕ → ℕ) (a b : Stmt) : (a.append b).rename f = (a.rename f).append (b.rename f)
~~~

### 1692. k_flatten_ren

Source: proofs/CANONF1.lean:417 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_flatten_ren (f : ℕ → ℕ) (s : Stmt) : flatten (s.rename f) = (flatten s).rename f
~~~

### 1693. k_FF_ren

Source: proofs/CANONF1.lean:420 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_FF_ren (f : ℕ → ℕ) (s : Stmt) : KFF (s.rename f) = (KFF s).rename f
~~~

### 1694. k_occ_append

Source: proofs/CANONF1.lean:423 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_occ_append (a b : Stmt) : (a.append b).occ = a.occ ++ b.occ
~~~

### 1695. k_occ_flatten

Source: proofs/CANONF1.lean:430 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_occ_flatten (s : Stmt) : (flatten s).occ = s.occ
~~~

### 1696. k_mem_occ_desugar

Source: proofs/CANONF1.lean:433 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_occ_desugar (s : Stmt) (v : ℕ) : v ∈ (desugar s).occ ↔ v ∈ s.occ
~~~

### 1697. k_mem_occ_FF

Source: proofs/CANONF1.lean:444 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_occ_FF (s : Stmt) (v : ℕ) : v ∈ (KFF s).occ ↔ v ∈ s.occ
~~~

### 1698. k_firstOcc_eq

Source: proofs/CANONF1.lean:451 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_firstOcc_eq (l : List ℕ) : firstOcc l = l.foldl kstep []
~~~

### 1699. k_mem_foldl

Source: proofs/CANONF1.lean:453 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_foldl (l acc : List ℕ) (v : ℕ) : v ∈ l.foldl kstep acc ↔ v ∈ acc ∨ v ∈ l
~~~

### 1700. k_mem_firstOcc

Source: proofs/CANONF1.lean:472 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_firstOcc (l : List ℕ) (v : ℕ) : v ∈ firstOcc l ↔ v ∈ l
~~~

### 1701. k_foldl_map

Source: proofs/CANONF1.lean:476 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_foldl_map {f : ℕ → ℕ} {S : Set ℕ} (hf : Set.InjOn f S) (l acc : List ℕ) (hl : ∀ v ∈ l, v ∈ S) (hacc : ∀ v ∈ acc, v ∈ S) : (l.map f).foldl kstep (acc.map f) = (l.foldl kstep acc).map f
~~~

### 1702. k_firstOcc_map

Source: proofs/CANONF1.lean:509 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_firstOcc_map {f : ℕ → ℕ} {S : Set ℕ} (hf : Set.InjOn f S) (l : List ℕ) (hl : ∀ v ∈ l, v ∈ S) : firstOcc (l.map f) = (firstOcc l).map f
~~~

### 1703. k_idxOf_map

Source: proofs/CANONF1.lean:515 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_idxOf_map {f : ℕ → ℕ} {S : Set ℕ} (hf : Set.InjOn f S) (v : ℕ) (hv : v ∈ S) : ∀ (L : List ℕ), (∀ w ∈ L, w ∈ S) → (L.map f).idxOf (f v) = L.idxOf v | [], _ => rfl | a :: L, hL => by rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, k_idxOf_map hf v hv L (fun w hw => hL w (by simp [hw]))] have ha : a ∈ S
~~~

### 1704. k_canon_eq

Source: proofs/CANONF1.lean:532 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canon_eq (p : Prog) : canon p = kcanon' (desugarProg p)
~~~

### 1705. k_mem_locals

Source: proofs/CANONF1.lean:534 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_locals {d : Prog} {v : ℕ} : v ∈ d.locals ↔ v ∈ d.occ ∧ d.nparams ≤ v
~~~

### 1706. k_canonMap_ren

Source: proofs/CANONF1.lean:537 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canonMap_ren {f : ℕ → ℕ} {d : Prog} (hA : Admissible f d) (v : ℕ) (hv : v ∈ d.occ) : (d.rename f).canonMap (f v) = d.canonMap v
~~~

### 1707. k_canon'_ren

Source: proofs/CANONF1.lean:567 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canon'_ren {f : ℕ → ℕ} {d : Prog} (hA : Admissible f d) : kcanon' (d.rename f) = kcanon' d
~~~

### 1708. k_desugarProg_ren

Source: proofs/CANONF1.lean:575 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_desugarProg_ren (f : ℕ → ℕ) (p : Prog) : desugarProg (p.rename f) = (desugarProg p).rename f
~~~

### 1709. k_adm_desugar

Source: proofs/CANONF1.lean:581 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_adm_desugar {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) : Admissible f (desugarProg p)
~~~

### 1710. k_canon_step

Source: proofs/CANONF1.lean:590 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canon_step {p q : Prog} (h : Step p q) : canon p = canon q
~~~

### 1711. k_canon_syn

Source: proofs/CANONF1.lean:599 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canon_syn {p q : Prog} (h : SynEquiv p q) : canon p = canon q
~~~

### 1712. k_eqv_map

Source: proofs/CANONF1.lean:608 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_map {φ : Stmt → Stmt} (hφ : ∀ a b, ForStep a b → ForStep (φ a) (φ b)) {a b : Stmt} (h : Relation.EqvGen ForStep a b) : Relation.EqvGen ForStep (φ a) (φ b)
~~~

### 1713. k_eqv_seq

Source: proofs/CANONF1.lean:616 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_seq {s s' t t' : Stmt} (h1 : Relation.EqvGen ForStep s s') (h2 : Relation.EqvGen ForStep t t') : Relation.EqvGen ForStep (.seq s t) (.seq s' t')
~~~

### 1714. k_eqv_ite

Source: proofs/CANONF1.lean:621 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_ite {b : BExp} {s s' t t' : Stmt} (h1 : Relation.EqvGen ForStep s s') (h2 : Relation.EqvGen ForStep t t') : Relation.EqvGen ForStep (.ite b s t) (.ite b s' t')
~~~

### 1715. k_eqv_while

Source: proofs/CANONF1.lean:626 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_while {b : BExp} {s s' : Stmt} (h : Relation.EqvGen ForStep s s') : Relation.EqvGen ForStep (.while b s) (.while b s')
~~~

### 1716. k_eqv_cfor

Source: proofs/CANONF1.lean:630 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_cfor {i i' : Stmt} {c : BExp} {st st' body body' : Stmt} (hi : Relation.EqvGen ForStep i i') (hst : Relation.EqvGen ForStep st st') (hb : Relation.EqvGen ForStep body body') : Relation.EqvGen ForStep (.cfor i c st body) (.cfor i' c st' body')
~~~

### 1717. k_eqv_append

Source: proofs/CANONF1.lean:640 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_append (a b : Stmt) : Relation.EqvGen ForStep (.seq a b) (a.append b)
~~~

### 1718. k_eqv_flatten

Source: proofs/CANONF1.lean:646 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_flatten (s : Stmt) : Relation.EqvGen ForStep s (flatten s)
~~~

### 1719. k_eqv_desugar

Source: proofs/CANONF1.lean:655 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_desugar (s : Stmt) : Relation.EqvGen ForStep s (desugar s)
~~~

### 1720. k_eqv_FF

Source: proofs/CANONF1.lean:666 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_FF (s : Stmt) : Relation.EqvGen ForStep s (KFF s)
~~~

### 1721. k_lift

Source: proofs/CANONF1.lean:669 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_lift {k : ℕ} {ret : AExp} {body body' : Stmt} (h : Relation.EqvGen ForStep body body') : SynEquiv ⟨k, body, ret⟩ ⟨k, body', ret⟩
~~~

### 1722. k_adm_canonMap

Source: proofs/CANONF1.lean:677 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_adm_canonMap (d : Prog) : Admissible d.canonMap d
~~~

### 1723. k_syn_canon

Source: proofs/CANONF1.lean:693 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_syn_canon (p : Prog) : SynEquiv p (canon p)
~~~

### 1724. k_part2

Source: proofs/CANONF1.lean:697 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_part2 (p q : Prog) : canon p = canon q ↔ SynEquiv p q
~~~

### 1725. k_runs_step

Source: proofs/CANONF1.lean:705 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_runs_step {p q : Prog} (h : Step p q) (ins : List ℤ) (out : ℤ) : Runs p ins out ↔ Runs q ins out
~~~

### 1726. k_runs_syn

Source: proofs/CANONF1.lean:714 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_runs_syn {p q : Prog} (h : SynEquiv p q) (ins : List ℤ) (out : ℤ) : Runs p ins out ↔ Runs q ins out
~~~

### 1727. k_part1

Source: proofs/CANONF1.lean:722 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_part1 (p : Prog) (ins : List ℤ) (out : ℤ) : Runs (canon p) ins out ↔ Runs p ins out
~~~

### 1728. claim

Source: proofs/CANONF1.lean:725 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 1729. witness

Source: proofs/CANONF1.lean:741 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## proofs/SANDBOX2F1.lean

### 1730. fp2_split1

Source: proofs/SANDBOX2F1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fp2_split1 (W : Path) (sd : List Path) : PL_SANDBOX2F1.fixedPolicy2 W sd = [.bind [] [] .ro] ++ ([.tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++ sd.map (fun d => .bind d d .rw) ++ hiddenDirs.map .tmpfs ++ [.bind mathlibProj mathlibProj .ro])
~~~

### 1731. fp2_split2

Source: proofs/SANDBOX2F1.lean:10 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fp2_split2 (W : Path) (sd : List Path) : PL_SANDBOX2F1.fixedPolicy2 W sd = ([.bind [] [] .ro, .tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++ sd.map (fun d => .bind d d .rw)) ++ (hiddenDirs.map .tmpfs ++ [.bind mathlibProj mathlibProj .ro])
~~~

### 1732. part_a

Source: proofs/SANDBOX2F1.lean:16 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_a : ∀ W : Path, ["var", "tmp"] <+: W → ReadsHost (fixedPolicy W [home ++ [".agent-b"]]) (home ++ [".agent-b", "sessions", "s.jsonl"]) (home ++ [".agent-b", "sessions", "s.jsonl"])
~~~

### 1733. part_b

Source: proofs/SANDBOX2F1.lean:24 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_b : ∀ (W : Path) (stateDirs : List Path) (canWrite : Path → Prop) (p hp : Path), WritesHost (PL_SANDBOX2F1.fixedPolicy2 W stateDirs) canWrite p hp → W <+: hp ∨ ∃ d ∈ stateDirs, d <+: hp
~~~

### 1734. part_c

Source: proofs/SANDBOX2F1.lean:34 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c : ∀ (W : Path) (stateDirs : List Path) (p hp H : Path), ["var", "tmp"] <+: W → H ∈ hiddenDirs → H <+: hp → ReadsHost (PL_SANDBOX2F1.fixedPolicy2 W stateDirs) p hp → mathlibProj <+: hp
~~~

### 1735. claim

Source: proofs/SANDBOX2F1.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_SANDBOX2F1.Claim
~~~

### 1736. witness

Source: proofs/SANDBOX2F1.lean:66 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_SANDBOX2F1.Witness
~~~

## proofs/SANDBOXF1.lean

### 1737. eff_mem

Source: proofs/SANDBOXF1.lean:1 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem eff_mem {pol : Policy} {p : Path} {m : Mount} (h : effective pol p = some m) : m ∈ pol ∧ m.tgt <+: p
~~~

### 1738. eff_tail

Source: proofs/SANDBOXF1.lean:6 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem eff_tail {l1 l2 : Policy} {p : Path} {m x : Mount} (h : effective (l1 ++ l2) p = some m) (hx : x ∈ l2) (hP : x.tgt <+: p) : m ∈ l2
~~~

### 1739. head_eq

Source: proofs/SANDBOXF1.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem head_eq {a b : String} {as bs l : Path} (h1 : a :: as <+: l) (h2 : b :: bs <+: l) : a = b
~~~

### 1740. hidden_head

Source: proofs/SANDBOXF1.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hidden_head : ∀ H ∈ hiddenDirs, ∃ as, H = "home" :: as ∨ H = "tmp" :: as
~~~

### 1741. cur_split

Source: proofs/SANDBOXF1.lean:33 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cur_split (W : Path) : currentPolicy W = [.bind [] [] .rw] ++ ([.tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++ hiddenDirs.map .tmpfs ++ [.bind mathlibProj mathlibProj .ro])
~~~

### 1742. claim_a

Source: proofs/SANDBOXF1.lean:38 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_a : ∀ W : Path, ["var", "tmp"] <+: W → WritesHost (currentPolicy W) (fun hp => home <+: hp ∨ ["var", "tmp"] <+: hp) (home ++ [".toolchain", "bin", "lake"]) (home ++ [".toolchain", "bin", "lake"])
~~~

### 1743. claim_b

Source: proofs/SANDBOXF1.lean:47 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_b : ∀ (W : Path) (stateDirs : List Path) (canWrite : Path → Prop) (p hp : Path), WritesHost (fixedPolicy W stateDirs) canWrite p hp → W <+: hp ∨ ∃ d ∈ stateDirs, d <+: hp
~~~

### 1744. claim_c

Source: proofs/SANDBOXF1.lean:57 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_c : ∀ (W p hp H : Path), ["var", "tmp"] <+: W → H ∈ hiddenDirs → H <+: hp → ReadsHost (currentPolicy W) p hp → mathlibProj <+: hp
~~~

### 1745. claim

Source: proofs/SANDBOXF1.lean:81 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 1746. witness

Source: proofs/SANDBOXF1.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## proofs/TMCERTF1.lean

### 1747. claimS

Source: proofs/TMCERTF1.lean:2 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimS : ∀ (S A Θ : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ) (σ : RHist S A → S → A → ℝ) (θ : ℕ → RHist S A → S → A → Θ), AdmKNonneg N G adm → RiskCertUpTo N G adm V → IsPolicy σ → SelectorUpTo N adm θ → ∀ n, n ≤ N → ∀ s h, risk G θ σ n s h ≤ V n s
~~~

### 1748. claimP

Source: proofs/TMCERTF1.lean:29 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimP : ∀ (S A Θ : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (σ : RHist S A → S → A → ℝ) (θ : ℕ → RHist S A → S → A → Θ), (∀ n, n < N → ∀ s a th, adm n s a th → 0 ≤ (G th).cat n s a ∧ (∀ s', 0 ≤ (G th).K n s a s') ∧ (G th).cat n s a + ∑ s', (G th).K n s a s' ≤ 1) → IsPolicy σ → SelectorUpTo N adm θ → ∀ n, n ≤ N → ∀ s h, 0 ≤ risk G θ σ n s h ∧ risk G θ σ n s h ≤ 1
~~~

### 1749. claimS

Source: proofs/TMCERTF1.lean:63 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimS' : ∀ (S A Θ Ω : Type) [Fintype S] [Fintype A] [Fintype Ω] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ) (ρ : Ω → ℝ) (σ : Ω → RHist S A → S → A → ℝ) (θ : Ω → ℕ → RHist S A → S → A → Θ) (s₀ : S), AdmKNonneg N G adm → RiskCertUpTo N G adm V → (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, IsPolicy (σ ω)) → (∀ ω, SelectorUpTo N adm (θ ω)) → ∑ ω, ρ ω * risk G (θ ω) (σ ω) N s₀ [] ≤ V N s₀
~~~

### 1750. claimFx

Source: proofs/TMCERTF1.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimFx : ∀ (S A : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Game S A) (V : ℕ → S → ℝ) (σ : RHist S A → S → A → ℝ) (s₀ : S), (∀ n, n < N → ∀ s a s', 0 ≤ G.K n s a s') → RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V → IsPolicy σ → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ N s₀ [] ≤ V N s₀
~~~

### 1751. claimFxGap

Source: proofs/TMCERTF1.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimFxGap : risk (fun _ : Unit => gapG true) (fun _ _ _ _ => ()) (fun _ _ _ => 1) 2 () [] = 1/2 ∧ risk (fun _ : Unit => gapG false) (fun _ _ _ _ => ()) (fun _ _ _ => 1) 2 () [] = 1/2 ∧ risk gapG (fun n _ _ _ => decide (n = 1)) (fun _ _ _ => 1) 2 () [] = 3/4
~~~

### 1752. claimObs

Source: proofs/TMCERTF1.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimObs : ∀ (S A O : Type) [Fintype A] (obs : RHist S A → S → O) (π : O → A → ℝ), (∀ o, (∀ a, 0 ≤ π o a) ∧ ∑ a, π o a = 1) → IsPolicy (liftObs obs π)
~~~

### 1753. claimT

Source: proofs/TMCERTF1.lean:97 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimT : ∀ (S A : Type) [Fintype S] [Fintype A] [Nonempty A] (G : Game S A), Lawful G → (∀ N, RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) (Vstar G)) ∧ (∀ N V, RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V → ∀ n, n ≤ N → ∀ s, Vstar G n s ≤ V n s) ∧ (∀ n s, 0 ≤ Vstar G n s ∧ Vstar G n s ≤ 1) ∧ ∀ (N : ℕ) (s₀ : S), ∃ σ, IsPolicy σ ∧ (∀ h s a, σ h s a = 0 ∨ σ h s a = 1) ∧ (∀ h h' s, h.length = h'.length → σ h s = σ h' s) ∧ risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ N s₀ [] = Vstar G N s₀
~~~

### 1754. claimTR

Source: proofs/TMCERTF1.lean:192 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimTR : ∀ (S A Θ : Type) [Fintype S] [Fintype A] [Fintype Θ] [Nonempty A] [Nonempty Θ] (G : Θ → Game S A), (∀ th, Lawful (G th)) → (∀ N, RiskCertUpTo N G (fun _ _ _ _ => True) (Vrob G)) ∧ (∀ N V, RiskCertUpTo N G (fun _ _ _ _ => True) V → ∀ n, n ≤ N → ∀ s, Vrob G n s ≤ V n s) ∧ ∀ (N : ℕ) (s₀ : S), ∃ σ θ, IsPolicy σ ∧ (∀ h s a, σ h s a = 0 ∨ σ h s a = 1) ∧ (∀ h h' s, h.length = h'.length → σ h s = σ h' s) ∧ (∀ n h h' s a, h.length = h'.length → θ n h s a = θ n h' s a) ∧ risk G θ σ N s₀ [] = Vrob G N s₀
~~~

### 1755. claimU

Source: proofs/TMCERTF1.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimU : ∀ (S A Θ : Type) [Fintype S] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (a₀ : A) (rew : Θ → ℕ → S → ℝ) (W : ℕ → S → ℝ) (θ : ℕ → RHist S A → S → Θ), (∀ n, n < N → ∀ s th, adm n s a₀ th → ∀ s', 0 ≤ (G th).K n s a₀ s') → UseCertUpTo N G adm a₀ rew W → (∀ n, n < N → ∀ h s, adm n s a₀ (θ n h s)) → ∀ n, n ≤ N → ∀ s h, W n s ≤ honestER G a₀ rew θ n s h
~~~

### 1756. foldl_add_eq

Source: proofs/TMCERTF1.lean:288 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_add_eq {m : ℕ} (f : Fin m → ℚ) : ∀ (l : List (Fin m)) (acc : ℚ), l.foldl (fun acc i => acc + f i) acc = acc + (l.map f).sum
~~~

### 1757. sumQ_eq

Source: proofs/TMCERTF1.lean:298 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sumQ_eq (m : ℕ) (f : Fin m → ℚ) : sumQ m f = ∑ i, f i
~~~

### 1758. checkRiskQ_spec

Source: proofs/TMCERTF1.lean:301 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkRiskQ_spec {N m k t : ℕ} {cat : Fin t → Fin N → Fin m → Fin k → ℚ} {K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ} {V : Fin (N + 1) → Fin m → ℚ} (hc : checkRiskQ N m k t cat K V = true) : 0 < t ∧ 0 < k ∧ (∀ j s, 0 ≤ V j s) ∧ (∀ th i s a, cat th i s a + ∑ s', K th i s a s' * V i.castSucc s' ≤ V i.succ s)
~~~

### 1759. checkLawfulQ_spec

Source: proofs/TMCERTF1.lean:310 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkLawfulQ_spec {N m k t : ℕ} {cat : Fin t → Fin N → Fin m → Fin k → ℚ} {K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ} (hc : checkLawfulQ N m k t cat K = true) : ∀ th i s a, 0 ≤ cat th i s a ∧ (∀ s', 0 ≤ K th i s a s') ∧ cat th i s a + ∑ s', K th i s a s' ≤ 1
~~~

### 1760. claimQ

Source: proofs/TMCERTF1.lean:319 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimQ : ∀ (N m k t : ℕ) (cat : Fin t → Fin N → Fin m → Fin k → ℚ) (K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ) (V : Fin (N + 1) → Fin m → ℚ), (checkRiskQ N m k t cat K V = true → RiskCertUpTo N (gameOfQ N m k t cat K) (fun _ _ _ _ => True) (valOfQ N m V) ∧ (∀ n s, 0 ≤ valOfQ N m V n s) ∧ 0 < t ∧ 0 < k) ∧ (checkLawfulQ N m k t cat K = true → ∀ th, Lawful (gameOfQ N m k t cat K th))
~~~

### 1761. claimVx

Source: proofs/TMCERTF1.lean:350 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimVx : ∀ (S A ι : Type) [Fintype S] [Fintype ι] (N : ℕ) (Gv : ι → Game S A) (V : ℕ → S → ℝ), RiskCertUpTo N Gv (fun _ _ _ _ => True) V → RiskCertUpTo N (hullGame Gv) (fun _ _ _ lam => Simplex lam) V ∧ ((∀ i n s a s', 0 ≤ (Gv i).K n s a s') → ∀ n s a lam, Simplex lam → ∀ s', 0 ≤ (hullGame Gv lam).K n s a s')
~~~

### 1762. claimAbsV

Source: proofs/TMCERTF1.lean:374 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimAbsV : ∀ (Sc Ac S A Θ : Type) [Fintype Sc] [Fintype Ac] [Fintype S] (N : ℕ) (Gc : Game Sc Ac) (α : Sc → S) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ) (σc : RHist Sc Ac → Sc → Ac → ℝ), (∀ n, n < N → ∀ x ac x', 0 ≤ Gc.K n x ac x') → CoveredV N Gc α G adm V → RiskCertUpTo N G adm V → IsPolicy σc → ∀ n, n ≤ N → ∀ x h, risk (fun _ : Unit => Gc) (fun _ _ _ _ => ()) σc n x h ≤ V n (α x)
~~~

### 1763. claimAbsEq

Source: proofs/TMCERTF1.lean:400 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimAbsEq : ∀ (Sc Ac S A Θ : Type) [Fintype Sc] [Fintype S] [DecidableEq S] (N : ℕ) (Gc : Game Sc Ac) (α : Sc → S) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ), Covered N Gc α G adm → CoveredV N Gc α G adm V
~~~

### 1764. claim

Source: proofs/TMCERTF1.lean:417 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_TMCERTF1.Claim
~~~

### 1765. witness

Source: proofs/TMCERTF1.lean:421 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_TMCERTF1.Witness
~~~

## proofs/TMCERTUSF1.lean

### 1766. foldl_add_eq

Source: proofs/TMCERTUSF1.lean:1 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_add_eq {m : ℕ} (f : Fin m → ℚ) : ∀ (l : List (Fin m)) (acc : ℚ), l.foldl (fun acc i => acc + f i) acc = acc + (l.map f).sum
~~~

### 1767. sumQ_eq

Source: proofs/TMCERTUSF1.lean:8 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sumQ_eq (m : ℕ) (f : Fin m → ℚ) : sumQ m f = ∑ i, f i
~~~

### 1768. checkUseQ_spec

Source: proofs/TMCERTUSF1.lean:11 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkUseQ_spec {N m t : ℕ} {rew : Fin t → Fin N → Fin m → ℚ} {K : Fin t → Fin N → Fin m → Fin m → ℚ} {adm : Fin t → Fin N → Fin m → Bool} {W : Fin (N + 1) → Fin m → ℚ} {s₀ : Fin m} {floor : ℚ} (hc : checkUseQ N m t rew K adm W s₀ floor = true) : 0 < t ∧ floor ≤ W (Fin.last N) s₀ ∧ (∀ s, W 0 s ≤ 0) ∧ (∀ i s, ∃ th, adm th i s = true) ∧ (∀ th i s, adm th i s = true → W i.succ s ≤ rew th i s + ∑ s', K th i s s' * W i.castSucc s')
~~~

### 1769. selector_exists

Source: proofs/TMCERTUSF1.lean:29 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem selector_exists {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ) (K : Fin t → Fin N → Fin m → Fin m → ℚ) (adm : Fin t → Fin N → Fin m → Bool) (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ) (hc : checkUseQ N m t rew K adm W s₀ floor = true) : ∃ θ : ℕ → List (Fin m) → Fin m → Fin t, ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true
~~~

### 1770. checkUseQ_sound

Source: proofs/TMCERTUSF1.lean:45 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkUseQ_sound {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ) (K : Fin t → Fin N → Fin m → Fin m → ℚ) (adm : Fin t → Fin N → Fin m → Bool) (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ) (θ : ℕ → List (Fin m) → Fin m → Fin t) (hc : checkUseQ N m t rew K adm W s₀ floor = true) (hK : ∀ th i s, adm th i s = true → ∀ s', 0 ≤ K th i s s') (hθ : ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true) : (floor : ℝ) ≤ PL_TMCERTUSF1.honestValue rew K θ N s₀ []
~~~

### 1771. claim

Source: proofs/TMCERTUSF1.lean:98 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_TMCERTUSF1.Claim
~~~

### 1772. witness

Source: proofs/TMCERTUSF1.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_TMCERTUSF1.Witness
~~~

## proofs/TMGACF1.lean

### 1773. risk_zero

Source: proofs/TMGACF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_zero' {S A Θ : Type} [Fintype S] [Fintype A] (G : Θ → Game S A) (θ : ℕ → RHist S A → S → A → Θ) (σ : RHist S A → S → A → ℝ) (s : S) (h : RHist S A) : risk G θ σ 0 s h = 0
~~~

### 1774. risk_succ_bool

Source: proofs/TMGACF1.lean:10 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_succ_bool {S : Type} [Fintype S] (G : Game S Bool) (σ : RHist S Bool → S → Bool → ℝ) (n : ℕ) (s : S) (h : RHist S Bool) : risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ (n + 1) s h = σ h s true * (G.cat n s true + ∑ s', G.K n s true s' * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' (h ++ [(s, true)])) + σ h s false * (G.cat n s false + ∑ s', G.K n s false s' * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' (h ++ [(s, false)]))
~~~

### 1775. risk_hist

Source: proofs/TMGACF1.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_hist {S A : Type} [Fintype S] [Fintype A] (G : Game S A) (σ : RHist S A → S → A → ℝ) (hσ : ∀ h s a, σ h s a = σ [] s a) : ∀ n s h, risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s h = risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s []
~~~

### 1776. risk_succ_hf

Source: proofs/TMGACF1.lean:35 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_succ_hf {S : Type} [Fintype S] (G : Game S Bool) (σ : RHist S Bool → S → Bool → ℝ) (hσ : ∀ h s a, σ h s a = σ [] s a) (n : ℕ) (s : S) (h : RHist S Bool) : risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ (n + 1) s h = σ [] s true * (G.cat n s true + ∑ s', G.K n s true s' * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' []) + σ [] s false * (G.cat n s false + ∑ s', G.K n s false s' * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' [])
~~~

### 1777. honestER_hist

Source: proofs/TMGACF1.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honestER_hist {S A : Type} [Fintype S] (G : Game S A) (a₀ : A) (rew : Unit → ℕ → S → ℝ) : ∀ n s h, honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) n s h = honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) n s []
~~~

### 1778. honestER_succ_hf

Source: proofs/TMGACF1.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honestER_succ_hf {S A : Type} [Fintype S] (G : Game S A) (a₀ : A) (rew : Unit → ℕ → S → ℝ) (n : ℕ) (s : S) (h : RHist S A) : honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) (n + 1) s h = rew () n s + ∑ s', G.K n s a₀ s' * honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) n s' []
~~~

### 1779. sup'_bool

Source: proofs/TMGACF1.lean:69 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sup'_bool (g : Bool → ℝ) : (Finset.univ : Finset Bool).sup' Finset.univ_nonempty g = max (g true) (g false)
~~~

### 1780. Vstar_succ_bool

Source: proofs/TMGACF1.lean:79 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Vstar_succ_bool {S : Type} [Fintype S] (G : Game S Bool) (n : ℕ) (s : S) : Vstar G (n + 1) s = max (G.cat n s true + ∑ s', G.K n s true s' * Vstar G n s') (G.cat n s false + ∑ s', G.K n s false s' * Vstar G n s')
~~~

### 1781. constRed_t

Source: proofs/TMGACF1.lean:84 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem constRed_t {S : Type} (β : ℝ) (h : RHist S Bool) (s : S) : constRed β h s true = β
~~~

### 1782. constRed_f

Source: proofs/TMGACF1.lean:85 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem constRed_f {S : Type} (β : ℝ) (h : RHist S Bool) (s : S) : constRed β h s false = 1 - β
~~~

### 1783. gac_cat_true

Source: proofs/TMGACF1.lean:89 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_cat_true (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) : (gac C TA TD FA).cat n c true = (if 0 < c.val then 1 - TD n c.val else 1 - TD n c.val + TA n c.val)
~~~

### 1784. gac_cat_false

Source: proofs/TMGACF1.lean:93 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_cat_false (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) : (gac C TA TD FA).cat n c false = 0
~~~

### 1785. gac_sum_true

Source: proofs/TMGACF1.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_sum_true (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) (F : Fin (C + 1) → ℝ) : ∑ c', (gac C TA TD FA).K n c true c' * F c' = (TD n c.val - TA n c.val) * F c
~~~

### 1786. gac_sum_false_zero

Source: proofs/TMGACF1.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_sum_false_zero (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) (hc : c.val = 0) (F : Fin (C + 1) → ℝ) : ∑ c', (gac C TA TD FA).K n c false c' * F c' = F c
~~~

### 1787. gac_sum_false_succ

Source: proofs/TMGACF1.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_sum_false_succ (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n k : ℕ) (hk : k + 1 < C + 1) (F : Fin (C + 1) → ℝ) : ∑ c', (gac C TA TD FA).K n ⟨k + 1, hk⟩ false c' * F c' = FA n (k + 1) * F ⟨k, by omega⟩ + (1 - FA n (k + 1)) * F ⟨k + 1, hk⟩
~~~

### 1788. conjL

Source: proofs/TMGACF1.lean:130 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjL : ∀ (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ), (∀ n c, 0 ≤ TA n c ∧ TA n c ≤ TD n c ∧ TD n c ≤ 1 ∧ 0 ≤ FA n c ∧ FA n c ≤ 1) → Lawful (gac C TA TD FA)
~~~

### 1789. conjLQ

Source: proofs/TMGACF1.lean:159 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjLQ : ∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ), (∀ m c, 0 ≤ qa m c ∧ qa m c ≤ qd m c ∧ qd m c ≤ 1 ∧ 0 ≤ f (qa m c) ∧ f (qa m c) ≤ f (qd m c) ∧ f (qd m c) ≤ 1) → Lawful (gacQ C f qa qd)
~~~

### 1790. conjZ

Source: proofs/TMGACF1.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjZ : ∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (β : ℝ), f 0 = 0 → (∀ m, qa m 0 = 0) → ∀ (m : ℕ) (c : Fin (C + 1)), 1 - risk (fun _ : Unit => gacQ C f qa qd) (fun _ _ _ _ => ()) (constRed β) m c [] = zGAC f qa qd β m c.val
~~~

### 1791. conjUZ

Source: proofs/TMGACF1.lean:201 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjUZ : ∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (m : ℕ) (c : Fin (C + 1)), honestER (fun _ : Unit => gacQ C f qa qd) false (fun _ n c => usedReward qa qd n c.val) (fun _ _ _ => ()) m c [] = uGAC qa qd m c.val
~~~

### 1792. conjM

Source: proofs/TMGACF1.lean:226 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjM : ∀ (S Ω : Type) [Fintype S] [Fintype Ω] (G : Game S Bool) (ρ : Ω → ℝ) (β : Ω → ℝ) (N : ℕ) (s₀ : S) (U : ℝ), (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, 0 ≤ β ω ∧ β ω ≤ 1) → (∀ b : ℝ, 0 ≤ b → b ≤ 1 → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] ≤ U) → ∑ ω, ρ ω * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed (β ω)) N s₀ [] ≤ U
~~~

### 1793. rowval_bounds

Source: proofs/TMGACF1.lean:239 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rowval_bounds {S : Type} [Fintype S] (G : Game S Bool) (hG : Lawful G) (n : ℕ) (s : S) (a : Bool) (F : S → ℝ) (hF : ∀ s, 0 ≤ F s ∧ F s ≤ 1) : 0 ≤ G.cat n s a + ∑ s', G.K n s a s' * F s' ∧ G.cat n s a + ∑ s', G.K n s a s' * F s' ≤ 1
~~~

### 1794. risk_const_bounds

Source: proofs/TMGACF1.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_const_bounds {S : Type} [Fintype S] (G : Game S Bool) (hG : Lawful G) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : ∀ n s, 0 ≤ risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) n s [] ∧ risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) n s [] ≤ 1
~~~

### 1795. rowval_diff

Source: proofs/TMGACF1.lean:267 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rowval_diff {S : Type} [Fintype S] (G : Game S Bool) (hG : Lawful G) (n : ℕ) (s : S) (a : Bool) (F1 F2 : S → ℝ) (e : ℝ) (he : 0 ≤ e) (hF : ∀ s, |F1 s - F2 s| ≤ e) : |(G.cat n s a + ∑ s', G.K n s a s' * F1 s') - (G.cat n s a + ∑ s', G.K n s a s' * F2 s')| ≤ e
~~~

### 1796. lip_comb

Source: proofs/TMGACF1.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lip_comb (b b' X Y X' Y' e : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hX0 : 0 ≤ X') (hX1 : X' ≤ 1) (hY0 : 0 ≤ Y') (hY1 : Y' ≤ 1) (hXX : |X - X'| ≤ e) (hYY : |Y - Y'| ≤ e) : |b * X + (1 - b) * Y - (b' * X' + (1 - b') * Y')| ≤ e + |b - b'|
~~~

### 1797. conjLip

Source: proofs/TMGACF1.lean:303 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjLip : ∀ (S : Type) [Fintype S] (G : Game S Bool) (N : ℕ) (s₀ : S) (b b' : ℝ), Lawful G → 0 ≤ b → b ≤ 1 → 0 ≤ b' → b' ≤ 1 → |risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] - risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b') N s₀ []| ≤ N * |b - b'|
~~~

### 1798. conjGrid

Source: proofs/TMGACF1.lean:329 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjGrid : ∀ (S : Type) [Fintype S] (G : Game S Bool) (N J : ℕ) (s₀ : S) (U : ℝ), Lawful G → 0 < J → (∀ j : ℕ, j ≤ J → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed ((j : ℝ) / J)) N s₀ [] ≤ U) → ∀ b : ℝ, 0 ≤ b → b ≤ 1 → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] ≤ U + N / (2 * J)
~~~

### 1799. Vstar_zero

Source: proofs/TMGACF1.lean:364 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Vstar_zero' {S A : Type} [Fintype S] [Fintype A] [Nonempty A] (G : Game S A) (s : S) : Vstar G 0 s = 0
~~~

### 1800. conjW

Source: proofs/TMGACF1.lean:368 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjW : ∀ (TA TD FA : ℕ → ℕ → ℝ), (∀ n c, 0 ≤ TA n c ∧ TA n c ≤ TD n c ∧ TD n c ≤ 1 ∧ 0 ≤ FA n c ∧ FA n c ≤ 1) → ∀ (N : ℕ) (c : Fin 1), risk (fun _ : Unit => gac 0 TA TD FA) (fun _ _ _ _ => ()) (constRed 1) N c [] = Vstar (gac 0 TA TD FA) N c
~~~

### 1801. ex_row0t

Source: proofs/TMGACF1.lean:399 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_row0t (n : ℕ) (F : Fin 2 → ℝ) : exG3.cat n 0 true + ∑ s', exG3.K n 0 true s' * F s' = 1/4 + 3/4 * F 0
~~~

### 1802. ex_row0f

Source: proofs/TMGACF1.lean:404 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_row0f (n : ℕ) (F : Fin 2 → ℝ) : exG3.cat n 0 false + ∑ s', exG3.K n 0 false s' * F s' = F 0
~~~

### 1803. ex_row1t

Source: proofs/TMGACF1.lean:408 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_row1t (n : ℕ) (F : Fin 2 → ℝ) : exG3.cat n 1 true + ∑ s', exG3.K n 1 true s' * F s' = 1/4
~~~

### 1804. ex_row1f

Source: proofs/TMGACF1.lean:413 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_row1f (n : ℕ) (F : Fin 2 → ℝ) : exG3.cat n 1 false + ∑ s', exG3.K n 1 false s' * F s' = 1/2 * F 0 + 1/2 * F 1
~~~

### 1805. ex_step0

Source: proofs/TMGACF1.lean:418 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_step0 (σ : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ) (n : ℕ) (h : RHist (Fin 2) Bool) : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ (n + 1) 0 h = σ h 0 true * (1/4 + 3/4 * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 0 (h ++ [(0, true)])) + σ h 0 false * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 0 (h ++ [(0, false)])
~~~

### 1806. ex_step1

Source: proofs/TMGACF1.lean:424 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_step1 (σ : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ) (n : ℕ) (h : RHist (Fin 2) Bool) : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ (n + 1) 1 h = σ h 1 true * (1/4) + σ h 1 false * (1/2 * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 0 (h ++ [(1, false)]) + 1/2 * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 1 (h ++ [(1, false)]))
~~~

### 1807. ex_V0

Source: proofs/TMGACF1.lean:431 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_V0 (n : ℕ) : Vstar exG3 (n + 1) 0 = max (1/4 + 3/4 * Vstar exG3 n 0) (Vstar exG3 n 0)
~~~

### 1808. ex_V1

Source: proofs/TMGACF1.lean:434 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_V1 (n : ℕ) : Vstar exG3 (n + 1) 1 = max (1/4) (1/2 * Vstar exG3 n 0 + 1/2 * Vstar exG3 n 1)
~~~

### 1809. ex_poly

Source: proofs/TMGACF1.lean:438 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_poly (b : ℝ) : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed b) 3 1 [] = 3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3
~~~

### 1810. ex_clocked

Source: proofs/TMGACF1.lean:444 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_clocked : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) clocked3 3 1 [] = 11/32
~~~

### 1811. ex_coin

Source: proofs/TMGACF1.lean:448 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_coin : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) coinRed 3 1 [] = 9/32
~~~

### 1812. ex_Vstar

Source: proofs/TMGACF1.lean:452 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_Vstar : Vstar exG3 3 1 = 11/32
~~~

### 1813. conjT5

Source: proofs/TMGACF1.lean:463 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjT5 : (∀ b : ℝ, 0 ≤ b → b ≤ 1 → risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed b) 3 1 [] = 3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3 ∧ 3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3 ≤ 13/50) ∧ risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed (4/5)) 3 1 [] = 13/50 ∧ IsPolicy clocked3 ∧ IsPolicy coinRed ∧ risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) coinRed 3 1 [] = 9/32 ∧ (13/50 : ℝ) < 9/32 ∧ risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) clocked3 3 1 [] = 11/32 ∧ Vstar exG3 3 1 = 11/32 ∧ (13/50 : ℝ) < 11/32
~~~

### 1814. sound_unit

Source: proofs/TMGACF1.lean:497 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sound_unit {S A : Type} [Fintype S] [Fintype A] (G : Game S A) (N : ℕ) (V : ℕ → S → ℝ) (σ : RHist S A → S → A → ℝ) (hK : ∀ n, n < N → ∀ s a s', 0 ≤ G.K n s a s') (hV : RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V) (hσ : IsPolicy σ) : ∀ n, n ≤ N → ∀ s h, risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s h ≤ V n s
~~~

### 1815. claim

Source: proofs/TMGACF1.lean:516 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_TMGACF1.Claim
~~~

### 1816. witness

Source: proofs/TMGACF1.lean:519 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_TMGACF1.Witness
~~~

## proofs/TMLIPF1.lean

### 1817. oneStep

Source: proofs/TMLIPF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem oneStep : OneStep
~~~

### 1818. transfer

Source: proofs/TMLIPF1.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem transfer : Transfer
~~~

### 1819. gridTransfer

Source: proofs/TMLIPF1.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gridTransfer : GridTransfer
~~~

### 1820. gridRisk

Source: proofs/TMLIPF1.lean:125 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gridRisk : GridRisk
~~~

### 1821. claim

Source: proofs/TMLIPF1.lean:132 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_TMLIPF1.Claim
~~~

### 1822. w_lawfulParam

Source: proofs/TMLIPF1.lean:134 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_lawfulParam : ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), LawfulUpTo 1 (paramGame p)
~~~

### 1823. w_cover

Source: proofs/TMLIPF1.lean:141 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_cover : ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ q ∈ pGrid, |p - q| ≤ 1 / 8
~~~

### 1824. w_lip

Source: proofs/TMLIPF1.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_lip : ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ q ∈ pGrid, RowClose 1 (paramGame q) (paramGame p) (2 * |p - q|)
~~~

### 1825. w_gridCert

Source: proofs/TMLIPF1.lean:157 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_gridCert : ∀ q ∈ pGrid, RiskCertUpTo 1 (fun _ : Unit => paramGame q) (fun _ _ _ _ => True) (gridCert q) ∧ InRange 1 (gridCert q) ∧ ∀ s, gridCert q 1 s ≤ 3 / 8
~~~

### 1826. witness

Source: proofs/TMLIPF1.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_TMLIPF1.Witness
~~~

## proofs/UMADAPTF1.lean

### 1827. adSurv_zero

Source: proofs/UMADAPTF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_zero' {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (h : Hist X Z) : adSurv T M φ keep 0 h = keep h
~~~

### 1828. adSurv_succ

Source: proofs/UMADAPTF1.lean:10 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_succ' {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ) (h : Hist X Z) : adSurv T M φ keep (n + 1) h = ∑ x, T h x * ∑ z, M x z * (φ z * adSurv T M φ keep n (h ++ [(x, z, true)]) + (1 - φ z) * adSurv T M φ keep n (h ++ [(x, z, false)]))
~~~

### 1829. s_aux

Source: proofs/UMADAPTF1.lean:18 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem s_aux {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hk : ∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) : ∀ (n : ℕ) (h : Hist X Z), (∀ e ∈ h, e.2.2 = false) → adSurv T M (fun _ => 0) keep n h = 1
~~~

### 1830. part_s

Source: proofs/UMADAPTF1.lean:39 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_s : ∀ (X Z : Type) [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ), IsKernel M → (∀ h, IsDist (T h)) → (∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) → AcceptsAllFlag T M keep n
~~~

### 1831. surv_bounds

Source: proofs/UMADAPTF1.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_bounds {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hφ : IsRule φ) (hk : ∀ h, 0 ≤ keep h ∧ keep h ≤ 1) : ∀ (n : ℕ) (h : Hist X Z), 0 ≤ adSurv T M φ keep n h ∧ adSurv T M φ keep n h ≤ 1
~~~

### 1832. Qf_zero

Source: proofs/UMADAPTF1.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_zero {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (h : Hist X Z) : Qf T M w 0 h = 0
~~~

### 1833. Qf_succ

Source: proofs/UMADAPTF1.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_succ {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (n : ℕ) (h : Hist X Z) : Qf T M w (n + 1) h = ∑ x, T h x * ∑ z, M x z * (w z + Qf T M w n (h ++ [(x, z, false)]))
~~~

### 1834. Qf_nonneg

Source: proofs/UMADAPTF1.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_nonneg {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hw : ∀ z, 0 ≤ w z) : ∀ (n : ℕ) (h : Hist X Z), 0 ≤ Qf T M w n h
~~~

### 1835. sum2_add

Source: proofs/UMADAPTF1.lean:105 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum2_add {X Z : Type} [Fintype X] [Fintype Z] (a : X → ℝ) (m : X → Z → ℝ) (f g : X → Z → ℝ) (t : ℝ) : ∑ x, a x * ∑ z, m x z * f x z + t * ∑ x, a x * ∑ z, m x z * g x z = ∑ x, a x * ∑ z, m x z * (f x z + t * g x z)
~~~

### 1836. ref_lb

Source: proofs/UMADAPTF1.lean:116 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ref_lb {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ w : Z → ℝ) (t : ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hk : ∀ h, 0 ≤ keep h ∧ keep h ≤ 1) (hφ : IsRule φ) (hw : ∀ z, 0 ≤ w z) (ht : 0 ≤ t) (hφw : ∀ z, φ z ≤ t * w z) : ∀ (n : ℕ) (h : Hist X Z), adSurv T M (fun _ => 0) keep n h - t * Qf T M w n h ≤ adSurv T M φ keep n h
~~~

### 1837. Q_sum_le

Source: proofs/UMADAPTF1.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Q_sum_le {X Z Ω : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (S : Finset Ω) (w : Ω → Z → ℝ) (hw1 : ∀ z, ∑ ω ∈ S, w ω z ≤ 1) : ∀ (n : ℕ) (h : Hist X Z), ∑ ω ∈ S, Qf T M (w ω) n h ≤ n
~~~

### 1838. ind_sum_le

Source: proofs/UMADAPTF1.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ind_sum_le {X Z C : Type} [DecidableEq C] (c : X → C) (g : Z → C) (S : Finset X) (hinj : Set.InjOn c (S : Set X)) (z : Z) : ∑ ω ∈ S, (if g z = c ω then (1 : ℝ) else 0) ≤ 1
~~~

### 1839. classRule_rule

Source: proofs/UMADAPTF1.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classRule_rule {X Z C : Type} [DecidableEq C] (c : X → C) (g : Z → C) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ω : X) : IsRule (classRule c g t ω)
~~~

### 1840. conv_a

Source: proofs/UMADAPTF1.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conv_a {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X) (hM : IsKernel M) (hbad : ∀ x ∈ S, Bad x) (hinj : Set.InjOn c (S : Set X)) (hS : 0 < S.card) (g : Z → C) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ) (hTk : AdTester T keep) (hacc : AcceptsAllFlag T M keep n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (r : ℝ) (b N : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hN : 1 ≤ N) : t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z
~~~

### 1841. opt_arith

Source: proofs/UMADAPTF1.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem opt_arith (k n : ℝ) (hk : 0 < k) (hn : 1 ≤ n) : min (1 / 2) (k / (4 * n)) ≤ min 1 (k / (2 * n)) * max 0 (1 - min 1 (k / (2 * n)) * n / k)
~~~

### 1842. part_a

Source: proofs/UMADAPTF1.lean:288 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_a : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X), Setup Bad M c S → ∃ g : Z → C, (∀ x z, M x z ≠ 0 → g z = c x) ∧ (∀ (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ), AdTester T keep → AcceptsAllFlag T M keep n → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N → t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z
~~~

### 1843. adSurv_det

Source: proofs/UMADAPTF1.lean:321 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_det {X : Type} [Fintype X] [DecidableEq X] (T : Hist X X → X → ℝ) (M : X → X → ℝ) (q : Hist X X → X) (hT : ∀ h x, T h x = if x = q h then 1 else 0) (hM : ∀ x z, M x z = if z = x then 1 else 0) (φ : X → ℝ) (keep : Hist X X → ℝ) (n : ℕ) (h : Hist X X) : adSurv T M φ keep (n + 1) h = φ (q h) * adSurv T M φ keep n (h ++ [(q h, q h, true)]) + (1 - φ (q h)) * adSurv T M φ keep n (h ++ [(q h, q h, false)])
~~~

### 1844. cat_id1

Source: proofs/UMADAPTF1.lean:331 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_id1 {X : Type} [Fintype X] [DecidableEq X] (M : X → X → ℝ) (hM : ∀ x z, M x z = if z = x then 1 else 0) (φ : X → ℝ) (ω : X) : cat (fun _ : X => True) M φ (seedPolicy (Z
~~~

### 1845. det_dist

Source: proofs/UMADAPTF1.lean:336 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem det_dist {X : Type} [Fintype X] [DecidableEq X] (y : X) : IsDist (fun x : X => if x = y then (1 : ℝ) else 0)
~~~

### 1846. keep01

Source: proofs/UMADAPTF1.lean:342 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem keep01 (P : Prop) [Decidable P] : 0 ≤ (if P then (1 : ℝ) else 0) ∧ (if P then (1 : ℝ) else 0) ≤ 1
~~~

### 1847. setup_id

Source: proofs/UMADAPTF1.lean:346 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem setup_id {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] (M : X → X → ℝ) (hM : ∀ x z, M x z = if z = x then 1 else 0) : Setup (fun _ : X => True) M id (univ : Finset X)
~~~

### 1848. misses_allflag

Source: proofs/UMADAPTF1.lean:359 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem misses_allflag {X Z : Type} (h : Hist X Z) (hh : ∀ e ∈ h, e.2.2 = false) : misses h = 0
~~~

### 1849. c1_surv

Source: proofs/UMADAPTF1.lean:366 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c1_surv (t : ℝ) (ω : Bool) : adSurv ctrT idM (classRule id id t ω) ctrKeep 3 [] = if ω then 1 - t ^ 2 else (1 - t) + t * (1 - t) ^ 2
~~~

### 1850. c1_risk

Source: proofs/UMADAPTF1.lean:372 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c1_risk (t : ℝ) : adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool)) (classRule id id t) (seedPolicy (Z
~~~

### 1851. c2_surv

Source: proofs/UMADAPTF1.lean:383 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_surv (t : ℝ) (ω : Fin 3) : adSurv stT idM3 (classRule id id t ω) stKeep 3 [] = if ω = 0 then (1 - t) + t * (1 - t) ^ 2 else if ω = 1 then 1 - t ^ 2 else 1
~~~

### 1852. c2_risk

Source: proofs/UMADAPTF1.lean:389 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_risk (t : ℝ) : adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3))) (classRule id id t) (seedPolicy (Z
~~~

### 1853. c2_bound

Source: proofs/UMADAPTF1.lean:400 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t - t ^ 3 + t ^ 4 / 3 < 1 / 2
~~~

### 1854. w_surv

Source: proofs/UMADAPTF1.lean:404 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_surv (t : ℝ) (ω : Bool) : adSurv wT idM (classRule id id t ω) wKeep 1 [] = if ω then 1 else 1 - t
~~~

### 1855. wbad_surv

Source: proofs/UMADAPTF1.lean:409 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wbad_surv (t : ℝ) (ω : Bool) : adSurv wT idM (classRule id id t ω) wKeepBad 1 [] = if ω then 0 else t
~~~

### 1856. part_c1

Source: proofs/UMADAPTF1.lean:414 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c1 : (Setup (fun _ : Bool => True) idM id (univ : Finset Bool) ∧ AdTester ctrT ctrKeep ∧ AcceptsAllFlag ctrT idM ctrKeep 3 ∧ (∀ h : Hist Bool Bool, misses h ≤ 1 → ctrKeep h = 1) ∧ adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool)) (classRule id id (3/4)) (seedPolicy (Z
~~~

### 1857. part_c2

Source: proofs/UMADAPTF1.lean:439 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c2 : (Setup (fun _ : Fin 3 => True) idM3 id (univ : Finset (Fin 3)) ∧ AdTester stT stKeep ∧ AcceptsAllFlag stT idM3 stKeep 3 ∧ (∀ h : Hist (Fin 3) (Fin 3), misses h ≤ 1 → stKeep h = 1) ∧ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3))) (classRule id id t) (seedPolicy (Z
~~~

### 1858. claim

Source: proofs/UMADAPTF1.lean:460 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMADAPTF1.Claim
~~~

### 1859. witness

Source: proofs/UMADAPTF1.lean:463 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMADAPTF1.Witness
~~~

## proofs/UMADAPTF2.lean

### 1860. adSurv_zero

Source: proofs/UMADAPTF2.lean:6 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_zero' {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (h : Hist X Z) : adSurv T M φ keep 0 h = keep h
~~~

### 1861. adSurv_succ

Source: proofs/UMADAPTF2.lean:11 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_succ' {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ) (h : Hist X Z) : adSurv T M φ keep (n + 1) h = ∑ x, T h x * ∑ z, M x z * (φ z * adSurv T M φ keep n (h ++ [(x, z, true)]) + (1 - φ z) * adSurv T M φ keep n (h ++ [(x, z, false)]))
~~~

### 1862. s_aux

Source: proofs/UMADAPTF2.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem s_aux {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hk : ∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) : ∀ (n : ℕ) (h : Hist X Z), (∀ e ∈ h, e.2.2 = false) → adSurv T M (fun _ => 0) keep n h = 1
~~~

### 1863. part_s

Source: proofs/UMADAPTF2.lean:40 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_s : ∀ (X Z : Type) [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ), IsKernel M → (∀ h, IsDist (T h)) → (∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) → AcceptsAllFlag T M keep n
~~~

### 1864. surv_bounds

Source: proofs/UMADAPTF2.lean:49 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_bounds {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hφ : IsRule φ) (hk : ∀ h, 0 ≤ keep h ∧ keep h ≤ 1) : ∀ (n : ℕ) (h : Hist X Z), 0 ≤ adSurv T M φ keep n h ∧ adSurv T M φ keep n h ≤ 1
~~~

### 1865. Qf_zero

Source: proofs/UMADAPTF2.lean:84 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_zero {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (h : Hist X Z) : Qf T M w 0 h = 0
~~~

### 1866. Qf_succ

Source: proofs/UMADAPTF2.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_succ {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (n : ℕ) (h : Hist X Z) : Qf T M w (n + 1) h = ∑ x, T h x * ∑ z, M x z * (w z + Qf T M w n (h ++ [(x, z, false)]))
~~~

### 1867. Qf_nonneg

Source: proofs/UMADAPTF2.lean:93 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_nonneg {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hw : ∀ z, 0 ≤ w z) : ∀ (n : ℕ) (h : Hist X Z), 0 ≤ Qf T M w n h
~~~

### 1868. sum2_add

Source: proofs/UMADAPTF2.lean:106 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum2_add {X Z : Type} [Fintype X] [Fintype Z] (a : X → ℝ) (m : X → Z → ℝ) (f g : X → Z → ℝ) (t : ℝ) : ∑ x, a x * ∑ z, m x z * f x z + t * ∑ x, a x * ∑ z, m x z * g x z = ∑ x, a x * ∑ z, m x z * (f x z + t * g x z)
~~~

### 1869. ref_lb

Source: proofs/UMADAPTF2.lean:117 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ref_lb {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ w : Z → ℝ) (t : ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hk : ∀ h, 0 ≤ keep h ∧ keep h ≤ 1) (hφ : IsRule φ) (hw : ∀ z, 0 ≤ w z) (ht : 0 ≤ t) (hφw : ∀ z, φ z ≤ t * w z) : ∀ (n : ℕ) (h : Hist X Z), adSurv T M (fun _ => 0) keep n h - t * Qf T M w n h ≤ adSurv T M φ keep n h
~~~

### 1870. Q_sum_le

Source: proofs/UMADAPTF2.lean:147 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Q_sum_le {X Z Ω : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (S : Finset Ω) (w : Ω → Z → ℝ) (hw1 : ∀ z, ∑ ω ∈ S, w ω z ≤ 1) : ∀ (n : ℕ) (h : Hist X Z), ∑ ω ∈ S, Qf T M (w ω) n h ≤ n
~~~

### 1871. ind_sum_le

Source: proofs/UMADAPTF2.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ind_sum_le {X Z C : Type} [DecidableEq C] (c : X → C) (g : Z → C) (S : Finset X) (hinj : Set.InjOn c (S : Set X)) (z : Z) : ∑ ω ∈ S, (if g z = c ω then (1 : ℝ) else 0) ≤ 1
~~~

### 1872. classRule_rule

Source: proofs/UMADAPTF2.lean:184 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classRule_rule {X Z C : Type} [DecidableEq C] (c : X → C) (g : Z → C) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ω : X) : IsRule (classRule c g t ω)
~~~

### 1873. conv_a

Source: proofs/UMADAPTF2.lean:188 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conv_a {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X) (hM : IsKernel M) (hbad : ∀ x ∈ S, Bad x) (hinj : Set.InjOn c (S : Set X)) (hS : 0 < S.card) (g : Z → C) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ) (hTk : AdTester T keep) (hacc : AcceptsAllFlag T M keep n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (r : ℝ) (b N : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hN : 1 ≤ N) : t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z
~~~

### 1874. opt_arith

Source: proofs/UMADAPTF2.lean:270 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem opt_arith (k n : ℝ) (hk : 0 < k) (hn : 1 ≤ n) : min (1 / 2) (k / (4 * n)) ≤ min 1 (k / (2 * n)) * max 0 (1 - min 1 (k / (2 * n)) * n / k)
~~~

### 1875. part_a

Source: proofs/UMADAPTF2.lean:289 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_a : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X), Setup Bad M c S → ∃ g : Z → C, (∀ x z, M x z ≠ 0 → g z = c x) ∧ (∀ (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ), AdTester T keep → AcceptsAllFlag T M keep n → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N → t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z
~~~

### 1876. adSurv_det

Source: proofs/UMADAPTF2.lean:322 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_det {X : Type} [Fintype X] [DecidableEq X] (T : Hist X X → X → ℝ) (M : X → X → ℝ) (q : Hist X X → X) (hT : ∀ h x, T h x = if x = q h then 1 else 0) (hM : ∀ x z, M x z = if z = x then 1 else 0) (φ : X → ℝ) (keep : Hist X X → ℝ) (n : ℕ) (h : Hist X X) : adSurv T M φ keep (n + 1) h = φ (q h) * adSurv T M φ keep n (h ++ [(q h, q h, true)]) + (1 - φ (q h)) * adSurv T M φ keep n (h ++ [(q h, q h, false)])
~~~

### 1877. cat_id1

Source: proofs/UMADAPTF2.lean:332 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_id1 {X : Type} [Fintype X] [DecidableEq X] (M : X → X → ℝ) (hM : ∀ x z, M x z = if z = x then 1 else 0) (φ : X → ℝ) (ω : X) : cat (fun _ : X => True) M φ (seedPolicy (Z
~~~

### 1878. det_dist

Source: proofs/UMADAPTF2.lean:337 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem det_dist {X : Type} [Fintype X] [DecidableEq X] (y : X) : IsDist (fun x : X => if x = y then (1 : ℝ) else 0)
~~~

### 1879. keep01

Source: proofs/UMADAPTF2.lean:343 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem keep01 (P : Prop) [Decidable P] : 0 ≤ (if P then (1 : ℝ) else 0) ∧ (if P then (1 : ℝ) else 0) ≤ 1
~~~

### 1880. setup_id

Source: proofs/UMADAPTF2.lean:347 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem setup_id {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] (M : X → X → ℝ) (hM : ∀ x z, M x z = if z = x then 1 else 0) : Setup (fun _ : X => True) M id (univ : Finset X)
~~~

### 1881. misses_allflag

Source: proofs/UMADAPTF2.lean:360 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem misses_allflag {X Z : Type} (h : Hist X Z) (hh : ∀ e ∈ h, e.2.2 = false) : misses h = 0
~~~

### 1882. c1_surv

Source: proofs/UMADAPTF2.lean:367 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c1_surv (t : ℝ) (ω : Bool) : adSurv ctrT idM (PL_UMLOWERF1.classRule id id t ω) ctrKeep 3 [] = if ω then 1 - t ^ 2 else (1 - t) + t * (1 - t) ^ 2
~~~

### 1883. c1_risk

Source: proofs/UMADAPTF2.lean:373 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c1_risk (t : ℝ) : adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool)) (classRule id id t) (seedPolicy (Z
~~~

### 1884. c2_surv

Source: proofs/UMADAPTF2.lean:384 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_surv (t : ℝ) (ω : Fin 3) : adSurv stT idM3 (PL_UMLOWERF1.classRule id id t ω) stKeep 3 [] = if ω = 0 then (1 - t) + t * (1 - t) ^ 2 else if ω = 1 then 1 - t ^ 2 else 1
~~~

### 1885. c2_risk

Source: proofs/UMADAPTF2.lean:390 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_risk (t : ℝ) : adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3))) (classRule id id t) (seedPolicy (Z
~~~

### 1886. c2_bound

Source: proofs/UMADAPTF2.lean:401 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t - t ^ 3 + t ^ 4 / 3 < 1 / 2
~~~

### 1887. w_surv

Source: proofs/UMADAPTF2.lean:405 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_surv (t : ℝ) (ω : Bool) : adSurv wT idM (PL_UMLOWERF1.classRule id id t ω) wKeep 1 [] = if ω then 1 else 1 - t
~~~

### 1888. wbad_surv

Source: proofs/UMADAPTF2.lean:410 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wbad_surv (t : ℝ) (ω : Bool) : adSurv wT idM (PL_UMLOWERF1.classRule id id t ω) wKeepBad 1 [] = if ω then 0 else t
~~~

### 1889. part_c1

Source: proofs/UMADAPTF2.lean:415 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c1 : (Setup (fun _ : Bool => True) idM id (univ : Finset Bool) ∧ AdTester ctrT ctrKeep ∧ AcceptsAllFlag ctrT idM ctrKeep 3 ∧ (∀ h : Hist Bool Bool, misses h ≤ 1 → ctrKeep h = 1) ∧ adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool)) (classRule id id (3/4)) (seedPolicy (Z
~~~

### 1890. part_c2

Source: proofs/UMADAPTF2.lean:440 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c2 : (Setup (fun _ : Fin 3 => True) idM3 id (univ : Finset (Fin 3)) ∧ AdTester stT stKeep ∧ AcceptsAllFlag stT idM3 stKeep 3 ∧ (∀ h : Hist (Fin 3) (Fin 3), misses h ≤ 1 → stKeep h = 1) ∧ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3))) (classRule id id t) (seedPolicy (Z
~~~

### 1891. claim1

Source: proofs/UMADAPTF2.lean:461 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim1 : PL_UMADAPTF1.Claim
~~~

### 1892. witness1

Source: proofs/UMADAPTF2.lean:464 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness1 : PL_UMADAPTF1.Witness
~~~

### 1893. slope_mono

Source: proofs/UMADAPTF2.lean:494 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
private lemma slope_mono (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : ∀ {n k : ℕ}, n ≤ k → slope b n ≤ slope b k
~~~

### 1894. tangent_step

Source: proofs/UMADAPTF2.lean:506 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
private lemma tangent_step (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (m q : ℕ) (hmq : m ≤ q) : b ^ (q + 1) + ((m : ℝ) - ((q + 1 : ℕ) : ℝ)) * slope b (q + 1) ≤ b ^ q + ((m : ℝ) - (q : ℝ)) * slope b q
~~~

### 1895. balanced_bound

Source: proofs/UMADAPTF2.lean:522 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem balanced_bound (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (m q : ℕ) : b ^ m ≥ b ^ q + ((m : ℝ) - (q : ℝ)) * (b ^ (q + 1) - b ^ q)
~~~

### 1896. aggregate_balanced_budget

Source: proofs/UMADAPTF2.lean:550 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem aggregate_balanced_budget (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k q a : ℕ) (_hk : 0 < k) (ha : a < k) (counts : Fin k → ℕ) (hcounts : ∑ i : Fin k, counts i ≤ k * q + a) : ∑ i : Fin k, b ^ (counts i) ≥ ((k - a : ℕ) : ℝ) * b ^ q + (a : ℝ) * b ^ (q + 1)
~~~

### 1897. aggregate_balanced_exact

Source: proofs/UMADAPTF2.lean:591 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem aggregate_balanced_exact (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k n : ℕ) (hk : 0 < k) (counts : Fin k → ℕ) (hcounts : ∑ i : Fin k, counts i = n) : ∑ i : Fin k, b ^ (counts i) ≥ ((k - n % k : ℕ) : ℝ) * b ^ (n / k) + ((n % k : ℕ) : ℝ) * b ^ (n / k + 1)
~~~

### 1898. classCount_append_flag

Source: proofs/UMADAPTF2.lean:626 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classCount_append_flag {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (h : SharpHist X Z) (x : X) (z : Z) (ω : Fin k) : classCount g (h ++ [(x, z, false)]) ω = classCount g h ω + (if g z = some ω then 1 else 0)
~~~

### 1899. flagFactor

Source: proofs/UMADAPTF2.lean:632 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem flagFactor {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (b : ℝ) (ω : Fin k) (z : Z) : 1 - passProb g (1-b) ω z = if g z = some ω then b else 1
~~~

### 1900. passProb_bounds

Source: proofs/UMADAPTF2.lean:646 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem passProb_bounds {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ω : Fin k) (z : Z) : 0 ≤ passProb g t ω z ∧ passProb g t ω z ≤ 1
~~~

### 1901. fullSurv_nonneg

Source: proofs/UMADAPTF2.lean:653 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fullSurv_nonneg {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) : ∀ n h ω, 0 ≤ fullSurv T M g t keep ω n h
~~~

### 1902. fullSurv_ge_flagOnly

Source: proofs/UMADAPTF2.lean:684 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fullSurv_ge_flagOnly {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) : ∀ n h ω, flagOnly T M g t keep ω n h ≤ fullSurv T M g t keep ω n h
~~~

### 1903. refSurv_eq_fullSurv_zero

Source: proofs/UMADAPTF2.lean:730 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refSurv_eq_fullSurv_zero {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (keep : SharpHist X Z → ℝ) : ∀ n h ω, refSurv T M keep n h = fullSurv T M g 0 keep ω n h
~~~

### 1904. classPower_append_flag

Source: proofs/UMADAPTF2.lean:756 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classPower_append_flag {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (b : ℝ) (h : SharpHist X Z) (x : X) (z : Z) (ω : Fin k) : b ^ classCount g h ω * (if g z = some ω then b else 1) = b ^ classCount g (h ++ [(x,z,false)]) ω
~~~

### 1905. weightedFactor_append

Source: proofs/UMADAPTF2.lean:763 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
private theorem weightedFactor_append {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (b : ℝ) (h : SharpHist X Z) (x : X) (z : Z) (ω : Fin k) (f : ℝ) : b ^ classCount g (h ++ [(x,z,false)]) ω * f = b ^ classCount g h ω * ((1 - passProb g (1-b) ω z) * f)
~~~

### 1906. weighted_double_sum

Source: proofs/UMADAPTF2.lean:779 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem weighted_double_sum {α β : Type} [Fintype α] [Fintype β] (a : α → ℝ) (c : β → ℝ) (f : α → β → ℝ) : (∑ i, a i * ∑ j, c j * f i j) = ∑ j, c j * ∑ i, a i * f i j
~~~

### 1907. weightedFlag_succ

Source: proofs/UMADAPTF2.lean:799 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem weightedFlag_succ {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (b : ℝ) (keep : SharpHist X Z → ℝ) (n : ℕ) (h : SharpHist X Z) : weightedFlag T M g b keep (n+1) h = ∑ x, T h x * ∑ z, M x z * weightedFlag T M g b keep n (h ++ [(x,z,false)])
~~~

### 1908. count_sum_le

Source: proofs/UMADAPTF2.lean:886 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem count_sum_le {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (h : SharpHist X Z) : (∑ ω : Fin k, classCount g h ω) ≤ h.length
~~~

### 1909. weightedFlag_lower

Source: proofs/UMADAPTF2.lean:928 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem weightedFlag_lower {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (N : ℕ) : ∀ n h, h.length + n = N → balancedTarget k N b * refSurv T M keep n h ≤ weightedFlag T M g b keep n h
~~~

### 1910. sharp_survival

Source: proofs/UMADAPTF2.lean:992 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_survival {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : refSurv T M keep n [] = 1) : balancedTarget k n (1-t) ≤ ∑ ω : Fin k, fullSurv T M g t keep ω n []
~~~

### 1911. sharp_uniform_cat

Source: proofs/UMADAPTF2.lean:1022 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_uniform_cat {k : ℕ} (hkpos : 0 < k) (t : ℝ) (ht0 : 0 ≤ t) (n : ℕ) (surv cat : Fin k → ℝ) (hsurv : ∀ i, 0 ≤ surv i) (hcat : ∀ i, t ≤ cat i) (hsum : balancedTarget k n (1-t) ≤ ∑ i : Fin k, surv i) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ (1 / (k : ℝ)) * ∑ i : Fin k, surv i * cat i
~~~

### 1912. seedDecoder_eq_some_iff

Source: proofs/UMADAPTF2.lean:1058 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seedDecoder_eq_some_iff {X C Z : Type} [DecidableEq C] {k : ℕ} (seed : Fin k → X) (c : X → C) (g : Z → C) (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (z : Z) (i : Fin k) : seedDecoder seed c g z = some i ↔ g z = c (seed i)
~~~

### 1913. seedDecoder_pass_eq

Source: proofs/UMADAPTF2.lean:1088 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seedDecoder_pass_eq {X C Z : Type} [DecidableEq C] {k : ℕ} (seed : Fin k → X) (c : X → C) (g : Z → C) (t : ℝ) (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (i : Fin k) (z : Z) : passProb (seedDecoder seed c g) t i z = classPass c g t (seed i) z
~~~

### 1914. refSurv_eq_passSurv_zero

Source: proofs/UMADAPTF2.lean:1109 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refSurv_eq_passSurv_zero {X : Type} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (keep : SharpHist X Z → ℝ) : ∀ n h, refSurv T M keep n h = passSurv T M (fun _ => 0) keep n h
~~~

### 1915. fullSurv_eq_passSurv_seed

Source: proofs/UMADAPTF2.lean:1126 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fullSurv_eq_passSurv_seed {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (seed : Fin k → X) (c : X → C) (g : Z → C) (t : ℝ) (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (keep : SharpHist X Z → ℝ) (i : Fin k) : ∀ n h, fullSurv T M (seedDecoder seed c g) t keep i n h = passSurv T M (classPass c g t (seed i)) keep n h
~~~

### 1916. sharp_seedset_survival

Source: proofs/UMADAPTF2.lean:1148 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_seedset_survival {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : refSurv T M keep n [] = 1) : balancedTarget k n (1-t) ≤ ∑ i : Fin k, passSurv T M (classPass c g t ((e i).val)) keep n []
~~~

### 1917. sharp_seedset_catRisk

Source: proofs/UMADAPTF2.lean:1177 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_seedset_catRisk {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : refSurv T M keep n [] = 1) (cat : Fin k → ℝ) (hcat : ∀ i, t ≤ cat i) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ (1 / (k : ℝ)) * ∑ i : Fin k, passSurv T M (classPass c g t ((e i).val)) keep n [] * cat i
~~~

### 1918. adSurv_reference_eq

Source: proofs/UMADAPTF2.lean:1234 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_reference_eq {X Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (keep : SharpHist X Z → ℝ) : ∀ n h, refSurv T M keep n h = adSurv T M (fun _ => 0) keep n h
~~~

### 1919. accepts_all_flag_reference

Source: proofs/UMADAPTF2.lean:1240 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem accepts_all_flag_reference {X Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (keep : SharpHist X Z → ℝ) (n : ℕ) (hacc : adSurv T M (fun _ => 0) keep n [] = 1) : refSurv T M keep n [] = 1
~~~

### 1920. sharp_uniform_seed_risk

Source: proofs/UMADAPTF2.lean:1250 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_uniform_seed_risk {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : adSurv T M (fun _ => 0) keep n [] = 1) (cat : Fin k → ℝ) (hcat : ∀ i, t ≤ cat i) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ (1 / (k : ℝ)) * ∑ i : Fin k, adSurv T M (classRule c g t ((e i).val)) keep n [] * cat i
~~~

### 1921. protocolCatModel_eq

Source: proofs/UMADAPTF2.lean:1281 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem protocolCatModel_eq {X : Type} [Fintype X] [DecidableEq X] (S : Finset X) (surv cat : X → ℝ) : protocolCatModel S surv cat = (1 / (S.card : ℝ)) * ∑ x : {x // x ∈ S}, surv x.val * cat x.val
~~~

### 1922. sum_finEquiv_eq_sum_seed

Source: proofs/UMADAPTF2.lean:1301 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_finEquiv_eq_sum_seed {X : Type} {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (f : {x // x ∈ S} → ℝ) : (∑ i : Fin k, f (e i)) = ∑ x : {x // x ∈ S}, f x
~~~

### 1923. sharp_uniform_adProtocolCatModel

Source: proofs/UMADAPTF2.lean:1305 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_uniform_adProtocolCatModel {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] [DecidableEq X] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : adSurv T M (fun _ => 0) keep n [] = 1) (cat : X → ℝ) (hcat : ∀ x ∈ S, t ≤ cat x) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ protocolCatModel S (fun x => adSurv T M (classRule c g t x) keep n []) cat
~~~

### 1924. sharp_surv_eq_campaign

Source: proofs/UMADAPTF2.lean:1357 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_surv_eq_campaign {X Z : Type} [Fintype X] [Fintype Z] (T : _root_.PL_UMPROTF1.Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : _root_.PL_UMPROTF1.Hist X Z → ℝ) : ∀ n h, SharpUM.adSurv T M φ keep n h = _root_.PL_UMADAPTF1.adSurv T M φ keep n h
~~~

### 1925. conv_a_sharp

Source: proofs/UMADAPTF2.lean:1379 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conv_a_sharp {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X) (hM : IsKernel M) (hbad : ∀ x ∈ S, Bad x) (hinj : Set.InjOn c (S : Set X)) (hS : 0 < S.card) (g : Z → C) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ) (hTk : AdTester T keep) (hacc : AcceptsAllFlag T M keep n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (r : ℝ) (b N : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hN : 1 ≤ N) : (t / (S.card : ℝ)) * balancedTarget S.card n (1-t) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (_root_.PL_UMLOWERF1.classRule c g t) (seedPolicy (Z
~~~

### 1926. sharpTarget_eq

Source: proofs/UMADAPTF2.lean:1439 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharpTarget_eq (k n : ℕ) (b : ℝ) : PL_UMADAPTF2.sharpTarget k n b = balancedTarget k n b
~~~

### 1927. claim

Source: proofs/UMADAPTF2.lean:1442 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMADAPTF2.Claim
~~~

### 1928. rr_surv

Source: proofs/UMADAPTF2.lean:1451 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rr_surv (t : ℝ) (ω : Bool) : PL_UMADAPTF1.adSurv rrT idM (PL_UMLOWERF1.classRule id id t ω) rrKeep 3 [] = if ω then 1 - t else (1 - t) ^ 2
~~~

### 1929. witness

Source: proofs/UMADAPTF2.lean:1456 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMADAPTF2.Witness
~~~

## proofs/UMCERTF1.lean

### 1930. capB_mono

Source: proofs/UMCERTF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB_mono (r : ℝ) (b : ℕ) (hr : 0 ≤ r) {a a' : ℝ} (h : a ≤ a') : capB r b a ≤ capB r b a'
~~~

### 1931. capB_nonneg

Source: proofs/UMCERTF1.lean:12 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB_nonneg (r : ℝ) (b : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ capB r b a
~~~

### 1932. capB_le

Source: proofs/UMCERTF1.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB_le (r : ℝ) (b : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {a : ℝ} (ha : a ≤ 1) : capB r b a ≤ 1 - r + r * a
~~~

### 1933. capB_one

Source: proofs/UMCERTF1.lean:26 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB_one (r : ℝ) (b : ℕ) : capB r b 1 = 1
~~~

### 1934. E_const

Source: proofs/UMCERTF1.lean:32 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_const {Z : Type} [Fintype Z] (P : Z → ℝ) (hP : ∑ z, P z = 1) (t : ℝ) : E P (fun _ => t) = t
~~~

### 1935. E_push

Source: proofs/UMCERTF1.lean:37 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_push {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (P : X → ℝ) (ψ : Z → ℝ) : E (push M P) ψ = ∑ x, P x * E (M x) ψ
~~~

### 1936. unit_dist

Source: proofs/UMCERTF1.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unit_dist : IsDist (fun _ : Unit => (1 : ℝ))
~~~

### 1937. point_dist

Source: proofs/UMCERTF1.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem point_dist {X : Type} [Fintype X] [DecidableEq X] (x : X) : IsDist (fun x' : X => if x' = x then (1 : ℝ) else 0)
~~~

### 1938. cat_empty

Source: proofs/UMCERTF1.lean:60 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_empty {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (b : ℕ) (hB : ∀ x, ¬ Bad x) : ∀ n u h, cat Bad M φ π r b n u h = 0
~~~

### 1939. cat_oneshot

Source: proofs/UMCERTF1.lean:71 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_oneshot {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] [DecidableEq X] (M : X → Z → ℝ) (ψ : Z → ℝ) (r : ℝ) (b N : ℕ) (x : X) (hM : IsKernel M) (hx : Bad x) (hN : 1 ≤ N) : cat Bad M ψ (fun _ x' => if x' = x then 1 else 0) r b N 0 [] = capB r b (E (M x) ψ)
~~~

### 1940. exists_worst

Source: proofs/UMCERTF1.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exists_worst {X : Type} [Fintype X] (Bad : X → Prop) [DecidablePred Bad] (f : X → ℝ) (hex : ∃ x, Bad x) : ∃ x0, Bad x0 ∧ ∀ x, Bad x → f x ≤ f x0
~~~

### 1941. oneshot_value

Source: proofs/UMCERTF1.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem oneshot_value {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] [DecidableEq X] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (ψ : Z → ℝ) (x : X) (hM : IsKernel M) (hP : IsDist PH) (hx : Bad x) (hN : 1 ≤ N) : protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (fun _ => ψ) (fun _ _ x' => if x' = x then 1 else 0) = survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ)
~~~

### 1942. strat_oneshot_value

Source: proofs/UMCERTF1.lean:108 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem strat_oneshot_value {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (g : Z → C) (Es : Finset C) (m sc b N : ℕ) (r t : ℝ) (x : X) (hK : IsKernel K) (hdec : ∀ e z, K e z ≠ 0 → g z = e) (hx : Bad x) (hcx : c x ∈ Es) (hN : 1 ≤ N) : stratProtocolCat Bad K c Es m sc r b N (fun _ : Unit => 1) (fun _ z => if g z = c x then t else 0) (fun _ _ x' => if x' = x then 1 else 0) = binCDF m sc t * capB r b t
~~~

### 1943. seed_le

Source: proofs/UMCERTF1.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seed_le {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (hM : IsKernel M) (hP : IsDist PH) (hφ : IsRule φ) (hπ : ∀ h, IsDist (π h)) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hU : 0 ≤ U) (hyp : ∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) ≤ U) : surv (push M PH) φ κ nh 0 * cat Bad M φ π r b N 0 [] ≤ U
~~~

### 1944. reduce_le

Source: proofs/UMCERTF1.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reduce_le {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) (hM : IsKernel M) (hP : IsDist PH) (hρ : IsDist ρ) (hφ : ∀ ω, IsRule (φ ω)) (hπ : ∀ ω h, IsDist (π ω h)) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hU : 0 ≤ U) (hyp : ∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) ≤ U) : protocolCat Bad M PH κ nh r b N ρ φ π ≤ U
~~~

### 1945. survH_aux

Source: proofs/UMCERTF1.lean:167 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survH_aux (κ : ℕ → ℝ) (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ 1) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) : ∀ n j, (1 - κ j) * survH h κ n (j + 1) ≤ survH h κ n j
~~~

### 1946. survH_anti

Source: proofs/UMCERTF1.lean:190 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survH_anti (κ : ℕ → ℝ) (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ 1) : ∀ n j (s t : ℝ), 0 ≤ s → s ≤ t → t ≤ 1 → survH t κ n j ≤ survH s κ n j
~~~

### 1947. GridOK_cons2

Source: proofs/UMCERTF1.lean:218 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem GridOK_cons2 (S F : ℝ → ℝ) (U s t : ℝ) (rest : List ℝ) : GridOK S F U (s :: t :: rest) ↔ s ≤ t ∧ S s * F t ≤ U ∧ GridOK S F U (t :: rest)
~~~

### 1948. GridOK_single

Source: proofs/UMCERTF1.lean:221 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem GridOK_single (S F : ℝ → ℝ) (U a : ℝ) : GridOK S F U [a] ↔ True
~~~

### 1949. grid_aux

Source: proofs/UMCERTF1.lean:223 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem grid_aux (S F : ℝ → ℝ) (U : ℝ) (hS : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s) (hF : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t) (h0 : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t) : ∀ (rest : List ℝ) (a b : ℝ), GridOK S F U (a :: b :: rest) → (a :: b :: rest).getLast? = some 1 → 0 ≤ a → a ≤ 1 ∧ ∀ t, a ≤ t → t ≤ 1 → S t * F t ≤ U
~~~

### 1950. grid_cert

Source: proofs/UMCERTF1.lean:263 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem grid_cert (S F : ℝ → ℝ) (U : ℝ) (ts : List ℝ) (hS : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s) (hF : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t) (h0 : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t) (hG : GridCert S F U ts) : ∀ t, 0 ≤ t → t ≤ 1 → S t * F t ≤ U
~~~

### 1951. bin_anti

Source: proofs/UMCERTF1.lean:282 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bin_anti (m sc : ℕ) : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → binCDF m sc t ≤ binCDF m sc s
~~~

### 1952. bin_nonneg

Source: proofs/UMCERTF1.lean:287 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bin_nonneg (m sc : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ binCDF m sc t
~~~

### 1953. dom_content

Source: proofs/UMCERTF1.lean:293 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dom_content {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] (K : C → Z → ℝ) (c : X → C) (PH : X → ℝ) (p : ℝ) (hK : IsKernel K) (hP : IsDist PH) (hp : 0 < p) (x : X) (hcov : p ≤ contentLaw c PH (c x)) (z : Z) : (fun x => K (c x)) x z ≤ (1 / p) * push (fun x => K (c x)) PH z
~~~

### 1954. claim_R

Source: proofs/UMCERTF1.lean:315 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_R : ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ), IsKernel M → IsDist PH → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N → 0 ≤ U → ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ↔ (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) ≤ U))
~~~

### 1955. claim_C

Source: proofs/UMCERTF1.lean:333 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_C : ∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (env : ℝ → ℝ) (U : ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 0 ≤ U → (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ env (E (push M PH) ψ)) → (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b (min 1 (env t)) ≤ U) → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U
~~~

### 1956. claim_E1

Source: proofs/UMCERTF1.lean:355 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_E1 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (L : ℝ) (x : X), (∀ z, M x z ≤ L * push M PH z) → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ L * E (push M PH) ψ
~~~

### 1957. claim_E2

Source: proofs/UMCERTF1.lean:361 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_E2 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (η δ : ℝ) (x : X), hs η (M x) (push M PH) ≤ δ → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ Real.exp η * E (push M PH) ψ + δ
~~~

### 1958. claim_G0

Source: proofs/UMCERTF1.lean:368 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_G0 : ∀ (κ : ℕ → ℝ) (n j : ℕ) (s t : ℝ), (∀ i, 0 ≤ κ i ∧ κ i ≤ 1) → 0 ≤ s → s ≤ t → t ≤ 1 → survH t κ n j ≤ survH s κ n j
~~~

### 1959. claim_G

Source: proofs/UMCERTF1.lean:372 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_G : ∀ (S F : ℝ → ℝ) (U : ℝ) (ts : List ℝ), (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s) → (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t) → (∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t) → GridCert S F U ts → ∀ t, 0 ≤ t → t ≤ 1 → S t * F t ≤ U
~~~

### 1960. claim_CG

Source: proofs/UMCERTF1.lean:379 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_CG : ∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (env : ℝ → ℝ) (U : ℝ) (ts : List ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ env (E (push M PH) ψ)) → (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → env s ≤ env t) → (∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ env t) → GridCert (fun t => survH t κ nh 0) (fun t => capB r b (min 1 (env t))) U ts → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U
~~~

### 1961. claim_S1

Source: proofs/UMCERTF1.lean:404 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_S1 : ∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 → (∀ x, Bad x → c x ∈ Es) → (∀ t : ℝ, 0 ≤ t → t ≤ 1 → binCDF m sc t * capB r b t ≤ U) → stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U
~~~

### 1962. claim_SG

Source: proofs/UMCERTF1.lean:440 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_SG : ∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ) (ts : List ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 → (∀ x, Bad x → c x ∈ Es) → GridCert (fun t => binCDF m sc t) (fun t => capB r b t) U ts → stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U
~~~

### 1963. claim_D1

Source: proofs/UMCERTF1.lean:455 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_D1 : ∀ (n s b : ℕ) (r L t : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ L → 0 ≤ t → t ≤ 1 → survH t (hardKill s) n 0 * capB r b (min 1 (L * t)) ≤ (1 - r) + r * (L * (((s : ℝ) + 1) / ((n : ℝ) + 1)))
~~~

### 1964. claim_D2

Source: proofs/UMCERTF1.lean:468 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_D2 : ∀ (n ns b : ℕ) (r L t : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ L → 1 ≤ ns → 0 ≤ t → t ≤ 1 → survH t (softKill ns) n 0 * capB r b (min 1 (L * t)) ≤ (1 - r) + r * (L * ((ns : ℝ) / ((n : ℝ) + 1)))
~~~

### 1965. claim_F

Source: proofs/UMCERTF1.lean:487 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_F : ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ), IsKernel M → IsDist PH → 1 ≤ N → (∃ x, Bad x) → (∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b t ≤ U
~~~

### 1966. claim_X

Source: proofs/UMCERTF1.lean:504 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_X : ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ), IsKernel M → IsDist PH → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N → (∃ x, Bad x) → (∀ x, Bad x → ∀ z, M x z ≤ push M PH z) → ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ↔ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b t ≤ U))
~~~

### 1967. claim_Xp

Source: proofs/UMCERTF1.lean:532 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_Xp : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (g : Z → C) (PH : X → ℝ) (p : ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ), IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → IsDist PH → 0 < p → (∀ x, Bad x → p ≤ contentLaw c PH (c x)) → (∃ x, Bad x ∧ contentLaw c PH (c x) = p) → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N → ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → protocolCat Bad (fun x => K (c x)) PH κ nh r b N ρ φ π ≤ U) ↔ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b (min 1 ((1 / p) * t)) ≤ U))
~~~

### 1968. claim_S2

Source: proofs/UMCERTF1.lean:620 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_S2 : ∀ (X Z C : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (g : Z → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ), IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → 0 ≤ r → r ≤ 1 → 1 ≤ N → (∃ x, Bad x) → (∀ x, Bad x → c x ∈ Es) → ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U) ↔ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → binCDF m sc t * capB r b t ≤ U))
~~~

### 1969. claim

Source: proofs/UMCERTF1.lean:646 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMCERTF1.Claim
~~~

### 1970. bin12

Source: proofs/UMCERTF1.lean:652 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bin12 (s : ℝ) : binCDF 12 1 s = (1 - s) ^ 12 + 12 * s * (1 - s) ^ 11
~~~

### 1971. bin30

Source: proofs/UMCERTF1.lean:655 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bin30 (s : ℝ) : binCDF 30 1 s = (1 - s) ^ 30 + 30 * s * (1 - s) ^ 29
~~~

### 1972. soft5

Source: proofs/UMCERTF1.lean:658 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem soft5 (t : ℝ) : survH t (softKill 5) 100 0 = (1 - 1 / 5 * t) ^ 100
~~~

### 1973. hard1

Source: proofs/UMCERTF1.lean:665 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hard1 (t : ℝ) : survH t (hardKill 1) 30 0 = binCDF 30 1 t
~~~

### 1974. capB11

Source: proofs/UMCERTF1.lean:668 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB11 (a : ℝ) : capB 1 1 a = a
~~~

### 1975. capBk

Source: proofs/UMCERTF1.lean:672 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capBk (a : ℝ) : capB (9 / 10) 1 a = 1 / 10 + 9 / 10 * a
~~~

### 1976. idK_kernel

Source: proofs/UMCERTF1.lean:676 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem idK_kernel : IsKernel idK
~~~

### 1977. idK_dec

Source: proofs/UMCERTF1.lean:684 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem idK_dec : ∀ e z : Bool, idK e z ≠ 0 → id z = e
~~~

### 1978. ptTrue_dist

Source: proofs/UMCERTF1.lean:691 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ptTrue_dist : IsDist ptTrue
~~~

### 1979. w_main

Source: proofs/UMCERTF1.lean:698 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_main : GridCert (fun t => binCDF 12 1 t) (fun t => capB 1 1 t) (7/100) gridMain
~~~

### 1980. w_soft

Source: proofs/UMCERTF1.lean:704 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_soft : GridCert (fun t => survH t (softKill 5) 100 0) (fun t => capB 1 1 (min 1 (1 * t))) (19/1000) gridSoft
~~~

### 1981. w_kink

Source: proofs/UMCERTF1.lean:711 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_kink : GridCert (fun t => survH t (hardKill 1) 30 0) (fun t => capB (9/10) 1 (min 1 (4 * t))) (17/100) gridKink
~~~

### 1982. w_strat

Source: proofs/UMCERTF1.lean:718 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_strat : (6833/100000 : ℝ) ≤ stratProtocolCat (fun x : Bool => x = true) idK id Finset.univ 12 1 1 1 1 (fun _ : Unit => 1) (fun _ z => if z = true then 1/8 else 0) (fun _ _ x => if x = true then 1 else 0)
~~~

### 1983. w_prot

Source: proofs/UMCERTF1.lean:727 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_prot : (6833/100000 : ℝ) ≤ protocolCat (fun x : Bool => x = true) idK ptTrue (hardKill 1) 12 1 1 1 (fun _ : Unit => 1) (fun _ _ => 1/8) (fun _ _ x => if x = true then 1 else 0)
~~~

### 1984. witness

Source: proofs/UMCERTF1.lean:738 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMCERTF1.Witness
~~~

## proofs/UMDEFERF1.lean

### 1985. mul_le_mul_of_pos_imp

Source: proofs/UMDEFERF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mul_le_mul_of_pos_imp {p x y : ℝ} (hp : 0 ≤ p) (h : 0 < p → x ≤ y) : p * x ≤ p * y
~~~

### 1986. conv01

Source: proofs/UMDEFERF1.lean:11 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conv01 {p v w : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : 0 ≤ p * v + (1 - p) * w ∧ p * v + (1 - p) * w ≤ 1
~~~

### 1987. wsum01

Source: proofs/UMDEFERF1.lean:18 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum01 {Y : Type} [Fintype Y] (w f : Y → ℝ) (hw : IsDist w) (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) : 0 ≤ ∑ y, w y * f y ∧ ∑ y, w y * f y ≤ 1
~~~

### 1988. prod3_nonneg

Source: proofs/UMDEFERF1.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prod3_nonneg {p q c : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hc : 0 ≤ c) : 0 ≤ p * q * c
~~~

### 1989. prod3_le_one

Source: proofs/UMDEFERF1.lean:26 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prod3_le_one {p q c : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : p * q * c ≤ 1
~~~

### 1990. theta_bounds

Source: proofs/UMDEFERF1.lean:31 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem theta_bounds {η α : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : 0 ≤ theta η α ∧ theta η α ≤ 1
~~~

### 1991. one_sub_theta

Source: proofs/UMDEFERF1.lean:38 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem one_sub_theta (η α : ℝ) : 1 - theta η α = (1 - η) * (1 - α)
~~~

### 1992. retry_zero

Source: proofs/UMDEFERF1.lean:43 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_zero (A θ : ℝ) : retry A θ 0 = 0
~~~

### 1993. retry_succ

Source: proofs/UMDEFERF1.lean:45 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_succ (A θ : ℝ) (n : ℕ) : retry A θ (n + 1) = A + (1 - A) * (1 - θ) * retry A θ n
~~~

### 1994. retry_bounds

Source: proofs/UMDEFERF1.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_bounds {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : ∀ n, 0 ≤ retry A θ n ∧ retry A θ n ≤ 1
~~~

### 1995. retry_le_succ

Source: proofs/UMDEFERF1.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_le_succ {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ1 : θ ≤ 1) : ∀ n, retry A θ n ≤ retry A θ (n + 1)
~~~

### 1996. retry_mono

Source: proofs/UMDEFERF1.lean:73 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_mono {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ1 : θ ≤ 1) {m n : ℕ} (hmn : m ≤ n) : retry A θ m ≤ retry A θ n
~~~

### 1997. retry_closed

Source: proofs/UMDEFERF1.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_closed (A θ : ℝ) : ∀ n, (θ + A * (1 - θ)) * retry A θ n = A * (1 - ((1 - A) * (1 - θ)) ^ n)
~~~

### 1998. retry_le_ratio

Source: proofs/UMDEFERF1.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_le_ratio (A θ : ℝ) (n : ℕ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hD : 0 < θ + A * (1 - θ)) : retry A θ n ≤ A / (θ + A * (1 - θ))
~~~

### 1999. retry_limit

Source: proofs/UMDEFERF1.lean:93 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_limit (A θ : ℝ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hD : 0 < θ + A * (1 - θ)) : Tendsto (fun n : ℕ => retry A θ n) atTop (𝓝 (A / (θ + A * (1 - θ))))
~~~

### 2000. theta_retry_le

Source: proofs/UMDEFERF1.lean:112 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem theta_retry_le {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ) : θ * retry A θ n ≤ A
~~~

### 2001. fc_zero

Source: proofs/UMDEFERF1.lean:121 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_zero (r A θ : ℝ) (b u : ℕ) : finiteCap r A θ b 0 u = 0
~~~

### 2002. fc_ge

Source: proofs/UMDEFERF1.lean:124 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_ge (r A θ : ℝ) {b u : ℕ} (n : ℕ) (hbu : b ≤ u) : finiteCap r A θ b n u = retry A θ n
~~~

### 2003. fc_lt

Source: proofs/UMDEFERF1.lean:132 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_lt (r A θ : ℝ) {b u : ℕ} (n : ℕ) (hu : u < b) : finiteCap r A θ b (n + 1) u = max (1 - r + r * A) (retry A θ (n + 1 - (b - u)))
~~~

### 2004. fc_le_succ

Source: proofs/UMDEFERF1.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_le_succ {r A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (b n u : ℕ) : finiteCap r A θ b n u ≤ finiteCap r A θ b (n + 1) u
~~~

### 2005. fc_step

Source: proofs/UMDEFERF1.lean:151 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_step {r A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {b u : ℕ} (n : ℕ) (hu : u < b) : finiteCap r A θ b n (u + 1) ≤ finiteCap r A θ b (n + 1) u
~~~

### 2006. catV_eta_one

Source: proofs/UMDEFERF1.lean:174 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catV_eta_one (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (a : Service X Z) (b : ℕ) : ∀ n u h, catV Bad M φ π r 1 a b n u h = cat Bad M φ π r b n u h
~~~

### 2007. catV_bounds

Source: proofs/UMDEFERF1.lean:185 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catV_bounds (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η : ℝ) (a : Service X Z) (b : ℕ) (hc : Core M φ π r η) (ha : IsService a) : ∀ n u h, 0 ≤ catV Bad M φ π r η a b n u h ∧ catV Bad M φ π r η a b n u h ≤ 1
~~~

### 2008. catD_cap

Source: proofs/UMDEFERF1.lean:221 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catD_cap (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α A : ℝ) (b : ℕ) (hc : Core M φ π r η) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hbad : ∀ x, Bad x → E (M x) φ ≤ A) : ∀ n u h, catD Bad M φ π r η α b n u h ≤ finiteCap r A (theta η α) b n u
~~~

### 2009. bridge

Source: proofs/UMDEFERF1.lean:306 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bridge (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α : ℝ) (a : Service X Z) (b n0 u0 : ℕ) (h0 : Hist X Z) (hc : Core M φ π r η) (ha : IsService a) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hfl : UniformFloor Bad M φ π η a b n0 u0 h0 α) : ∀ n u h, Reach Bad M φ π η a b n0 u0 h0 n u h → catV Bad M φ π r η a b n u h ≤ catD Bad M φ π r η α b n u h
~~~

### 2010. attain

Source: proofs/UMDEFERF1.lean:382 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attain [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (r η α A : ℝ) (b u : ℕ) (x : X) (hM : IsKernel M) (hx : Bad x) (hbu : b ≤ u) : ∀ n (h : Hist X Z), catD Bad M (fun _ => A) (fun _ x' => if x' = x then 1 else 0) r η α b n u h = retry A (theta η α) n
~~~

### 2011. seed_bound

Source: proofs/UMDEFERF1.lean:403 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seed_bound {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r η α L : ℝ) (a : Service X Z) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (hPH : IsDist PH) (hc : Core M φ π r η) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hL : 0 ≤ L) (ha : IsService a) (hfl : UniformFloor Bad M φ π η a b N 0 [] α) (hdom : ∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ surv (push M PH) φ (hardKill ns) nh 0 * catV Bad M φ π r η a b N 0 [] ≤ survH t (hardKill ns) nh 0 * finiteCap r (min 1 (L * t)) (theta η α) b N 0
~~~

### 2012. cert

Source: proofs/UMDEFERF1.lean:427 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cert {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r η α L U : ℝ) (a : Ω → Service X Z) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) (hpc : PairCore M PH ρ φ π r η) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hL : 0 ≤ L) (hfl : ProtocolFloor Bad M φ π η a b N α) (hdom : ∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) (hU : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t (hardKill ns) nh 0 * finiteCap r (min 1 (L * t)) (theta η α) b N 0 ≤ U) : protocolCatV Bad M PH (hardKill ns) nh r η a b N ρ φ π ≤ U
~~~

### 2013. coarse_bound

Source: proofs/UMDEFERF1.lean:445 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem coarse_bound (r θ L t : ℝ) (b N nh ns : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : survH t (hardKill ns) nh 0 * finiteCap r (min 1 (L * t)) θ b N 0 ≤ max (if 0 < b then (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) else 0) (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)) / θ)
~~~

### 2014. cnt_append

Source: proofs/UMDEFERF1.lean:486 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cnt_append (h : Hist Bool Bool) (x z c : Bool) : ((h ++ [(x, z, c)]).filter (fun e => e.2.2 = false)).length = (h.filter (fun e => e.2.2 = false)).length + (if c = false then 1 else 0)
~~~

### 2015. attack_phase

Source: proofs/UMDEFERF1.lean:491 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attack_phase (r t : ℝ) (b : ℕ) : ∀ n (u : ℕ) (h : Hist Bool Bool), b ≤ u → b ≤ (h.filter (fun e => e.2.2 = false)).length → catV (X
~~~

### 2016. burn_phase

Source: proofs/UMDEFERF1.lean:511 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem burn_phase (r t : ℝ) (b : ℕ) : ∀ n k (u : ℕ) (h : Hist Bool Bool), u = (h.filter (fun e => e.2.2 = false)).length → u + k = b → catV (X
~~~

### 2017. nogo_eq

Source: proofs/UMDEFERF1.lean:533 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nogo_eq (PH : Bool → ℝ) (nh ns b N : ℕ) (r t : ℝ) (hPH : IsDist PH) : protocolCatD (X
~~~

### 2018. nogo_lb

Source: proofs/UMDEFERF1.lean:549 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nogo_lb (PH : Bool → ℝ) (nh ns b N : ℕ) (t : ℝ) (hPH : IsDist PH) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (1 - t) ^ nh * (1 - (1 - t) ^ (N - b)) ≤ binCDF nh ns (PH true * t) * (1 - (1 - t) ^ (N - b))
~~~

### 2019. limit_e

Source: proofs/UMDEFERF1.lean:576 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem limit_e' (nh : ℕ) : Tendsto (fun K : ℕ => (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ nh * (1 - (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ K)) atTop (𝓝 1)
~~~

### 2020. claim

Source: proofs/UMDEFERF1.lean:625 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMDEFERF1.Claim
~~~

### 2021. witness

Source: proofs/UMDEFERF1.lean:665 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMDEFERF1.Witness
~~~

## proofs/UMHSF1.lean

### 2022. mul_le_max0

Source: proofs/UMHSF1.lean:1 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mul_le_max0 (a φ : ℝ) (h0 : 0 ≤ φ) (h1 : φ ≤ 1) : a * φ ≤ max 0 a
~~~

### 2023. t2

Source: proofs/UMHSF1.lean:8 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t2 : ∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q φ : Z → ℝ), IsRule φ → E P φ ≤ Real.exp η * E Q φ + hs η P Q
~~~

### 2024. t2att

Source: proofs/UMHSF1.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t2att : ∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q : Z → ℝ), ∃ φ, IsRule φ ∧ E P φ = Real.exp η * E Q φ + hs η P Q
~~~

### 2025. hs0_symm

Source: proofs/UMHSF1.lean:35 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hs0_symm {Z : Type} [Fintype Z] (P Q : Z → ℝ) (hP : ∑ z, P z = 1) (hQ : ∑ z, Q z = 1) : hs 0 Q P = hs 0 P Q
~~~

### 2026. t1

Source: proofs/UMHSF1.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t1 : ∀ (Z : Type) [Fintype Z] (P Q φ : Z → ℝ), IsDist P → IsDist Q → IsRule φ → |E P φ - E Q φ| ≤ hs 0 P Q
~~~

### 2027. max0_sum_le

Source: proofs/UMHSF1.lean:60 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem max0_sum_le {X : Type} [Fintype X] (w f : X → ℝ) (hw : ∀ x, 0 ≤ w x) : max 0 (∑ x, w x * f x) ≤ ∑ x, w x * max 0 (f x)
~~~

### 2028. t4a

Source: proofs/UMHSF1.lean:66 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4a : ∀ (X Z : Type) [Fintype X] [Fintype Z] (η : ℝ) (K : X → Z → ℝ) (P Q : X → ℝ), IsKernel K → hs η (push K P) (push K Q) ≤ hs η P Q
~~~

### 2029. push_contentLaw

Source: proofs/UMHSF1.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_contentLaw {X Z C : Type} [Fintype X] [Fintype C] [DecidableEq C] (K : C → Z → ℝ) (c : X → C) (P : X → ℝ) : push K (contentLaw c P) = push (fun x => K (c x)) P
~~~

### 2030. t4b

Source: proofs/UMHSF1.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4b : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η : ℝ) (M : X → Z → ℝ) (c : X → C) (PA PH : X → ℝ), ContentOnly M c → hs η (push M PA) (push M PH) ≤ hs η (contentLaw c PA) (contentLaw c PH)
~~~

### 2031. delta_dist

Source: proofs/UMHSF1.lean:106 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem delta_dist {C : Type} [Fintype C] [DecidableEq C] (e : C) : IsDist (delta e)
~~~

### 2032. push_decode

Source: proofs/UMHSF1.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_decode {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (P : X → ℝ) : push (fun z => delta (g z)) (push M P) = contentLaw c P
~~~

### 2033. t4c

Source: proofs/UMHSF1.lean:126 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4c : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η : ℝ) (M : X → Z → ℝ) (c : X → C) (PA PH : X → ℝ), IsKernel M → ContentPreserving M c → hs η (contentLaw c PA) (contentLaw c PH) ≤ hs η (push M PA) (push M PH)
~~~

### 2034. t5d

Source: proofs/UMHSF1.lean:135 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t5d : ∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q P' Q' : Z → ℝ), hs η P Q ≤ hs η P' Q' + ∑ z, max 0 (P z - P' z) + Real.exp η * ∑ z, max 0 (Q' z - Q z)
~~~

### 2035. sum_max0_mix

Source: proofs/UMHSF1.lean:153 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_max0_mix {Z C : Type} [Fintype Z] [Fintype C] (w : Z → ℝ) (hw : ∀ z, 0 ≤ w z) (f : Z → C → ℝ) : ∑ e, max 0 (∑ z, w z * f z e) ≤ ∑ z, w z * ∑ e, max 0 (f z e)
~~~

### 2036. sum_max0_delta_sub_le

Source: proofs/UMHSF1.lean:161 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_max0_delta_sub_le {C : Type} [Fintype C] [DecidableEq C] (a b : C) : ∑ e, max 0 (delta a e - delta b e) ≤ 1
~~~

### 2037. inner_A

Source: proofs/UMHSF1.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inner_A {Z C : Type} [Fintype Z] [Fintype C] [DecidableEq C] (m : Z → ℝ) (hm : IsDist m) (a : C) (g : Z → C) : ∑ e, max 0 (delta a e - ∑ z, m z * delta (g z) e) ≤ ∑ z, m z * (if g z = a then 0 else 1)
~~~

### 2038. inner_H

Source: proofs/UMHSF1.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inner_H {Z C : Type} [Fintype Z] [Fintype C] [DecidableEq C] (m : Z → ℝ) (hm : IsDist m) (a : C) (g : Z → C) : ∑ e, max 0 (∑ z, m z * delta (g z) e - delta a e) ≤ ∑ z, m z * (if g z = a then 0 else 1)
~~~

### 2039. push_push

Source: proofs/UMHSF1.lean:203 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_push {X Z C : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (D : Z → C → ℝ) (P : X → ℝ) (e : C) : push D (push M P) e = ∑ x, P x * ∑ z, M x z * D z e
~~~

### 2040. approx_A

Source: proofs/UMHSF1.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem approx_A {X Z C : Type} [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (γ : ℝ) (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PA : X → ℝ) (hM : IsKernel M) (hPA : IsDist PA) (hγ : ∀ x, ∑ z, M x z * (if g z = c x then 0 else 1) ≤ γ) : ∑ e, max 0 (contentLaw c PA e - push (fun z => delta (g z)) (push M PA) e) ≤ γ
~~~

### 2041. approx_H

Source: proofs/UMHSF1.lean:231 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem approx_H {X Z C : Type} [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (γ : ℝ) (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PH : X → ℝ) (hM : IsKernel M) (hPH : IsDist PH) (hγ : ∀ x, ∑ z, M x z * (if g z = c x then 0 else 1) ≤ γ) : ∑ e, max 0 (push (fun z => delta (g z)) (push M PH) e - contentLaw c PH e) ≤ γ
~~~

### 2042. t4c_approx

Source: proofs/UMHSF1.lean:250 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4c_approx : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η γ : ℝ) (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PA PH : X → ℝ), IsKernel M → IsDist PA → IsDist PH → (∀ x, ∑ z, M x z * (if g z = c x then 0 else 1) ≤ γ) → hs η (contentLaw c PA) (contentLaw c PH) ≤ hs η (push M PA) (push M PH) + (1 + Real.exp η) * γ
~~~

### 2043. t4c'1

Source: proofs/UMHSF1.lean:266 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4c'1 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (B : Finset X) (hB : B.Nonempty) (Q : Z → ℝ) (L : ℝ), IsKernel M → IsDist Q → (∀ x ∈ B, ∀ z, M x z ≤ L * Q z) → ∑ z, B.sup' hB (fun x => M x z) ≤ L
~~~

### 2044. t4c'2

Source: proofs/UMHSF1.lean:275 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4c'2 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (B : Finset X) (hB : B.Nonempty), IsKernel M → ∃ Q, IsDist Q ∧ ∀ x ∈ B, ∀ z, M x z ≤ (∑ z', B.sup' hB (fun x' => M x' z')) * Q z
~~~

### 2045. dom

Source: proofs/UMHSF1.lean:299 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dom : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (PH : X → ℝ) (Bad : X → Prop) (p : ℝ), ContentOnly M c → IsDist PH → 0 < p → (∀ x, Bad x → p ≤ contentLaw c PH (c x)) → ∀ x, Bad x → ∀ z, M x z ≤ (1 / p) * push M PH z
~~~

### 2046. claim

Source: proofs/UMHSF1.lean:320 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 2047. idKernel

Source: proofs/UMHSF1.lean:323 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem idKernel : IsKernel (fun (x : Bool) (z : Bool) => if z = x then (1 : ℝ) else 0)
~~~

### 2048. witness

Source: proofs/UMHSF1.lean:329 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## proofs/UMLOWERF1.lean

### 2049. pat_sum_prod

Source: proofs/UMLOWERF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pat_sum_prod {n : ℕ} (f : Fin n → Bool → ℝ) : ∑ pat : Fin n → Bool, ∏ i, f i (pat i) = ∏ i, ∑ b, f i b
~~~

### 2050. bern_nonneg

Source: proofs/UMLOWERF1.lean:7 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bern_nonneg {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (pat : Fin n → Bool) : 0 ≤ ∏ i, (if pat i then a i else 1 - a i)
~~~

### 2051. bern_sum

Source: proofs/UMLOWERF1.lean:15 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bern_sum {n : ℕ} (a : Fin n → ℝ) : ∑ pat : Fin n → Bool, ∏ i, (if pat i then a i else 1 - a i) = 1
~~~

### 2052. bern_mean

Source: proofs/UMLOWERF1.lean:20 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bern_mean {n : ℕ} (a : Fin n → ℝ) : ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) * ((univ.filter (fun i => pat i = true)).card : ℝ) = ∑ i, a i
~~~

### 2053. keep_lb

Source: proofs/UMLOWERF1.lean:49 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem keep_lb (ns : ℕ) (k : ℝ) (m : ℕ) (hk0 : 0 ≤ k) (hk : m ≤ ns → k = 1) : 1 - (m : ℝ) / ((ns : ℝ) + 1) ≤ k
~~~

### 2054. inner_lb

Source: proofs/UMLOWERF1.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inner_lb {n : ℕ} (ns : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (kp : (Fin n → Bool) → ℝ) (hk0 : ∀ pat, 0 ≤ kp pat) (hk1 : ∀ pat, (univ.filter (fun i => pat i = true)).card ≤ ns → kp pat = 1) : 1 - (∑ i, a i) / ((ns : ℝ) + 1) ≤ ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) * kp pat
~~~

### 2055. inner_nonneg

Source: proofs/UMLOWERF1.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inner_nonneg {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (kp : (Fin n → Bool) → ℝ) (hk0 : ∀ pat, 0 ≤ kp pat) : 0 ≤ ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) * kp pat
~~~

### 2056. pass_eq

Source: proofs/UMLOWERF1.lean:82 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pass_eq {X Z C : Type} [Fintype Z] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (t : ℝ) (x ω : X) : ∑ z, M x z * (if g z = c ω then t else 0) = if c x = c ω then t else 0
~~~

### 2057. class_sum_le

Source: proofs/UMLOWERF1.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem class_sum_le {X C : Type} [DecidableEq C] (c : X → C) (S : Finset X) (hinj : Set.InjOn c (S : Set X)) (t : ℝ) (ht : 0 ≤ t) (x : X) : ∑ ω ∈ S, (if c x = c ω then t else 0) ≤ t
~~~

### 2058. cat_ge

Source: proofs/UMLOWERF1.lean:104 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_ge {X Z : Type} [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (r : ℝ) (b N : ℕ) (ω : X) (hM : IsKernel M) (hφ : IsRule φ) (hr1 : r ≤ 1) (hN : 1 ≤ N) (hω : Bad ω) : ∑ z, M ω z * φ z ≤ cat Bad M φ (fun _ x => if x = ω then 1 else 0) r b N 0 []
~~~

### 2059. surv_sum_lb

Source: proofs/UMLOWERF1.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_sum_lb {X Ω : Type} [Fintype X] (n ns : ℕ) (D : (Fin n → X) → ℝ) (hD : IsDist D) (keep : (Fin n → X) → (Fin n → Bool) → ℝ) (hkeep : ∀ xs pat, 0 ≤ keep xs pat) (hkeep1 : ∀ xs pat, (univ.filter (fun i => pat i = true)).card ≤ ns → keep xs pat = 1) (S : Finset Ω) (a : Ω → X → ℝ) (ha : ∀ ω x, 0 ≤ a ω x ∧ a ω x ≤ 1) (t : ℝ) (hsumA : ∀ x, ∑ ω ∈ S, a ω x ≤ t) : (S.card : ℝ) - n * t / ((ns : ℝ) + 1) ≤ ∑ ω ∈ S, ∑ xs, D xs * ∑ pat : Fin n → Bool, (∏ i, (if pat i then a ω (xs i) else 1 - a ω (xs i))) * keep xs pat
~~~

### 2060. combine

Source: proofs/UMLOWERF1.lean:151 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem combine {X : Type} [Fintype X] [DecidableEq X] (S : Finset X) (n ns : ℕ) (sv ct : X → ℝ) (t : ℝ) (hS : 0 < S.card) (ht : 0 ≤ t) (hsv0 : ∀ ω, 0 ≤ sv ω) (hct : ∀ ω ∈ S, t ≤ ct ω) (hsum : (S.card : ℝ) - n * t / ((ns : ℝ) + 1) ≤ ∑ ω ∈ S, sv ω) : t * (1 - t * (n : ℝ) / ((S.card : ℝ) * ((ns : ℝ) + 1))) ≤ ∑ ω, (if ω ∈ S then 1 / (S.card : ℝ) else 0) * sv ω * ct ω
~~~

### 2061. claim

Source: proofs/UMLOWERF1.lean:176 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMLOWERF1.Claim
~~~

### 2062. none_pass

Source: proofs/UMLOWERF1.lean:227 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem none_pass {n : ℕ} (a : Fin n → ℝ) : ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) * (if (univ.filter (fun i => pat i = true)).card ≤ 0 then (1 : ℝ) else 0) = ∏ i, (1 - a i)
~~~

### 2063. witness

Source: proofs/UMLOWERF1.lean:252 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMLOWERF1.Witness
~~~

## proofs/UMNOGOF1.lean

### 2064. submit_sum

Source: proofs/UMNOGOF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma submit_sum {X Z : Type} [Fintype X] (xs : X) (ω : Unit) (h : Hist X Z) (f : X → ℝ) : ∑ x, submit (Z
~~~

### 2065. submit_dist

Source: proofs/UMNOGOF1.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma submit_dist {X Z : Type} [Fintype X] (xs : X) (ω : Unit) (h : Hist X Z) : IsDist (submit (Z
~~~

### 2066. classMonitor_rule

Source: proofs/UMNOGOF1.lean:22 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma classMonitor_rule {Z C : Type} [DecidableEq C] (g : Z → C) (e : C) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : ∀ ω, IsRule (classMonitor g e t ω)
~~~

### 2067. protocolCat_unit

Source: proofs/UMNOGOF1.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma protocolCat_unit {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (φ : Unit → Z → ℝ) (π : Unit → Hist X Z → X → ℝ) : protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) φ π = surv (push M PH) (φ ()) κ nh 0 * cat Bad M (φ ()) (π ()) r b N 0 []
~~~

### 2068. cat_submit

Source: proofs/UMNOGOF1.lean:39 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma cat_submit {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (xs : X) (hx : Bad xs) (r : ℝ) (b N : ℕ) (hN : 1 ≤ N) : cat Bad M φ (submit (Z
~~~

### 2069. rate_eq

Source: proofs/UMNOGOF1.lean:47 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma rate_eq {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (PH : X → ℝ) (e : C) (t : ℝ) : ∑ z, push M PH z * classMonitor g e t () z = t * contentLaw c PH e
~~~

### 2070. pass_sum

Source: proofs/UMNOGOF1.lean:70 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma pass_sum {X Z C : Type} [Fintype Z] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (xs : X) (t K : ℝ) : ∑ z, M xs z * (classMonitor g (c xs) t () z * 1 + (1 - classMonitor g (c xs) t () z) * K) = t + (1 - t) * K
~~~

### 2071. prot_formula

Source: proofs/UMNOGOF1.lean:82 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma prot_formula {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PH : X → ℝ) (xs : X) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (hPH : IsDist PH) (hx : Bad xs) (t : ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (hN : 1 ≤ N) : protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (classMonitor g (c xs) t) (submit (Z
~~~

### 2072. survH_ge

Source: proofs/UMNOGOF1.lean:93 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma survH_ge (h : ℝ) (κ : ℕ → ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1) : ∀ n j, (1 - h) ^ n ≤ survH h κ n j
~~~

### 2073. contentLaw_nonneg

Source: proofs/UMNOGOF1.lean:112 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma contentLaw_nonneg {X C : Type} [Fintype X] [DecidableEq C] (c : X → C) (PH : X → ℝ) (hPH : IsDist PH) (e : C) : 0 ≤ contentLaw c PH e
~~~

### 2074. classes_sum_le

Source: proofs/UMNOGOF1.lean:122 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma classes_sum_le {X C : Type} [Fintype X] [DecidableEq C] (c : X → C) (PH : X → ℝ) (hPH : IsDist PH) (S : Finset X) (hinj : Set.InjOn c (S : Set X)) : ∑ x ∈ S, contentLaw c PH (c x) ≤ 1
~~~

### 2075. claim

Source: proofs/UMNOGOF1.lean:145 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMNOGOF1.Claim
~~~

### 2076. witnessM_kernel

Source: proofs/UMNOGOF1.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witnessM_kernel : IsKernel witnessM
~~~

### 2077. witnessM_dec

Source: proofs/UMNOGOF1.lean:195 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witnessM_dec : ∀ x z, witnessM x z ≠ 0 → (id : Fin 4 → Fin 4) z = id x
~~~

### 2078. witnessPH_dist

Source: proofs/UMNOGOF1.lean:202 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witnessPH_dist : IsDist witnessPH
~~~

### 2079. witness_content

Source: proofs/UMNOGOF1.lean:209 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witness_content : contentLaw (id : Fin 4 → Fin 4) witnessPH 2 = 1 / 4
~~~

### 2080. witnessS_card

Source: proofs/UMNOGOF1.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witnessS_card : witnessS.card = 4
~~~

### 2081. witness

Source: proofs/UMNOGOF1.lean:215 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMNOGOF1.Witness
~~~

## proofs/UMPROTF1.lean

### 2082. wsum_le

Source: proofs/UMPROTF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum_le {Y : Type} [Fintype Y] (w f : Y → ℝ) (c : ℝ) (hw : IsDist w) (hf : ∀ y, f y ≤ c) : ∑ y, w y * f y ≤ c
~~~

### 2083. wsum_nonneg

Source: proofs/UMPROTF1.lean:9 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum_nonneg {Y : Type} [Fintype Y] (w f : Y → ℝ) (hw : ∀ y, 0 ≤ w y) (hf : ∀ y, 0 ≤ f y) : 0 ≤ ∑ y, w y * f y
~~~

### 2084. t3a

Source: proofs/UMPROTF1.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t3a {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r A : ℝ) (b : ℕ) (hM : IsKernel M) (hφ : IsRule φ) (hπ : ∀ h, IsDist (π h)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hbad : ∀ x, Bad x → E (M x) φ ≤ A) : ∀ n u h, 0 ≤ cat Bad M φ π r b n u h ∧ cat Bad M φ π r b n u h ≤ (if u < b then 1 - r + r * A else A)
~~~

### 2085. cat_le

Source: proofs/UMPROTF1.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_le {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r A : ℝ) (b : ℕ) (hM : IsKernel M) (hφ : IsRule φ) (hπ : ∀ h, IsDist (π h)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hbad : ∀ x, Bad x → E (M x) φ ≤ A) (n u : ℕ) (h : Hist X Z) : 0 ≤ cat Bad M φ π r b n u h ∧ cat Bad M φ π r b n u h ≤ 1 - r + r * A
~~~

### 2086. push_dist

Source: proofs/UMPROTF1.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_dist {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (hM : IsKernel M) (hP : IsDist PH) : IsDist (push M PH)
~~~

### 2087. prot_bound

Source: proofs/UMPROTF1.lean:108 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prot_bound {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) (C : ℝ) (hM : IsKernel M) (hρ : IsDist ρ) (hφ : ∀ ω, IsRule (φ ω)) (hπ : ∀ ω h, IsDist (π ω h)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hω : ∀ ω, ∃ A, 0 ≤ A ∧ A ≤ 1 ∧ (∀ x, Bad x → E (M x) (φ ω) ≤ A) ∧ 0 ≤ surv (push M PH) (φ ω) κ nh 0 ∧ surv (push M PH) (φ ω) κ nh 0 * (1 - r + r * A) ≤ C) : protocolCat Bad M PH κ nh r b N ρ φ π ≤ C
~~~

### 2088. rate_facts

Source: proofs/UMPROTF1.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rate_facts {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (φ : Z → ℝ) (hM : IsKernel M) (hP : IsDist PH) (hφ : IsRule φ) : 0 ≤ ∑ z, push M PH z * φ z ∧ ∑ z, push M PH z * φ z ≤ 1
~~~

### 2089. E_le_one

Source: proofs/UMPROTF1.lean:133 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_le_one {X Z : Type} [Fintype Z] (M : X → Z → ℝ) (φ : Z → ℝ) (hM : IsKernel M) (hφ : IsRule φ) (x : X) : E (M x) φ ≤ 1
~~~

### 2090. surv_eq

Source: proofs/UMPROTF1.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_eq {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (φ : Z → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (hM : IsKernel M) (hP : IsDist PH) : surv (push M PH) φ κ nh 0 = survH (∑ z, push M PH z * φ z) κ nh 0
~~~

### 2091. final_dom

Source: proofs/UMPROTF1.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem final_dom (S h L r A B : ℝ) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hA : A ≤ L * h) (hB : h * S ≤ B) : S * (1 - r + r * A) ≤ (1 - r) + r * (L * B)
~~~

### 2092. final_hs

Source: proofs/UMPROTF1.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem final_hs (S h r A δ c B : ℝ) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hA : A ≤ c * h + δ) (hB : h * S ≤ B) : S * (1 - r + r * A) ≤ (1 - r) + r * (δ + c * B)
~~~

### 2093. hardKill_prob

Source: proofs/UMPROTF1.lean:170 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hardKill_prob (ns : ℕ) : ∀ i, 0 ≤ hardKill ns i ∧ hardKill ns i ≤ 1
~~~

### 2094. E_dom

Source: proofs/UMPROTF1.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_dom {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (φ : Z → ℝ) (hφ : IsRule φ) (L : ℝ) (x : X) (hd : ∀ z, M x z ≤ L * push M PH z) : E (M x) φ ≤ L * ∑ z, push M PH z * φ z
~~~

### 2095. claim

Source: proofs/UMPROTF1.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMPROTF1.Claim
~~~

### 2096. witness

Source: proofs/UMPROTF1.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMPROTF1.Witness
~~~

## proofs/UMSTRATF1.lean

### 2097. surv_eq_bin

Source: proofs/UMSTRATF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_eq_bin {Z : Type} [Fintype Z] (q φ : Z → ℝ) (hq : ∑ z, q z = 1) (m sc : ℕ) : surv q φ (hardKill sc) m 0 = binCDF m sc (E q φ)
~~~

### 2098. rate01

Source: proofs/UMSTRATF1.lean:9 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rate01 {Z : Type} [Fintype Z] (q φ : Z → ℝ) (hq : IsDist q) (hφ : IsRule φ) : 0 ≤ E q φ ∧ E q φ ≤ 1
~~~

### 2099. factor01

Source: proofs/UMSTRATF1.lean:14 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem factor01 {Z : Type} [Fintype Z] (q φ : Z → ℝ) (hq : IsDist q) (hφ : IsRule φ) (m sc : ℕ) : 0 ≤ surv q φ (hardKill sc) m 0 ∧ surv q φ (hardKill sc) m 0 ≤ 1
~~~

### 2100. strat01

Source: proofs/UMSTRATF1.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem strat01 {Z C : Type} [Fintype Z] (K : C → Z → ℝ) (Es : Finset C) (φ : Z → ℝ) (m sc : ℕ) (hK : IsKernel K) (hφ : IsRule φ) : 0 ≤ stratSurv K Es φ m sc ∧ stratSurv K Es φ m sc ≤ 1
~~~

### 2101. strat_le_factor

Source: proofs/UMSTRATF1.lean:31 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem strat_le_factor {Z C : Type} [Fintype Z] (K : C → Z → ℝ) (Es : Finset C) (φ : Z → ℝ) (m sc : ℕ) (hK : IsKernel K) (hφ : IsRule φ) (e : C) (he : e ∈ Es) : stratSurv K Es φ m sc ≤ surv (K e) φ (hardKill sc) m 0
~~~

### 2102. exists_A

Source: proofs/UMSTRATF1.lean:44 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exists_A {X Z C : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (φ : Z → ℝ) (m sc : ℕ) (hK : IsKernel K) (hφ : IsRule φ) (hEs : ∀ x, Bad x → c x ∈ Es) : ∃ A, 0 ≤ A ∧ A ≤ 1 ∧ (∀ x, Bad x → E (K (c x)) φ ≤ A) ∧ A * stratSurv K Es φ m sc ≤ ((sc : ℝ) + 1) / ((m : ℝ) + 1)
~~~

### 2103. claim1

Source: proofs/UMSTRATF1.lean:72 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim1 : ∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r : ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 → (∀ x, Bad x → c x ∈ Es) → stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ (1 - r) + r * (((sc : ℝ) + 1) / ((m : ℝ) + 1))
~~~

### 2104. binCDF_at_zero

Source: proofs/UMSTRATF1.lean:98 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem binCDF_at_zero (m sc : ℕ) : binCDF m sc 0 = 1
~~~

### 2105. E_dec

Source: proofs/UMSTRATF1.lean:103 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_dec {Z C : Type} [Fintype Z] [DecidableEq C] (K : C → Z → ℝ) (g : Z → C) (t : ℝ) (e0 e : C) (hK : IsKernel K) (hdec : ∀ e z, K e z ≠ 0 → g z = e) : E (K e) (fun z => if g z = e0 then t else 0) = if e = e0 then t else 0
~~~

### 2106. strat_att

Source: proofs/UMSTRATF1.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem strat_att {Z C : Type} [Fintype Z] [DecidableEq C] (K : C → Z → ℝ) (g : Z → C) (Es : Finset C) (t : ℝ) (e0 : C) (m sc : ℕ) (hK : IsKernel K) (hdec : ∀ e z, K e z ≠ 0 → g z = e) (he0 : e0 ∈ Es) : stratSurv K Es (fun z => if g z = e0 then t else 0) m sc = binCDF m sc t
~~~

### 2107. cat_point

Source: proofs/UMSTRATF1.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_point {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] [DecidableEq X] (M : X → Z → ℝ) (φ : Z → ℝ) (r : ℝ) (b N : ℕ) (x : X) (hM : IsKernel M) (hx : Bad x) (hN : 1 ≤ N) (hb : 1 ≤ b) : cat Bad M φ (fun _ x' => if x' = x then 1 else 0) r b N 0 [] = 1 - r + r * E (M x) φ
~~~

### 2108. claim2

Source: proofs/UMSTRATF1.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim2 : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq C] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (g : Z → C) (Es : Finset C) (m sc b N : ℕ) (r t : ℝ) (x : X), IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → Bad x → c x ∈ Es → 1 ≤ N → 1 ≤ b → 0 ≤ t → t ≤ 1 → stratProtocolCat Bad K c Es m sc r b N (fun _ : Unit => 1) (fun _ z => if g z = c x then t else 0) (fun _ _ x' => if x' = x then 1 else 0) = binCDF m sc t * (1 - r + r * t)
~~~

### 2109. claim

Source: proofs/UMSTRATF1.lean:166 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMSTRATF1.Claim
~~~

### 2110. wK

Source: proofs/UMSTRATF1.lean:168 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wK : IsKernel witnessK
~~~

### 2111. wdec

Source: proofs/UMSTRATF1.lean:176 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wdec : ∀ e z : Bool, witnessK e z ≠ 0 → id z = e
~~~

### 2112. wval

Source: proofs/UMSTRATF1.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wval : stratProtocolCat (fun x : Bool => x = true) witnessK id (Finset.univ : Finset Bool) 12 1 1 1 1 (fun _ : Unit => 1) witnessPhi witnessPi = binCDF 12 1 (1 / 6) * (1 - 1 + 1 * (1 / 6 : ℝ))
~~~

### 2113. wbin

Source: proofs/UMSTRATF1.lean:190 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wbin : binCDF 12 1 (1 / 6 : ℝ) = (5 / 6) ^ 12 + 12 * (1 / 6) * (5 / 6) ^ 11
~~~

### 2114. witness

Source: proofs/UMSTRATF1.lean:194 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMSTRATF1.Witness
~~~

## proofs/UMSURVF1.lean

### 2115. binTerm_pascal

Source: proofs/UMSURVF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binTerm_pascal (n k : ℕ) (h : ℝ) : ((n + 1).choose (k + 1) : ℝ) * h ^ (k + 1) * (1 - h) ^ (n + 1 - (k + 1)) = h * ((n.choose k : ℝ) * h ^ k * (1 - h) ^ (n - k)) + (1 - h) * ((n.choose (k + 1) : ℝ) * h ^ (k + 1) * (1 - h) ^ (n - (k + 1)))
~~~

### 2116. binCDF_zero_n

Source: proofs/UMSURVF1.lean:21 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binCDF_zero_n (s : ℕ) (h : ℝ) : binCDF 0 s h = 1
~~~

### 2117. binCDF_n_zero

Source: proofs/UMSURVF1.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binCDF_n_zero (n : ℕ) (h : ℝ) : binCDF n 0 h = (1 - h) ^ n
~~~

### 2118. binCDF_pascal

Source: proofs/UMSURVF1.lean:34 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binCDF_pascal (n s : ℕ) (h : ℝ) : binCDF (n + 1) (s + 1) h = (1 - h) * binCDF n (s + 1) h + h * binCDF n s h
~~~

### 2119. survH_hard

Source: proofs/UMSURVF1.lean:43 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma survH_hard (h : ℝ) (ns : ℕ) : ∀ n j, j ≤ ns → survH h (hardKill ns) n j = binCDF n (ns - j) h
~~~

### 2120. survH_const

Source: proofs/UMSURVF1.lean:66 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma survH_const (h k : ℝ) : ∀ (n j : ℕ), survH h (fun _ => k) n j = (1 - k * h) ^ n
~~~

### 2121. survH_prob

Source: proofs/UMSURVF1.lean:75 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma survH_prob (h : ℝ) (κ : ℕ → ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ 1) : ∀ n j, 0 ≤ survH h κ n j ∧ survH h κ n j ≤ 1
~~~

### 2122. binCDF_le_one

Source: proofs/UMSURVF1.lean:99 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binCDF_le_one (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : binCDF n s h ≤ 1
~~~

### 2123. first_moment

Source: proofs/UMSURVF1.lean:106 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma first_moment (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : ((n : ℝ) + 1) * (h * binCDF n s h) ≤ (s : ℝ) + 1
~~~

### 2124. first_moment

Source: proofs/UMSURVF1.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma first_moment' (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : h * binCDF n s h ≤ ((s : ℝ) + 1) / ((n : ℝ) + 1)
~~~

### 2125. claim

Source: proofs/UMSURVF1.lean:152 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 2126. witness

Source: proofs/UMSURVF1.lean:191 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## proofs/UMUSEF1.lean

### 2127. usef_split

Source: proofs/UMUSEF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_split {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (μ : X → ℝ) (φ : Z → ℝ) (hM : IsKernel M) (hμ : IsDist μ) (A B : ℝ) : ∑ x, μ x * ∑ z, M x z * (φ z * A + (1 - φ z) * B) = (1 - flagRate M μ φ) * A + flagRate M μ φ * B
~~~

### 2128. usef_flag01

Source: proofs/UMUSEF1.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_flag01 {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (μ : X → ℝ) (φ : Z → ℝ) (hM : IsKernel M) (hφ : IsRule φ) (hμ : IsDist μ) : 0 ≤ flagRate M μ φ ∧ flagRate M μ φ ≤ 1
~~~

### 2129. usef_halt

Source: proofs/UMUSEF1.lean:37 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_halt {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (μ : X → ℝ) (b : ℕ) (hM : IsKernel M) (hμ : IsDist μ) (hsupp : ∀ x, μ x ≠ 0 → ¬ Bad x) : ∀ n u h, 1 - haltP Bad M φ (fun _ => μ) b n u h = survH (flagRate M μ φ) (hardKill b) n u
~~~

### 2130. usef_bin01

Source: proofs/UMUSEF1.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_bin01 (n s : ℕ) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : 0 ≤ binCDF n s a ∧ binCDF n s a ≤ 1
~~~

### 2131. usef_hc

Source: proofs/UMUSEF1.lean:80 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_hc {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh b N : ℕ) (φ₀ : Z → ℝ) (μ : X → ℝ) (hM : IsKernel M) (hP : IsDist PH) (hμ : IsDist μ) (hsupp : ∀ x, μ x ≠ 0 → ¬ Bad x) : honestCompletion Bad M PH κ nh b N φ₀ μ = survH (missRate M PH φ₀) κ nh 0 * binCDF N b (flagRate M μ φ₀)
~~~

### 2132. usef_vb

Source: proofs/UMUSEF1.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_vb {X Z : Type} [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r h : ℝ) (b N : ℕ) (x : X) (hM : IsKernel M) (hP : IsDist PH) (hx : Bad x) (hN : 1 ≤ N) : viewBlindRisk Bad M PH κ nh r b N h x = survH h κ nh 0 * (h + (if 0 < b then (1 - r) * (1 - h) else 0))
~~~

### 2133. usefB_nonneg

Source: proofs/UMUSEF1.lean:120 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_nonneg (n : ℕ) (a : ℝ) (j : ℕ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : 0 ≤ usefB n a j
~~~

### 2134. usefB_step

Source: proofs/UMUSEF1.lean:123 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_step (n : ℕ) (a : ℝ) (g : ℕ → ℝ) : ∑ j ∈ range (n + 1 + 1), usefB (n + 1) a j * g j = (1 - a) * ∑ j ∈ range (n + 1), usefB n a j * g j + a * ∑ j ∈ range (n + 1), usefB n a j * g (j + 1)
~~~

### 2135. usefB_m0

Source: proofs/UMUSEF1.lean:154 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_m0 (a : ℝ) : ∀ n : ℕ, ∑ j ∈ range (n + 1), usefB n a j = 1
~~~

### 2136. usefB_m1

Source: proofs/UMUSEF1.lean:164 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_m1 (a : ℝ) : ∀ n : ℕ, ∑ j ∈ range (n + 1), usefB n a j * (j : ℝ) = n * a
~~~

### 2137. usefB_m2

Source: proofs/UMUSEF1.lean:181 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_m2 (a : ℝ) : ∀ n : ℕ, ∑ j ∈ range (n + 1), usefB n a j * (j : ℝ) ^ 2 = n * a * (1 - a) + (n * a) ^ 2
~~~

### 2138. usefB_var

Source: proofs/UMUSEF1.lean:200 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_var (a c : ℝ) (n : ℕ) : ∑ j ∈ range (n + 1), usefB n a j * ((j : ℝ) - c) ^ 2 = n * a * (1 - a) + (n * a - c) ^ 2
~~~

### 2139. usefB_ext

Source: proofs/UMUSEF1.lean:210 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_ext (n K : ℕ) (a : ℝ) (g : ℕ → ℝ) (hK : n + 1 ≤ K) : ∑ j ∈ range K, usefB n a j * g j = ∑ j ∈ range (n + 1), usefB n a j * g j
~~~

### 2140. usef_cant_alg

Source: proofs/UMUSEF1.lean:220 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_cant_alg (d σ W : ℝ) (hd : 0 < d) (hσ : 0 ≤ σ) (hW : 0 ≤ W) (h : ∀ t, 0 ≤ t → (d + t) ^ 2 * W ≤ σ + t ^ 2) : d ^ 2 * W ≤ σ * (1 - W)
~~~

### 2141. usef_lower

Source: proofs/UMUSEF1.lean:246 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_lower (n s : ℕ) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : (max 0 ((n : ℝ) * a - s)) ^ 2 * binCDF n s a ≤ n * a * (1 - a) * (1 - binCDF n s a)
~~~

### 2142. usef_upper

Source: proofs/UMUSEF1.lean:284 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_upper (n s : ℕ) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : (max 0 ((s : ℝ) + 1 - n * a)) ^ 2 * (1 - binCDF n s a) ≤ n * a * (1 - a) * binCDF n s a
~~~

### 2143. usef_cat_r

Source: proofs/UMUSEF1.lean:337 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_cat_r {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r r' : ℝ) : ∀ n u h, cat Bad M φ π r 0 n u h = cat Bad M φ π r' 0 n u h
~~~

### 2144. claim

Source: proofs/UMUSEF1.lean:349 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMUSEF1.Claim
~~~

### 2145. wM_k

Source: proofs/UMUSEF1.lean:486 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wM_k : IsKernel wM
~~~

### 2146. wPH_d

Source: proofs/UMUSEF1.lean:494 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wPH_d : IsDist wPH
~~~

### 2147. w_supp

Source: proofs/UMUSEF1.lean:518 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_supp : ∀ x, wμ x ≠ 0 → ¬ x = true
~~~

### 2148. w_miss

Source: proofs/UMUSEF1.lean:524 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_miss : missRate wM wPH wφ = 9 / 40
~~~

### 2149. w_flag

Source: proofs/UMUSEF1.lean:528 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_flag : flagRate wM wμ wφ = 13 / 40
~~~

### 2150. w_hs

Source: proofs/UMUSEF1.lean:532 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_hs : hs 0 (push wM wμ) (push wM wPH) = 1 / 2
~~~

### 2151. witness

Source: proofs/UMUSEF1.lean:536 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMUSEF1.Witness
~~~

## Reviewer obligations

Check fully elaborated Lean goals and quantified premises; inspect what Bad, observations, harm, authority and budgets mean; review model-to-runtime correspondence independently.
