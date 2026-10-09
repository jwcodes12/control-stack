# All Lean statements — source-normalized review catalog

Every indexed theorem and lemma is listed with its source statement, registry metadata and source location; no proof bodies. This is NOT kernel-elaborated normal form: inherited section variables, typeclasses, namespace elaboration, coercions and definitions can hide important premises. Run Lean #print and #print axioms for authoritative statements. No deployment assurance is implied.

Indexed declarations: 875; UNKNOWN adversary: 821; SOURCE_ONLY: 855.

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

Source: ControlStack/AuditDispatch.lean:79 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem trace_safe (s : St) (ops : List Op) (h : Inv s) : Inv (run s ops) ∧ s.audits <+: (run s ops).audits
~~~

### 49. app_cannot_effect

Source: ControlStack/AuditDispatch.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

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

## ControlStack/Core/Gate.lean

### 68. System.run_nil

Source: ControlStack/Core/Gate.lean:41 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem System.run_nil {St Op Eff : Type} (G : System St Op Eff) (s : St) : G.run s [] = s
~~~

### 69. System.run_cons

Source: ControlStack/Core/Gate.lean:43 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem System.run_cons {St Op Eff : Type} (G : System St Op Eff) (s : St) (o : Op) (ops : List Op) : G.run s (o :: ops) = G.run (G.step s o) ops
~~~

### 70. Spec.trace_safe

Source: ControlStack/Core/Gate.lean:55 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem Spec.trace_safe {St Op Eff : Type} {G : System St Op Eff} (S : Spec G) (s : St) (ops : List Op) (h : S.Inv s) : S.Inv (G.run s ops) ∧ G.effects s <+: G.effects (G.run s ops) ∧ ∀ e ∈ G.effects (G.run s ops), S.ok (G.run s ops) e
~~~

### 71. NoAgentEffects.agent_trace_inert

Source: ControlStack/Core/Gate.lean:70 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem NoAgentEffects.agent_trace_inert {St Op Eff : Type} {G : System St Op Eff} {agent : Op → Prop} (H : NoAgentEffects G agent) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, agent o) : G.effects (G.run s ops) = G.effects s
~~~

### 72. halt_absorbing

Source: ControlStack/Core/Gate.lean:97 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem halt_absorbing {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List (HOp Op)) : (withHalt G).run (s, true) ops = (s, true)
~~~

### 73. halt_freezes

Source: ControlStack/Core/Gate.lean:104 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List (HOp Op)) : (withHalt G).effects ((withHalt G).run (s, false) (.halt :: ops)) = G.effects s
~~~

## ControlStack/Core/Leakage.lean

### 74. transfer

Source: ControlStack/Core/Leakage.lean:54 | Family: F2 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem transfer {X T A : Type} [Fintype X] [Fintype T] [Fintype A] (p : X → ℝ) (lik : X → T → ℝ) (c : T → ℝ) (δ : T → A → ℝ) (u : X → A → ℝ) (b : ℝ) (hp : ∀ x, 0 ≤ p x) (hc : ∀ x t, lik x t ≤ c t) (hc0 : ∀ t, 0 ≤ c t) (hδ : ∀ t, IsDist (δ t)) (hu : ∀ x a, 0 ≤ u x a) (hb : ∀ a, ∑ x, p x * u x a ≤ b) : ∑ x, p x * ∑ t, lik x t * ∑ a, δ t a * u x a ≤ (∑ t, c t) * b
~~~

### 75. covert_from_transfer

Source: ControlStack/Core/Leakage.lean:84 | Family: F2 | Adversary: NON_ADAPTIVE | Status: SOURCE_ONLY

~~~lean
theorem covert_from_transfer {M V : Type} [Fintype M] [Fintype V] [DecidableEq M] [Nonempty M] (enc : M → V → ℝ) (dec : V → M → ℝ) (henc : ∀ m, IsDist (enc m)) (hdec : ∀ v, IsDist (dec v)) : ∑ m, (Fintype.card M : ℝ)⁻¹ * ∑ v, enc m v * ∑ a, dec v a * (if a = m then 1 else 0) ≤ (Fintype.card V : ℝ) * (Fintype.card M : ℝ)⁻¹
~~~

### 76. cval_nonneg

Source: ControlStack/Core/Leakage.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_nonneg (c : List O → O → ℝ) (B : List O → ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hB : ∀ g, 0 ≤ B g) : ∀ n g, 0 ≤ cval c B n g
~~~

### 77. cval_mono

Source: ControlStack/Core/Leakage.lean:125 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_mono (c : List O → O → ℝ) (B B' : List O → ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hBB : ∀ g, B g ≤ B' g) : ∀ n g, cval c B n g ≤ cval c B' n g
~~~

### 78. cval_wsum

Source: ControlStack/Core/Leakage.lean:131 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_wsum {X : Type} [Fintype X] (c : List O → O → ℝ) (p : X → ℝ) (B : X → List O → ℝ) : ∀ n g, ∑ x, p x * cval c (B x) n g = cval c (fun t => ∑ x, p x * B x t) n g
~~~

### 79. cval_smul

Source: ControlStack/Core/Leakage.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_smul (c : List O → O → ℝ) (b : ℝ) (B : List O → ℝ) : ∀ n g, cval c (fun t => b * B t) n g = b * cval c B n g
~~~

### 80. val_le_cval

Source: ControlStack/Core/Leakage.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_le_cval (K : List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (pay : List O → ℝ) (hK0 : ∀ h z, 0 ≤ K h z) (hdom : Dominated K c) (hc0 : ∀ g o, 0 ≤ c g o) (hpay : ∀ g, 0 ≤ pay g) : ∀ n h, val K pay n h ≤ cval c pay n (h.map Prod.snd)
~~~

### 81. seq_transfer

Source: ControlStack/Core/Leakage.lean:178 | Family: F8 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem seq_transfer {X : Type} [Fintype X] (p : X → ℝ) (K : X → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (pay : X → List O → ℝ) (B : List O → ℝ) (n : ℕ) (hp : ∀ x, 0 ≤ p x) (hK0 : ∀ x h z, 0 ≤ K x h z) (hdom : ∀ x, Dominated (K x) c) (hc0 : ∀ g o, 0 ≤ c g o) (hpay : ∀ x g, 0 ≤ pay x g) (hB : ∀ t, ∑ x, p x * pay x t ≤ B t) : ∑ x, p x * val (K x) (pay x) n [] ≤ cval c B n []
~~~

### 82. seq_transfer_const

Source: ControlStack/Core/Leakage.lean:192 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seq_transfer_const {X : Type} [Fintype X] (p : X → ℝ) (K : X → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (pay : X → List O → ℝ) (b : ℝ) (n : ℕ) (hp : ∀ x, 0 ≤ p x) (hK0 : ∀ x h z, 0 ≤ K x h z) (hdom : ∀ x, Dominated (K x) c) (hc0 : ∀ g o, 0 ≤ c g o) (hpay : ∀ x g, 0 ≤ pay x g) (hb : ∀ t, ∑ x, p x * pay x t ≤ b) : ∑ x, p x * val (K x) (pay x) n [] ≤ b * mass c n []
~~~

### 83. mass_le_prod

Source: ControlStack/Core/Leakage.lean:204 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mass_le_prod (c : List O → O → ℝ) (Lr : ℕ → ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hLr0 : ∀ i, 0 ≤ Lr i) (hL : ∀ g, ∑ o, c g o ≤ Lr g.length) : ∀ n g, mass c n g ≤ ∏ j ∈ range n, Lr (g.length + j)
~~~

### 84. mass_le_pow

Source: ControlStack/Core/Leakage.lean:224 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mass_le_pow (c : List O → O → ℝ) (L : ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hL0 : 0 ≤ L) (hL : ∀ g, ∑ o, c g o ≤ L) (n : ℕ) (g : List O) : mass c n g ≤ L ^ n
~~~

### 85. mass_const

Source: ControlStack/Core/Leakage.lean:229 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mass_const (w : O → ℝ) : ∀ n g, mass (fun _ o => w o) n g = (∑ o, w o) ^ n
~~~

### 86. covert_seq

Source: ControlStack/Core/Leakage.lean:248 | Family: F2 | Adversary: SHARED_SEED | Status: SOURCE_ONLY

~~~lean
theorem covert_seq {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (dec : Ω → List O → M → ℝ) (n : ℕ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c) (hc0 : ∀ g o, 0 ≤ c g o) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ mass c n [] / (Fintype.card M : ℝ)
~~~

### 87. covert_seq_seed

Source: ControlStack/Core/Leakage.lean:270 | Family: F2 | Adversary: SHARED_SEED | Status: SOURCE_ONLY

~~~lean
theorem covert_seq_seed {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : Ω → List O → O → ℝ) (dec : Ω → List O → M → ℝ) (n : ℕ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) (c ω)) (hc0 : ∀ ω g o, 0 ≤ c ω g o) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ (∑ ω, ρ ω * mass (c ω) n []) / (Fintype.card M : ℝ)
~~~

### 88. episode_dom

Source: ControlStack/Core/Leakage.lean:293 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem episode_dom {V S Z : Type} [Fintype V] [Fintype S] [Fintype Z] (enc : List (S × (V × Z)) → V × S → ℝ) (W : List (S × (V × Z)) → S → Z → ℝ) (cs : List (V × Z) → Z → ℝ) (henc : ∀ h, IsDist (enc h)) (hcs0 : ∀ g z, 0 ≤ cs g z) (hW : ∀ h s z, W h s z ≤ cs (h.map Prod.snd) z) : Dominated (fun h (y : S × (V × Z)) => enc h (y.2.1, y.1) * W h y.1 y.2.2) (fun g o => cs g o.2)
~~~

### 89. episode_mass

Source: ControlStack/Core/Leakage.lean:314 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem episode_mass {V Z : Type} [Fintype V] [Fintype Z] (cs : List (V × Z) → Z → ℝ) (g : List (V × Z)) : ∑ o : V × Z, cs g o.2 = (Fintype.card V : ℝ) * ∑ z, cs g z
~~~

### 90. sc01_adaptive_target

Source: ControlStack/Core/Leakage.lean:322 | Family: F2 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem sc01_adaptive_target {Ω Y Z : Type} [Fintype Ω] [Fintype Y] [Fintype Z] (ρ : Ω → ℝ) (K : Ω → Fin (2 ^ 32) → List (Y × (Option (Fin 8) × Z)) → Y × (Option (Fin 8) × Z) → ℝ) (cs : List (Option (Fin 8) × Z) → Z → ℝ) (lam : ℕ → ℝ) (dec : Ω → List (Option (Fin 8) × Z) → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) (fun g o => cs g o.2)) (hcs0 : ∀ g z, 0 ≤ cs g z) (hlam : ∀ g, ∑ z, cs g z ≤ lam g.length) (hlam0 : ∀ i, 0 ≤ lam i) (hprod : ∏ i ∈ range 5, lam i ≤ 65536 / 59049) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card (Fin (2 ^ 32)) : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) 5 []) ≤ (2 : ℝ)⁻¹ ^ 16
~~~

### 91. covert_side_bound

Source: ControlStack/Core/Leakage.lean:348 | Family: F2 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem covert_side_bound {Ω M V Y Z : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype V] [Fintype Y] [Fintype Z] (ρ : Ω → ℝ) (K : Ω → M → List (Y × (V × Z)) → Y × (V × Z) → ℝ) (cs : List (V × Z) → Z → ℝ) (lam : ℕ → ℝ) (dec : Ω → List (V × Z) → M → ℝ) (n : ℕ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) (fun g o => cs g o.2)) (hcs0 : ∀ g z, 0 ≤ cs g z) (hlam : ∀ g, ∑ z, cs g z ≤ lam g.length) (hlam0 : ∀ i, 0 ≤ lam i) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ (Fintype.card V : ℝ) ^ n * (∏ i ∈ range n, lam i) / (Fintype.card M : ℝ)
~~~

### 92. cval_live

Source: ControlStack/Core/Leakage.lean:381 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_live (st : O → Bool) (c : List O → O → ℝ) : ∀ n g, cval c (liveInd st) n g = liveInd st g * mass (dropStop st c) n g
~~~

### 93. val_congr_on

Source: ControlStack/Core/Leakage.lean:432 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_congr_on {Y O : Type} [Fintype Y] [Fintype O] (K : List (Y × O) → Y × O → ℝ) (P : List O → Prop) (pay pay' : List O → ℝ) (hP : ∀ h y o, K h (y, o) ≠ 0 → P (h.map Prod.snd) → P (h.map Prod.snd ++ [o])) (hagree : ∀ t, P t → pay t = pay' t) : ∀ n h, P (h.map Prod.snd) → val K pay n h = val K pay' n h
~~~

### 94. consistent_append

Source: ControlStack/Core/Leakage.lean:449 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem consistent_append (S : Finset (Fin N)) (g : List (AOut Z)) (o : AOut Z) (hg : Consistent S g) (ho : o.2.2 = (o.1 && decide (memN S g.length))) : Consistent S (g ++ [o])
~~~

### 95. surv_live

Source: ControlStack/Core/Leakage.lean:462 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_live (k : ℕ) (S : Finset (Fin N)) (t : List (AOut Z)) (ht : Consistent S t) : survInd k S t = survInd k S t * liveInd caughtFlag t
~~~

### 96. blind_audit

Source: ControlStack/Core/Leakage.lean:491 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem blind_audit (k B : ℕ) (hB : B ≤ N) (t : List (AOut Z)) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * survInd k S t ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

### 97. liveInd_nonneg

Source: ControlStack/Core/Leakage.lean:511 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem liveInd_nonneg {O : Type} (st : O → Bool) (t : List O) : 0 ≤ liveInd st t
~~~

### 98. survInd_nonneg

Source: ControlStack/Core/Leakage.lean:515 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survInd_nonneg (k : ℕ) (S : Finset (Fin N)) (t : List (AOut Z)) : 0 ≤ survInd k S t
~~~

### 99. audit_leak_bound_all

Source: ControlStack/Core/Leakage.lean:525 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem audit_leak_bound_all (k B : ℕ) (hB : B ≤ N) (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (hK0 : ∀ S h z, 0 ≤ K S h z) (hK1 : ∀ S h, ∑ z, K S h z ≤ 1) (hcons : ∀ S h y o, K S h (y, o) ≠ 0 → o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length))) (hdom : ∀ S h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o) (hcl0 : ∀ g o, 0 ≤ cl g o) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (K S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * mass (dropStop caughtFlag cl) N []
~~~

### 100. audit_leak_bound

Source: ControlStack/Core/Leakage.lean:579 | Family: F6 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem audit_leak_bound (k B : ℕ) (hB : B ≤ N) (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1) (hcons : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h y o, K S h (y, o) ≠ 0 → o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length))) (hdom : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o) (hcl0 : ∀ g o, 0 ≤ cl g o) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (K S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * mass (dropStop caughtFlag cl) N []
~~~

### 101. audit_leak_prod

Source: ControlStack/Core/Leakage.lean:616 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem audit_leak_prod (k B : ℕ) (hB : B ≤ N) (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (Lr : ℕ → ℝ) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1) (hcons : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h y o, K S h (y, o) ≠ 0 → o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length))) (hdom : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o) (hcl0 : ∀ g o, 0 ≤ cl g o) (hLr0 : ∀ i, 0 ≤ Lr i) (hL : ∀ g, ∑ o, dropStop caughtFlag cl g o ≤ Lr g.length) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (K S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * ∏ i ∈ range N, Lr i
~~~

### 102. audit_adaptive_hidden

Source: ControlStack/Core/Leakage.lean:644 | Family: F6 | Adversary: ADAPTIVE_FEEDBACK | Status: SOURCE_ONLY

~~~lean
theorem audit_adaptive_hidden (k B : ℕ) (hB : B ≤ N) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (hiddenK σ S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

## ControlStack/CovertChannel.lean

### 103. per_seed_le

Source: ControlStack/CovertChannel.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem per_seed_le {M V : Type} [Fintype M] [Fintype V] (enc : M → V → ℝ) (dec : V → M → ℝ) (henc : ∀ m, IsDist (enc m)) (hdec : ∀ v, IsDist (dec v)) : ∑ m, ∑ v, enc m v * dec v m ≤ (Fintype.card V : ℝ)
~~~

### 104. covert_bound

Source: ControlStack/CovertChannel.lean:48 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem covert_bound {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V] [Nonempty M] (ρ : Ω → ℝ) (enc : Ω → M → V → ℝ) (dec : Ω → V → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (Fintype.card V : ℝ) / (Fintype.card M : ℝ)
~~~

### 105. covert_bound_schema

Source: ControlStack/CovertChannel.lean:63 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem covert_bound_schema {Ω M S : Type} [Fintype Ω] [Fintype M] [Fintype S] [Nonempty M] [DecidableEq S] (n : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → (Fin n → S) → ℝ) (dec : Ω → (Fin n → S) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (Fintype.card S : ℝ) ^ n / (Fintype.card M : ℝ)
~~~

### 106. attain_injective

Source: ControlStack/CovertChannel.lean:72 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attain_injective {M V : Type} [Fintype M] [Fintype V] [DecidableEq M] [DecidableEq V] [Nonempty M] (code : M → V) (decode : V → M) (hinv : ∀ m, decode (code m) = m) : successProb (Ω
~~~

### 107. design_point

Source: ControlStack/CovertChannel.lean:89 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem design_point {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → (Fin 16 → Bool) → ℝ) (dec : Ω → (Fin 16 → Bool) → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ 1 / 2 ^ 16
~~~

### 108. attain_embedding

Source: ControlStack/CovertChannel.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attain_embedding {M V : Type} [Fintype M] [Fintype V] [DecidableEq M] [DecidableEq V] [Nonempty M] [Nonempty V] (e : V → M) (he : Function.Injective e) : successProb (Ω
~~~

### 109. covert_bound_lifetime

Source: ControlStack/CovertChannel.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem covert_bound_lifetime {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] {E : ℕ} (V : Fin E → Type) [∀ e, Fintype (V e)] [∀ e, DecidableEq (V e)] (ρ : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ) (dec : Ω → ((e : Fin E) → V e) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (∏ e, (Fintype.card (V e) : ℝ)) / (Fintype.card M : ℝ)
~~~

## ControlStack/CovertNoGo.lean

### 110. controllable_leak

Source: ControlStack/CovertNoGo.lean:22 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem controllable_leak {M T V : Type} [Fintype M] [Fintype T] [DecidableEq M] [DecidableEq T] [DecidableEq V] (N : ℕ) (hN : 0 < N) (view : T → V) (realize : Fin N → T) (hdist : Function.Injective (fun i => view (realize i))) (e : Fin N → M) (he : Function.Injective e) : ∃ (enc : M → T → ℝ) (dec : V → M → ℝ), (∀ m, IsDist (enc m)) ∧ (∀ v, IsDist (dec v)) ∧ successView view enc dec = (N : ℝ) / (Fintype.card M : ℝ)
~~~

### 111. one_bit_coordinates

Source: ControlStack/CovertNoGo.lean:73 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem one_bit_coordinates {T V : Type} [Fintype T] [DecidableEq T] [DecidableEq V] (view : T → V) (t0 t1 : T) (h : view t0 ≠ view t1) : ∃ (enc : Bool → T → ℝ) (dec : V → Bool → ℝ), (∀ m, IsDist (enc m)) ∧ (∀ v, IsDist (dec v)) ∧ successView view enc dec = 1
~~~

## ControlStack/DeferGame.lean

### 112. deployV_step

Source: ControlStack/DeferGame.lean:58 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployV_step {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) : Pr[= true | deployV Bad π M D A Halt Svc b (n+1) u h] = ∑ x, Pr[= x | π h] * ∑ z, Pr[= z | M x] * (Pr[= true | D z] * Pr[= true | (if Bad x then pure true else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,true)]) : ProbComp Bool)] + Pr[= false | D z] * (if u < b then Pr[= true | (if Bad x then (fun caught => !caught) <$> A h x z else deployV Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)]) : ProbComp Bool)] else Pr[= true | (if Bad x then do let halt ← Halt h x z if halt then pure false else do let caught ← Svc h x z if caught then pure false else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) else do let halt ← Halt h x z if halt then pure false else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) : ProbComp Bool)]))
~~~

### 113. halt_then_prob

Source: ControlStack/DeferGame.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_then_prob (H K : ProbComp Bool) : Pr[= true | do let halt ← H; if halt then pure false else K] = Pr[= false | H] * Pr[= true | K]
~~~

### 114. halt_then_real

Source: ControlStack/DeferGame.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_then_real (H K : ProbComp Bool) : (Pr[= true | do let halt ← H; if halt then pure false else K]).toReal = (1 - (Pr[= true | H]).toReal) * (Pr[= true | K]).toReal
~~~

### 115. halt_service_continue_real

Source: ControlStack/DeferGame.lean:101 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_service_continue_real (H S C : ProbComp Bool) : (Pr[= true | do let halt ← H if halt then pure false else do let caught ← S if caught then pure false else C]).toReal = (1 - (Pr[= true | H]).toReal) * (1 - (Pr[= true | S]).toReal) * (Pr[= true | C]).toReal
~~~

### 116. calibrated_exhausted_benign_real

Source: ControlStack/DeferGame.lean:112 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem calibrated_exhausted_benign_real (H C : ProbComp Bool) (η : ℝ) (hH : (Pr[= true | H]).toReal = η) : (Pr[= true | do let halt ← H; if halt then pure false else C]).toReal = (1 - η) * (Pr[= true | C]).toReal
~~~

### 117. calibrated_exhausted_bad_real

Source: ControlStack/DeferGame.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem calibrated_exhausted_bad_real (H S C : ProbComp Bool) (η a c : ℝ) (hH : (Pr[= true | H]).toReal = η) (hS : (Pr[= true | S]).toReal = a) (hC : (Pr[= true | C]).toReal = c) : (Pr[= true | do let halt ← H if halt then pure false else do let caught ← S if caught then pure false else C]).toReal = (1 - η) * (1 - a) * c
~~~

### 118. calibrated_audit_escape_real

Source: ControlStack/DeferGame.lean:129 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem calibrated_audit_escape_real (A : ProbComp Bool) (r : ℝ) (hA : (Pr[= true | A]).toReal = r) : (Pr[= true | (fun caught => !caught) <$> A]).toReal = 1 - r
~~~

### 119. exhausted_benign_probability

Source: ControlStack/DeferGame.lean:159 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exhausted_benign_probability (H C : ProbComp Bool) : Pr[= true | do let halt ← H if halt then pure false else C] = Pr[= false | H] * Pr[= true | C]
~~~

### 120. exhausted_bad_then_probability

Source: ControlStack/DeferGame.lean:169 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exhausted_bad_then_probability (H S C : ProbComp Bool) : Pr[= true | do let halt ← H if halt then pure false else do let caught ← S if caught then pure false else C] = Pr[= false | H] * Pr[= false | S] * Pr[= true | C]
~~~

### 121. deployV_eq_catVE

Source: ControlStack/DeferGame.lean:200 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployV_eq_catVE {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) : ∀ n u h, Pr[= true | deployV Bad π M D A Halt Svc b n u h] = catVE Bad π M D A Halt Svc b n u h
~~~

### 122. catVE_ne_top

Source: ControlStack/DeferGame.lean:219 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_ne_top {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) : catVE Bad π M D A Halt Svc b n u h ≠ ⊤
~~~

### 123. catVE_transition_ne_top

Source: ControlStack/DeferGame.lean:229 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_transition_ne_top {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) (x : X) (z : Z) : (Pr[= true | D z] * (if Bad x then 1 else catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,true)])) + Pr[= false | D z] * (if u < b then (if Bad x then Pr[= false | A h x z] else catVE Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)])) else if Bad x then Pr[= false | Halt h x z] * Pr[= false | Svc h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) else Pr[= false | Halt h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]))) ≠ ⊤
~~~

### 124. catVE_inner_ne_top

Source: ControlStack/DeferGame.lean:274 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_inner_ne_top {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) (x : X) : (∑ z, Pr[= z | M x] * (Pr[= true | D z] * (if Bad x then 1 else catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,true)])) + Pr[= false | D z] * (if u < b then (if Bad x then Pr[= false | A h x z] else catVE Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)])) else if Bad x then Pr[= false | Halt h x z] * Pr[= false | Svc h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) else Pr[= false | Halt h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)])))) ≠ ⊤
~~~

### 125. catVE_toReal_eq_catV

Source: ControlStack/DeferGame.lean:296 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_toReal_eq_catV {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) (r η : ℝ) (a : Service X Z) (hA : ∀ h x z, Bad x → (Pr[= true | A h x z]).toReal = r) (hH : ∀ h x z, (Pr[= true | Halt h x z]).toReal = η) (hS : ∀ h x z, Bad x → (Pr[= true | Svc h x z]).toReal = a h x z) : ∀ n u h, (catVE Bad π M D A Halt Svc b n u h).toReal = catV Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D z]).toReal) (fun h x => (Pr[= x | π h]).toReal) r η a b n u h
~~~

### 126. defer_bridge

Source: ControlStack/DeferGame.lean:330 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem defer_bridge : DeferBridgeClaim
~~~

## ControlStack/DeferMono.lean

### 127. catVE_toReal_le_catV

Source: ControlStack/DeferMono.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_toReal_le_catV {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) (r η : ℝ) (a : Service X Z) (hA : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) (hH : ∀ h x z, η ≤ (Pr[= true | Halt h x z]).toReal) (hS : ∀ h x z, Bad x → a h x z ≤ (Pr[= true | Svc h x z]).toReal) : ∀ n u h, (catVE Bad π M D A Halt Svc b n u h).toReal ≤ catV Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D z]).toReal) (fun h x => (Pr[= x | π h]).toReal) r η a b n u h
~~~

### 128. defer_mono

Source: ControlStack/DeferMono.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem defer_mono : DeferMonoClaim
~~~

## ControlStack/EgressGate.lean

### 129. lookup_pinned

Source: ControlStack/EgressGate.lean:26 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lookup_pinned (p : Policy) (key : String) (peer : Peer) (h : lookup p key = some peer) : peer ∈ p.map Rule.peer
~~~

### 130. direct_no_effect

Source: ControlStack/EgressGate.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem direct_no_effect (p : Policy) (s : State) (peer : Peer) (h : Invariant p s) : step p s (.directAttempt peer) = s
~~~

### 131. step_safe

Source: ControlStack/EgressGate.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_safe (p : Policy) (s : State) (a : Action) (h : Invariant p s) : Invariant p (step p s a)
~~~

### 132. trace_safe

Source: ControlStack/EgressGate.lean:126 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem trace_safe (p : Policy) (s : State) (actions : List Action) (h : Invariant p s) : Invariant p (run p s actions)
~~~

### 133. failed_launch

Source: ControlStack/EgressGate.lean:132 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem failed_launch (p : Policy) (s : State) (t : Topology) (h : safe t = false) : (step p s (.launch t)).active = false
~~~

### 134. crash_closed

Source: ControlStack/EgressGate.lean:135 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem crash_closed (p : Policy) (s : State) (key : String) : (step p (step p s .crashGateway) (.request key)).attempts = s.attempts
~~~

## ControlStack/Families/F4/GateClients.lean

### 135. dispatch_effects_prefix

Source: ControlStack/Families/F4/GateClients.lean:44 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dispatch_effects_prefix (s : AuditDispatch.St) (o : AuditDispatch.Op) : s.effects <+: (AuditDispatch.step s o).effects
~~~

### 136. dispatch_no_agent_effects

Source: ControlStack/Families/F4/GateClients.lean:55 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dispatch_no_agent_effects : NoAgentEffects dispatchSys (fun o => ∀ id, o ≠ .dispatch id)
~~~

### 137. auditGate_prefix

Source: ControlStack/Families/F4/GateClients.lean:65 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem auditGate_prefix (s : AuditGate.St) (o : AuditGate.Op) : s.executions <+: (AuditGate.step s o).executions
~~~

### 138. egress_prefix

Source: ControlStack/Families/F4/GateClients.lean:82 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem egress_prefix (p : EgressGate.Policy) (s : EgressGate.State) (a : EgressGate.Action) : s.attempts <+: (EgressGate.step p s a).attempts
~~~

### 139. step_inv

Source: ControlStack/Families/F4/GateClients.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (hash : C → H) (s : St C H) (o : Op C H) (h : Inv hash s) : Inv hash (step hash s o)
~~~

### 140. prefix_step

Source: ControlStack/Families/F4/GateClients.lean:169 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prefix_step (hash : C → H) (s : St C H) (o : Op C H) : s.deployed <+: (step hash s o).deployed
~~~

### 141. deployed_reviewed

Source: ControlStack/Families/F4/GateClients.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployed_reviewed (hash : C → H) (ops : List (Op C H)) : ∀ c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).deployed, hash c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).reviewed
~~~

### 142. deployed_is_reviewed

Source: ControlStack/Families/F4/GateClients.lean:195 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem deployed_is_reviewed (hash : C → H) (ops : List (Op C H)) (hinj : Set.InjOn hash {c | c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).store ∨ c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).reviewedContent}) : ∀ c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).deployed, c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).reviewedContent
~~~

### 143. collision_breaks

Source: ControlStack/Families/F4/GateClients.lean:210 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem collision_breaks : let s
~~~

### 144. agent_cannot_review

Source: ControlStack/Families/F4/GateClients.lean:222 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_cannot_review (hash : C → H) (s : St C H) (o : Op C H) (ho : agentOp o) : (step hash s o).reviewed = s.reviewed ∧ (step hash s o).reviewedContent = s.reviewedContent
~~~

### 145. step_inv

Source: ControlStack/Families/F4/GateClients.lean:273 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (s : St P) (o : Op P) (h : Inv s) : Inv (step s o)
~~~

### 146. prefix_step

Source: ControlStack/Families/F4/GateClients.lean:292 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prefix_step (s : St P) (o : Op P) : s.executed <+: (step s o).executed
~~~

### 147. approval_safe

Source: ControlStack/Families/F4/GateClients.lean:307 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem approval_safe (ops : List (Op P)) : let s
~~~

### 148. replay_without_nonce

Source: ControlStack/Families/F4/GateClients.lean:322 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem replay_without_nonce : let t : Tx Unit
~~~

### 149. agent_cannot_approve

Source: ControlStack/Families/F4/GateClients.lean:334 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_cannot_approve (s : St P) (o : Op P) (ho : agentOp o) : (step s o).approvals = s.approvals
~~~

### 150. replay_if_nonces_lost

Source: ControlStack/Families/F4/GateClients.lean:341 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem replay_if_nonces_lost : let t : Tx Unit
~~~

## ControlStack/Families/F5/Lease.lean

### 151. spent_append

Source: ControlStack/Families/F5/Lease.lean:107 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem spent_append (work : List (ℕ × ℕ × ℕ)) (e : ℕ × ℕ × ℕ) (id : ℕ) : spent (work ++ [e]) id = spent work id + (if e.1 = id then e.2.1 else 0)
~~~

### 152. total_append

Source: ControlStack/Families/F5/Lease.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem total_append (work : List (ℕ × ℕ × ℕ)) (e : ℕ × ℕ × ℕ) : total (work ++ [e]) = total work + e.2.1
~~~

### 153. spent_eq_zero_of_absent

Source: ControlStack/Families/F5/Lease.lean:114 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem spent_eq_zero_of_absent (work : List (ℕ × ℕ × ℕ)) (id : ℕ) (h : ∀ e ∈ work, e.1 ≠ id) : spent work id = 0
~~~

### 154. step_inv

Source: ControlStack/Families/F5/Lease.lean:120 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (cap : ℕ) (s : St) (o : Op) (h : Inv cap s) : Inv cap (step cap s o)
~~~

### 155. prefix_step

Source: ControlStack/Families/F5/Lease.lean:180 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prefix_step (cap : ℕ) (s : St) (o : Op) : s.work <+: (step cap s o).work
~~~

### 156. lease_safe

Source: ControlStack/Families/F5/Lease.lean:204 | Family: F5 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem lease_safe (cap : ℕ) (ops : List Op) : let s
~~~

### 157. revoke_step

Source: ControlStack/Families/F5/Lease.lean:213 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem revoke_step (cap : ℕ) (s : St) (o : Op) (id : ℕ) (hr : id ∈ s.revoked) : id ∈ (step cap s o).revoked ∧ ∃ δ, (step cap s o).work = s.work ++ δ ∧ ∀ e ∈ δ, e.1 ≠ id
~~~

### 158. revoke_absorbing

Source: ControlStack/Families/F5/Lease.lean:238 | Family: F5 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem revoke_absorbing (cap : ℕ) (s : St) (ops : List Op) (id : ℕ) (hr : id ∈ s.revoked) : ∃ δ, ((sys cap).run s ops).work = s.work ++ δ ∧ ∀ e ∈ δ, e.1 ≠ id
~~~

### 159. length_le_sum

Source: ControlStack/Families/F5/Lease.lean:252 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem length_le_sum (L : List (ℕ × ℕ × ℕ)) (h : ∀ e ∈ L, 1 ≤ e.2.1) : L.length ≤ (L.map (fun e => e.2.1)).sum
~~~

### 160. work_count_le

Source: ControlStack/Families/F5/Lease.lean:264 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem work_count_le (cap : ℕ) (ops : List Op) : let s
~~~

### 161. agent_cannot_issue

Source: ControlStack/Families/F5/Lease.lean:282 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_cannot_issue (cap : ℕ) (s : St) (o : Op) (ho : agentOp o) : (step cap s o).leases = s.leases ∧ (step cap s o).revoked = s.revoked
~~~

### 162. revoked_worker_stays_stopped

Source: ControlStack/Families/F5/Lease.lean:298 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem revoked_worker_stays_stopped : let ops
~~~

### 163. zero_cost_refused

Source: ControlStack/Families/F5/Lease.lean:304 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem zero_cost_refused : ([Op.issue ⟨0, 0, 100⟩ 1, .work 1 0, .work 1 0].foldl (step 100) init).work = []
~~~

### 164. fork_without_lease_accounting

Source: ControlStack/Families/F5/Lease.lean:328 | Family: F5 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem fork_without_lease_accounting : let ops
~~~

### 165. reissue_takes_effect

Source: ControlStack/Families/F5/Lease.lean:335 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reissue_takes_effect : let ops
~~~

## ControlStack/GateComposition.lean

### 166. shared_invariants

Source: ControlStack/GateComposition.lean:18 | Family: F8 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem shared_invariants {S A : Type} (P Q : S → Prop) (step : S → A → S) (s : S) (actions : List A) (hJoint : ∀ (x : S) (a : A), P x → Q x → P (step x a) ∧ Q (step x a)) (h : P s ∧ Q s) : P (run step s actions) ∧ Q (run step s actions)
~~~

### 167. confused_deputy_counterexample

Source: ControlStack/GateComposition.lean:45 | Family: F8 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem confused_deputy_counterexample : (unsafeDeputyStep { gateAApproved
~~~

## ControlStack/GatewayCore.lean

### 168. frozen

Source: ControlStack/GatewayCore.lean:72 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma frozen (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (v : View S slots) (h : st.snap = some v) (tr : List (Ev C R)) : runG valid st tr = st
~~~

### 169. close_freezes

Source: ControlStack/GatewayCore.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem close_freezes (valid : (c : Fin C) → R → Option (S c)) (pre post : List (Ev C R)) : finalView (runG valid (init (S
~~~

### 170. blanked_stays

Source: ControlStack/GatewayCore.lean:101 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma blanked_stays (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (hb : st.blanked = true) (hs : st.snap = none ∨ st.snap = some nullView) (tr : List (Ev C R)) : (runG valid st tr).blanked = true ∧ ((runG valid st tr).snap = none ∨ (runG valid st tr).snap = some nullView)
~~~

### 171. finalView_blanked

Source: ControlStack/GatewayCore.lean:144 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma finalView_blanked (st : GSt S slots) (hb : st.blanked = true) (hs : st.snap = none ∨ st.snap = some nullView) : finalView st = nullView
~~~

### 172. refusal_blanks

Source: ControlStack/GatewayCore.lean:152 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refusal_blanks (valid : (c : Fin C) → R → Option (S c)) (pre post : List (Ev C R)) (e : Ev C R) (hpre : (runG valid (init (S
~~~

### 173. other_blanks

Source: ControlStack/GatewayCore.lean:184 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem other_blanks (valid : (c : Fin C) → R → Option (S c)) (pre post : List (Ev C R)) (hpre : (runG valid (init (S
~~~

### 174. card_prefixes

Source: ControlStack/GatewayCore.lean:200 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem card_prefixes [∀ c, Fintype (S c)] [∀ c, DecidableEq (S c)] : Fintype.card (Prefixes S slots) = viewSpace slots (fun c => Fintype.card (S c))
~~~

### 175. viewOf_reachable

Source: ControlStack/GatewayCore.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma viewOf_reachable (st : GSt S slots) (h : ∀ c, (st.buf c).length ≤ slots c) : viewOf st ∈ Set.range (embedAll (S
~~~

### 176. gstep_inv

Source: ControlStack/GatewayCore.lean:217 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma gstep_inv (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (e : Ev C R) (h : Inv st) : Inv (gstep valid st e)
~~~

### 177. runG_inv

Source: ControlStack/GatewayCore.lean:247 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma runG_inv (valid : (c : Fin C) → R → Option (S c)) (tr : List (Ev C R)) (st : GSt S slots) (h : Inv st) : Inv (runG valid st tr)
~~~

### 178. view_reachable

Source: ControlStack/GatewayCore.lean:254 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem view_reachable (valid : (c : Fin C) → R → Option (S c)) (tr : List (Ev C R)) : finalView (runG valid (init (S
~~~

### 179. core_bound

Source: ControlStack/GatewayCore.lean:265 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem core_bound {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R] [∀ c, Fintype (S c)] [∀ c, DecidableEq (S c)] [Fintype (Ev C R)] (valid : (c : Fin C) → R → Option (S c)) (L : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ) (dec : Ω → View S slots → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : (∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ tr, enc ω m tr * dec ω (finalView (runG valid (init (S
~~~

### 180. sc01_episode_views

Source: ControlStack/GatewayCore.lean:297 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc01_episode_views : viewSpace (C
~~~

## ControlStack/GatewayModel.lean

### 181. blank_absorbing

Source: ControlStack/GatewayModel.lean:47 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem blank_absorbing {R S : Type} (valid : R → Option S) (slots : ℕ) (tr : List (Act R)) (st : St S) (h : st.blanked = true) : (tr.foldl (step valid slots) st).blanked = true
~~~

### 182. other_blanks

Source: ControlStack/GatewayModel.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem other_blanks {R S : Type} (valid : R → Option S) (slots : ℕ) (pre post : List (Act R)) : deliver slots (run valid slots (pre ++ Act.other :: post)) = fun _ => none
~~~

### 183. push_dist

Source: ControlStack/GatewayModel.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_dist {T V : Type} [Fintype T] [Fintype V] [DecidableEq V] (f : T → V) (p : T → ℝ) (hp : IsDist p) : IsDist (push f p)
~~~

### 184. gateway_bound

Source: ControlStack/GatewayModel.lean:84 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem gateway_bound {Ω M R S : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R] [Fintype S] [DecidableEq S] (valid : R → Option S) (slots L : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → (Fin L → Act R) → ℝ) (dec : Ω → (Fin slots → Option S) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : (∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ tr, enc ω m tr * dec ω (deliver slots (run valid slots (List.ofFn tr))) m)) ≤ ((Fintype.card S : ℝ) + 1) ^ slots / (Fintype.card M : ℝ)
~~~

### 185. buf_le

Source: ControlStack/GatewayModel.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem buf_le {R S : Type} (valid : R → Option S) (slots : ℕ) (tr : List (Act R)) (st : St S) (h : st.buf.length ≤ slots) : (tr.foldl (step valid slots) st).buf.length ≤ slots
~~~

### 186. deliver_eq_embed

Source: ControlStack/GatewayModel.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deliver_eq_embed {S : Type} (slots : ℕ) (st : St S) (h : st.buf.length ≤ slots) : deliver slots st = embedPrefix slots (toPrefix slots st h)
~~~

### 187. gateway_bound_reachable

Source: ControlStack/GatewayModel.lean:153 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gateway_bound_reachable {Ω M R S : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R] [Fintype S] [DecidableEq S] (valid : R → Option S) (slots L : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → (Fin L → Act R) → ℝ) (dec : Ω → (Fin slots → Option S) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : (∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ tr, enc ω m tr * dec ω (deliver slots (run valid slots (List.ofFn tr))) m)) ≤ (∑ j : Fin (slots + 1), (Fintype.card S : ℝ) ^ (j : ℕ)) / (Fintype.card M : ℝ)
~~~

## ControlStack/HaltLiveness.lean

### 188. run_append

Source: ControlStack/HaltLiveness.lean:18 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_append {St Op Eff : Type} (G : System St Op Eff) (s : St) (before after : List Op) : G.run s (before ++ after) = G.run (G.run s before) after
~~~

### 189. delivered_halt_absorbs

Source: ControlStack/HaltLiveness.lean:24 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem delivered_halt_absorbs {St Op Eff : Type} (G : System St Op Eff) (sh : St × Bool) (rest : List (HOp Op)) : (withHalt G).run sh (.halt :: rest) = (sh.1, true)
~~~

### 190. liveness_if_delivered

Source: ControlStack/HaltLiveness.lean:40 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem liveness_if_delivered {St Op Eff : Type} (G : System St Op Eff) (s : St) (n : Nat) (ops : List (HOp Op)) (h : DeliveredWithin n ops) : ((withHalt G).run (s, false) ops).2 = true
~~~

### 191. effects_frozen_after_delivered_halt

Source: ControlStack/HaltLiveness.lean:51 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem effects_frozen_after_delivered_halt {St Op Eff : Type} (G : System St Op Eff) (s : St) (before after : List (HOp Op)) : (withHalt G).effects ((withHalt G).run (s, false) (before ++ (.halt :: after))) = (withHalt G).effects ((withHalt G).run (s, false) before)
~~~

### 192. ordinary_operations_never_halt

Source: ControlStack/HaltLiveness.lean:62 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem ordinary_operations_never_halt {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List Op) : ((withHalt G).run (s, false) (ops.map HOp.op)).2 = false
~~~

## ControlStack/HoneypotBridgeProof.lean

### 193. honeypotPasses_step

Source: ControlStack/HoneypotBridgeProof.lean:34 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honeypotPasses_step {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (n k : ℕ) : Pr[= k | honeypotPasses H M D (n + 1)] = Pr[= true | H >>= M >>= D] * Pr[= k | (fun a => a + 1) <$> honeypotPasses H M D n] + Pr[= false | H >>= M >>= D] * Pr[= k | honeypotPasses H M D n]
~~~

### 194. honeypotPasses_probOutput

Source: ControlStack/HoneypotBridgeProof.lean:42 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honeypotPasses_probOutput {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (n k : ℕ) : Pr[= k | honeypotPasses H M D n] = (n.choose k : ENNReal) * Pr[= true | H >>= M >>= D] ^ k * Pr[= false | H >>= M >>= D] ^ (n - k)
~~~

### 195. bridge

Source: ControlStack/HoneypotBridgeProof.lean:76 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bridge : BridgeClaim
~~~

## ControlStack/LifetimeLedger.lean

### 196. pr_append_one

Source: ControlStack/LifetimeLedger.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma pr_append_one (ℓ ℓ' : L) (k : ℕ) (adm : List (L × ℕ)) : pr ℓ' (adm ++ [(ℓ, k)]) = pr ℓ' adm * (if ℓ = ℓ' then k else 1)
~~~

### 197. step_inv

Source: ControlStack/LifetimeLedger.lean:69 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma step_inv (cap : ℕ) (s : Option (L → ℕ)) (adm : List (L × ℕ)) (e : Ev L) (he : ¬ e.isRestore) (h : Inv cap (s, adm)) : Inv cap ((step cap s e).1, adm ++ (step cap s e).2.toList)
~~~

### 198. run_inv

Source: ControlStack/LifetimeLedger.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma run_inv (cap : ℕ) : ∀ (es : List (Ev L)) (st : Option (L → ℕ) × List (L × ℕ)), (∀ e ∈ es, ¬ e.isRestore) → Inv cap st → Inv cap (run cap st es) | [], st, _, h => h | e :: es, (s, adm), hes, h => by simp only [run] exact run_inv cap es _ (fun e' he' => hes e' (List.mem_cons_of_mem e he')) (step_inv cap s adm e (hes e List.mem_cons_self) h) theorem ledger_safe (cap : ℕ) (hcap : 1 ≤ cap) (es : List (Ev L)) (hes : ∀ e ∈ es, ¬ e.isRestore) (ℓ : L) : pr ℓ (run cap (some (fun _ => 1), []) es).2 ≤ cap
~~~

### 199. ledger_safe

Source: ControlStack/LifetimeLedger.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ledger_safe (cap : ℕ) (hcap : 1 ≤ cap) (es : List (Ev L)) (hes : ∀ e ∈ es, ¬ e.isRestore) (ℓ : L) : pr ℓ (run cap (some (fun _ => 1), []) es).2 ≤ cap
~~~

### 200. restore_breaks

Source: ControlStack/LifetimeLedger.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem restore_breaks (cap : ℕ) (hcap : 2 ≤ cap) (ℓ : L) : cap < pr ℓ (run cap (some (fun _ => 1), []) [.charge ℓ cap, .restore (fun _ => 1), .charge ℓ cap]).2
~~~

### 201. lifetime_secret_bound

Source: ControlStack/LifetimeLedger.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lifetime_secret_bound {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] {E : ℕ} (V : Fin E → Type) [∀ e, Fintype (V e)] [∀ e, DecidableEq (V e)] (cap : ℕ) (hV : ∏ e, Fintype.card (V e) ≤ cap) (ρ : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ) (dec : Ω → ((e : Fin E) → V e) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (cap : ℝ) / (Fintype.card M : ℝ)
~~~

## ControlStack/MultiStep.lean

### 202. V_zero

Source: ControlStack/MultiStep.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem V_zero {A : Type} [Fintype A] (π κ : List A → A → ℝ) (h : List A) : V π κ 0 h = 1
~~~

### 203. V_succ

Source: ControlStack/MultiStep.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem V_succ {A : Type} [Fintype A] (π κ : List A → A → ℝ) (k : ℕ) (h : List A) : V π κ (k + 1) h = ∑ a, π h a * (1 - κ h a) * V π κ k (h ++ [a])
~~~

### 204. survival_bounds

Source: ControlStack/MultiStep.lean:54 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_bounds {A : Type} [Fintype A] (π κ : List A → A → ℝ) (hπ : IsPolicy π) (hκ : IsMonitor κ) (k : ℕ) (h : List A) : 0 ≤ V π κ k h ∧ V π κ k h ≤ 1
~~~

### 205. survival_le

Source: ControlStack/MultiStep.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_le {A : Type} [Fintype A] (π κ : List A → A → ℝ) (hπ : IsPolicy π) (hκ : IsMonitor κ) (c : ℝ) (hc1 : c ≤ 1) (hcκ : ∀ h a, c ≤ κ h a) (k : ℕ) (h : List A) : V π κ k h ≤ (1 - c) ^ k
~~~

### 206. survival_const

Source: ControlStack/MultiStep.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_const {A : Type} [Fintype A] (π : List A → A → ℝ) (hπ : IsPolicy π) (c : ℝ) (k : ℕ) (h : List A) : V π (fun _ _ => c) k h = (1 - c) ^ k
~~~

### 207. V_never

Source: ControlStack/MultiStep.lean:104 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem V_never {A : Type} [Fintype A] (π : List A → A → ℝ) (hπ : IsPolicy π) (k : ℕ) (h : List A) : V π (fun _ _ => 0) k h = 1
~~~

### 208. V_always

Source: ControlStack/MultiStep.lean:109 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem V_always {A : Type} [Fintype A] (π : List A → A → ℝ) (k : ℕ) (h : List A) : V π (fun _ _ => 1) (k + 1) h = 0
~~~

### 209. seeded_marginal

Source: ControlStack/MultiStep.lean:125 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seeded_marginal {A : Type} (c : ℝ) (h : List A) (a : A) : seededMarginal c h a = c
~~~

### 210. seeded_survival

Source: ControlStack/MultiStep.lean:129 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seeded_survival {A : Type} [Fintype A] (c : ℝ) (π : List A → A → ℝ) (hπ : IsPolicy π) (k : ℕ) (hk : 1 ≤ k) (h : List A) : V π (seededκ true) k h = 0 ∧ V π (seededκ false) k h = 1 ∧ seededSurvival c π k h = 1 - c
~~~

### 211. pow_lt_self_of_two_le

Source: ControlStack/MultiStep.lean:139 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pow_lt_self_of_two_le (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (k : ℕ) (hk : 2 ≤ k) : (1 - c) ^ k < 1 - c
~~~

### 212. correlated_nogo

Source: ControlStack/MultiStep.lean:149 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem correlated_nogo {A : Type} [Fintype A] (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (π : List A → A → ℝ) (hπ : IsPolicy π) (k : ℕ) (hk : 2 ≤ k) (h : List A) : (∀ (h' : List A) (a : A), seededMarginal c h' a = c) ∧ seededSurvival c π k h = 1 - c ∧ V π (fun _ _ => c) k h = (1 - c) ^ k ∧ (1 - c) ^ k < seededSurvival c π k h
~~~

### 213. Vs_eq

Source: ControlStack/MultiStep.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Vs_eq {A Θ : Type} [Fintype A] [Fintype Θ] (π : List A → A → ℝ) (κ : Θ → List A → A → ℝ) (k : ℕ) (h : List A) (w : Θ → ℝ) : Vs π κ k h w = ∑ θ, w θ * V π (κ θ) k h
~~~

### 214. reachable_nonneg

Source: ControlStack/MultiStep.lean:184 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reachable_nonneg {A Θ : Type} (ρ : Θ → ℝ) (κ : Θ → List A → A → ℝ) (hρ : ∀ θ, 0 ≤ ρ θ) (hκ : ∀ θ, IsMonitor (κ θ)) {h : List A} {w : Θ → ℝ} (hr : Reachable ρ κ h w) : ∀ θ, 0 ≤ w θ
~~~

### 215. survival_avg

Source: ControlStack/MultiStep.lean:195 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_avg {A Θ : Type} [Fintype A] [Fintype Θ] (π : List A → A → ℝ) (hπ : IsPolicy π) (κ : Θ → List A → A → ℝ) (ρ : Θ → ℝ) (c : ℝ) (hc1 : c ≤ 1) (hpost : ∀ h w, Reachable ρ κ h w → ∀ a, c * ∑ θ, w θ ≤ ∑ θ, w θ * κ θ h a) (k : ℕ) : ∑ θ, ρ θ * V π (κ θ) k [] ≤ (1 - c) ^ k * ∑ θ, ρ θ
~~~

### 216. seeded_violates_posterior

Source: ControlStack/MultiStep.lean:225 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seeded_violates_posterior {A : Type} (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (a b : A) : let ρ : Bool → ℝ
~~~

### 217. survival_example

Source: ControlStack/MultiStep.lean:235 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_example {A : Type} [Fintype A] (π κ : List A → A → ℝ) (hπ : IsPolicy π) (hκ : IsMonitor κ) (hcκ : ∀ h a, (1 / 10 : ℝ) ≤ κ h a) (h : List A) : V π κ 5 h ≤ 0.59049
~~~

## ControlStack/OutcomeProof.lean

### 218. probOutput_isCat

Source: ControlStack/OutcomeProof.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_isCat (c : ProbComp Outcome) : Pr[= true | isCat <$> c] = Pr[= Outcome.catastrophe | c]
~~~

### 219. map_deployO

Source: ControlStack/OutcomeProof.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem map_deployO {X Z : Type} (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n : ℕ) : ∀ u h, isCat <$> deployO Bad π M D A b n u h = deploy Bad π M D A b n u h
~~~

### 220. marginal

Source: ControlStack/OutcomeProof.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem marginal : MarginalClaim
~~~

### 221. probOutput_auditO

Source: ControlStack/OutcomeProof.lean:44 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_auditO (c : ProbComp Bool) (o : Outcome) : Pr[= o | (fun caught => if caught then Outcome.caught else Outcome.catastrophe) <$> c] = Pr[= true | c] * (if o = Outcome.caught then 1 else 0) + Pr[= false | c] * (if o = Outcome.catastrophe then 1 else 0)
~~~

### 222. deployO_step

Source: ControlStack/OutcomeProof.lean:51 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployO_step {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) (o : Outcome) : Pr[= o | deployO Bad π M D A b (n+1) u h] = ∑ x, Pr[= x | π h] * ∑ z, Pr[= z | M x] * (Pr[= true | D z] * Pr[= o | (if Bad x then pure .catastrophe else deployO Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Outcome)] + Pr[= false | D z] * Pr[= o | (if u < b then (if Bad x then (fun caught => if caught then Outcome.caught else Outcome.catastrophe) <$> A h x z else deployO Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure .halted : ProbComp Outcome)])
~~~

### 223. deployO_step_real

Source: ControlStack/OutcomeProof.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployO_step_real {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) (o : Outcome) : (Pr[= o | deployO Bad π M D A b (n+1) u h]).toReal = ∑ x, (Pr[= x | π h]).toReal * ∑ z, (Pr[= z | M x]).toReal * ((Pr[= true | D z]).toReal * (Pr[= o | (if Bad x then pure .catastrophe else deployO Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Outcome)]).toReal + (1 - (Pr[= true | D z]).toReal) * (Pr[= o | (if u < b then (if Bad x then (fun caught => if caught then Outcome.caught else Outcome.catastrophe) <$> A h x z else deployO Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure .halted : ProbComp Outcome)]).toReal)
~~~

### 224. deployO_rejected

Source: ControlStack/OutcomeProof.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployO_rejected {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n : ℕ) : ∀ u h, Pr[= Outcome.rejected | deployO Bad π M D A b n u h] = 0
~~~

### 225. deployLaw

Source: ControlStack/OutcomeProof.lean:99 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployLaw : DeployLawClaim
~~~

### 226. conservation

Source: ControlStack/OutcomeProof.lean:129 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conservation : ConservationClaim
~~~

### 227. nonneg

Source: ControlStack/OutcomeProof.lean:154 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nonneg : NonnegClaim
~~~

### 228. deployO_rejected

Source: ControlStack/OutcomeProof.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployO_rejected' {X Z : Type} (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n : ℕ) : ∀ u h, Pr[= Outcome.rejected | deployO Bad π M D A b n u h] = 0
~~~

### 229. probEvent_not_toReal

Source: ControlStack/OutcomeProof.lean:190 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probEvent_not_toReal {α : Type} (c : ProbComp α) (p : α → Prop) : (Pr[fun x => ¬ p x | c]).toReal = 1 - (Pr[p | c]).toReal
~~~

### 230. gameLaw

Source: ControlStack/OutcomeProof.lean:199 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gameLaw : GameLawClaim
~~~

### 231. rateLink

Source: ControlStack/OutcomeProof.lean:231 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rateLink : RateLinkClaim
~~~

### 232. binCDF_succ_zero

Source: ControlStack/OutcomeProof.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem binCDF_succ_zero (n : ℕ) (f : ℝ) : binCDF (n + 1) 0 f = (1 - f) * binCDF n 0 f
~~~

### 233. binCDF_succ_succ

Source: ControlStack/OutcomeProof.lean:255 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem binCDF_succ_succ (n s : ℕ) (f : ℝ) : binCDF (n + 1) (s + 1) f = (1 - f) * binCDF n (s + 1) f + f * binCDF n s f
~~~

### 234. wsum_const

Source: ControlStack/OutcomeProof.lean:275 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum_const {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (φ : Z → ℝ) (μ : X → ℝ) (hM1 : ∀ x, ∑ z, M x z = 1) (hμ1 : ∑ x, μ x = 1) (a c : ℝ) : ∑ x, μ x * ∑ z, M x z * (φ z * a + (1 - φ z) * c) = (1 - flagRate M μ φ) * a + flagRate M μ φ * c
~~~

### 235. catG_benign

Source: ControlStack/OutcomeProof.lean:297 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catG_benign {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R : Hist X Z → X → Z → ℝ) (b : ℕ) (hben : ∀ h x, π h x ≠ 0 → ¬ Bad x) : ∀ n u h, catG Bad M φ π R b n u h = 0 ∧ caughtG Bad M φ π R b n u h = 0
~~~

### 236. complG_benign

Source: ControlStack/OutcomeProof.lean:312 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem complG_benign {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (μ : X → ℝ) (b : ℕ) (hM1 : ∀ x, ∑ z, M x z = 1) (hμ1 : ∑ x, μ x = 1) (hben : ∀ x, μ x ≠ 0 → ¬ Bad x) : ∀ n u h, u ≤ b → complG Bad M φ (fun _ => μ) b n u h = binCDF n (b - u) (flagRate M μ φ)
~~~

### 237. benignRecursion

Source: ControlStack/OutcomeProof.lean:341 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem benignRecursion : BenignRecursionClaim
~~~

### 238. honest

Source: ControlStack/OutcomeProof.lean:351 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest : HonestClaim
~~~

### 239. binCDF_nonneg

Source: ControlStack/OutcomeProof.lean:387 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem binCDF_nonneg (n s : ℕ) (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1) : 0 ≤ binCDF n s f
~~~

### 240. pareto

Source: ControlStack/OutcomeProof.lean:392 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pareto : ParetoClaim
~~~

### 241. witness

Source: ControlStack/OutcomeProof.lean:431 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## ControlStack/PolicyTamper.lean

### 242. policy_preserved_if_protected

Source: ControlStack/PolicyTamper.lean:31 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem policy_preserved_if_protected (p : Policy) (s : St) (ops : List Op) (h : s.activePolicy = p) : (run false s ops).activePolicy = p
~~~

### 243. tamper_possible_if_writable

Source: ControlStack/PolicyTamper.lean:42 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem tamper_possible_if_writable (s : St) (replacement : Policy) : (step true s (.attemptPolicyWrite replacement)).activePolicy = replacement
~~~

## ControlStack/RefinementProof.lean

### 244. probOutput_true_add_false_one

Source: ControlStack/RefinementProof.lean:6 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_true_add_false_one (c : ProbComp Bool) : Pr[= true | c] + Pr[= false | c] = 1
~~~

### 245. probOutput_false_toReal

Source: ControlStack/RefinementProof.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_false_toReal (c : ProbComp Bool) : (Pr[= false | c]).toReal = 1 - (Pr[= true | c]).toReal
~~~

### 246. probOutput_not_true

Source: ControlStack/RefinementProof.lean:20 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_not_true (c : ProbComp Bool) : Pr[= true | (fun caught => !caught) <$> c] = Pr[= false | c]
~~~

### 247. deploy_step

Source: ControlStack/RefinementProof.lean:24 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deploy_step {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) : Pr[= true | deploy Bad π M D A b (n+1) u h] = ∑ x, Pr[= x | π h] * ∑ z, Pr[= z | M x] * (Pr[= true | D z] * Pr[= true | (if Bad x then pure true else deploy Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Bool)] + Pr[= false | D z] * Pr[= true | (if u < b then (if Bad x then (fun caught => !caught) <$> A h x z else deploy Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure false : ProbComp Bool)])
~~~

### 248. deploy_step_real

Source: ControlStack/RefinementProof.lean:36 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deploy_step_real {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) : (Pr[= true | deploy Bad π M D A b (n+1) u h]).toReal = ∑ x, (Pr[= x | π h]).toReal * ∑ z, (Pr[= z | M x]).toReal * ((Pr[= true | D z]).toReal * (Pr[= true | (if Bad x then pure true else deploy Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Bool)]).toReal + (1 - (Pr[= true | D z]).toReal) * (Pr[= true | (if u < b then (if Bad x then (fun caught => !caught) <$> A h x z else deploy Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure false : ProbComp Bool)]).toReal)
~~~

### 249. toReal_probOutput_le_one

Source: ControlStack/RefinementProof.lean:58 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem toReal_probOutput_le_one {α : Type} (c : ProbComp α) (x : α) : (Pr[= x | c]).toReal ≤ 1
~~~

### 250. toReal_probEvent_le_one

Source: ControlStack/RefinementProof.lean:62 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem toReal_probEvent_le_one {α : Type} (c : ProbComp α) (p : α → Prop) : (Pr[p | c]).toReal ≤ 1
~~~

### 251. sum_toReal_probOutput

Source: ControlStack/RefinementProof.lean:66 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_toReal_probOutput {α : Type} [Fintype α] (c : ProbComp α) : ∑ x, (Pr[= x | c]).toReal = 1
~~~

### 252. catG_const

Source: ControlStack/RefinementProof.lean:72 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catG_const {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (b : ℕ) : ∀ n u h, catG Bad M φ π (fun _ _ _ => r) b n u h = cat Bad M φ π r b n u h
~~~

### 253. catG_congr

Source: ControlStack/RefinementProof.lean:80 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catG_congr {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R R' : Hist X Z → X → Z → ℝ) (b : ℕ) (hR : ∀ h x z, Bad x → R h x z = R' h x z) : ∀ n u h, catG Bad M φ π R b n u h = catG Bad M φ π R' b n u h
~~~

### 254. catG_le_cat

Source: ControlStack/RefinementProof.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catG_le_cat {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R : Hist X Z → X → Z → ℝ) (r : ℝ) (b : ℕ) (hπ : ∀ h x, 0 ≤ π h x) (hM : ∀ x z, 0 ≤ M x z) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) (hR : ∀ h x z, Bad x → r ≤ R h x z) : ∀ n u h, catG Bad M φ π R b n u h ≤ cat Bad M φ π r b n u h
~~~

### 255. wsum_le

Source: ControlStack/RefinementProof.lean:122 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum_le {Y : Type} [Fintype Y] (w f : Y → ℝ) (c : ℝ) (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∑ y, w y = 1) (hf : ∀ y, f y ≤ c) : ∑ y, w y * f y ≤ c
~~~

### 256. t3a

Source: ControlStack/RefinementProof.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t3a {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r A : ℝ) (b : ℕ) (hM0 : ∀ x z, 0 ≤ M x z) (hM1 : ∀ x, ∑ z, M x z = 1) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) (hπ0 : ∀ h x, 0 ≤ π h x) (hπ1 : ∀ h, ∑ x, π h x = 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hbad : ∀ x, Bad x → ∑ z, M x z * φ z ≤ A) : ∀ n u h, cat Bad M φ π r b n u h ≤ (if u < b then 1 - r + r * A else A)
~~~

### 257. final_dom

Source: ControlStack/RefinementProof.lean:185 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem final_dom (S h L r A B : ℝ) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hA : A ≤ L * h) (hB : h * S ≤ B) : S * (1 - r + r * A) ≤ (1 - r) + r * (L * B)
~~~

### 258. first_moment

Source: ControlStack/RefinementProof.lean:198 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem first_moment (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hB : binCDF (n + 1) (s + 1) h ≤ 1) : ((n : ℝ) + 1) * (h * binCDF n s h) ≤ (s : ℝ) + 1
~~~

### 259. first_moment

Source: ControlStack/RefinementProof.lean:238 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem first_moment' (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hB : binCDF (n + 1) (s + 1) h ≤ 1) : h * binCDF n s h ≤ ((s : ℝ) + 1) / ((n : ℝ) + 1)
~~~

### 260. deployG

Source: ControlStack/RefinementProof.lean:245 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployG : DeployGClaim
~~~

### 261. deploy_le

Source: ControlStack/RefinementProof.lean:258 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deploy_le : DeployClaim
~~~

### 262. deploy_exact

Source: ControlStack/RefinementProof.lean:264 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deploy_exact : DeployExactClaim
~~~

### 263. protocol

Source: ControlStack/RefinementProof.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem protocol : ProtocolClaim
~~~

### 264. endToEnd

Source: ControlStack/RefinementProof.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem endToEnd : EndToEndClaim
~~~

### 265. attain

Source: ControlStack/RefinementProof.lean:343 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attain : AttainClaim
~~~

### 266. witness

Source: ControlStack/RefinementProof.lean:375 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## ControlStack/SafetyCaseSC01.lean

### 267. step_adm

Source: ControlStack/SafetyCaseSC01.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma step_adm {L : Type} [DecidableEq L] (cap : ℕ) (s : Option (L → ℕ)) (e : Ev L) (a : L × ℕ) (h : (step cap s e).2 = some a) : ∃ ℓ k, e = .charge ℓ k ∧ a = (ℓ, k)
~~~

### 268. run_sizes

Source: ControlStack/SafetyCaseSC01.lean:32 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma run_sizes {L : Type} [DecidableEq L] (cap : ℕ) (K : ℕ) : ∀ (es : List (Ev L)) (st : Option (L → ℕ) × List (L × ℕ)), (∀ e ∈ es, ∀ ℓ k, e = .charge ℓ k → k = K) → (∀ a ∈ st.2, a.2 = K) → ∀ a ∈ (run cap st es).2, a.2 = K | [], st, _, h => h | e :: es, (s, adm), hes, h => by simp only [run] apply run_sizes cap K es _ (fun e' he' => hes e' (List.mem_cons_of_mem e he')) intro a ha rcases List.mem_append.1 ha with ha | ha · exact h a ha · cases hst : (step cap s e).2 with | none => simp [hst] at ha | some b => simp [hst] at ha; rw [ha] obtain ⟨ℓ, k, rfl, rfl⟩
~~~

### 269. pr_const

Source: ControlStack/SafetyCaseSC01.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma pr_const {L : Type} [DecidableEq L] (ℓ : L) (K : ℕ) (adm : List (L × ℕ)) (h : ∀ a ∈ adm, a.2 = K) : pr ℓ adm = K ^ (adm.filter (fun a => a.1 = ℓ)).length
~~~

### 270. ledger_five

Source: ControlStack/SafetyCaseSC01.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ledger_five {L : Type} [DecidableEq L] (es : List (Ev L)) (hes : ∀ e ∈ es, ¬ e.isRestore) (h9 : ∀ e ∈ es, ∀ ℓ k, e = .charge ℓ k → k = 9) (ℓ : L) : ((run (2 ^ 16) (some (fun _ => 1), []) es).2.filter (fun a => a.1 = ℓ)).length ≤ 5
~~~

### 271. bit_refutes

Source: ControlStack/SafetyCaseSC01.lean:78 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bit_refutes {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (enc : Ω → Bool → Unit × S → ℝ) (dec : Ω → Unit × O → Bool → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : 2 * sideSuccess ρ W enc dec ≤ ∑ o, c o
~~~

### 272. refute_threshold

Source: ControlStack/SafetyCaseSC01.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refute_threshold : (2 : ℝ) * (5551 / 10000) > 65536 / 59049
~~~

### 273. sc01_case

Source: ControlStack/SafetyCaseSC01.lean:95 | Family: F2 | Adversary: SIDE_OBSERVING | Status: PROVED_RECORDED

~~~lean
theorem sc01_case : (∀ {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ), (∀ s o, W s o ≤ c o) → (∀ o, 0 ≤ c o) → ∑ o, c o ≤ 65536 / 59049 → ∀ (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ) (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ), IsDist ρ → (∀ ω m, IsDist (enc ω m)) → (∀ ω y, IsDist (dec ω y)) → sideSuccess ρ W enc dec ≤ 1 / 2 ^ 16) ∧ (∀ p : ℝ, 0 ≤ p → p ≤ 9 / 10 → passProb p ≤ 1 / 80) ∧ (tail 64 (93382 / 100000) ≤ 1 / 80 ∧ (9 : ℝ) / 10 ≤ 93382 / 100000) ∧ (viewSpace (C
~~~

## ControlStack/ScenarioACore.lean

### 274. card_epPrefix

Source: ControlStack/ScenarioACore.lean:55 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem card_epPrefix : Fintype.card EpPrefix = 9
~~~

### 275. epView_card

Source: ControlStack/ScenarioACore.lean:60 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem epView_card : Fintype.card EpView = 9
~~~

### 276. prefixToView_viewToPrefix

Source: ControlStack/ScenarioACore.lean:71 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma prefixToView_viewToPrefix (o : ScenarioARepair.View) : prefixToView (viewToPrefix o) = o
~~~

### 277. viewToPrefix_prefixToView

Source: ControlStack/ScenarioACore.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma viewToPrefix_prefixToView (p : EpPrefix) : viewToPrefix (prefixToView p) = p
~~~

### 278. prefixEquiv_apply

Source: ControlStack/ScenarioACore.lean:99 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prefixEquiv_apply (p : EpPrefix) : prefixEquiv p = embedAll p 0 0
~~~

### 279. epView_ext

Source: ControlStack/ScenarioACore.lean:102 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma epView_ext (v w : EpView) (h : v 0 0 = w 0 0) : v = w
~~~

### 280. embedAll_viewToPrefix

Source: ControlStack/ScenarioACore.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem embedAll_viewToPrefix (v : EpView) : embedAll (prefixEquiv.symm (v 0 0)) = v
~~~

### 281. embedAll_surjective

Source: ControlStack/ScenarioACore.lean:114 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem embedAll_surjective : Function.Surjective (embedAll (C
~~~

### 282. embedAll_injective

Source: ControlStack/ScenarioACore.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem embedAll_injective : Function.Injective (embedAll (C
~~~

### 283. reachable_eq_univ

Source: ControlStack/ScenarioACore.lean:124 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reachable_eq_univ : Set.range (embedAll (C
~~~

### 284. delivered_view_coord

Source: ControlStack/ScenarioACore.lean:130 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem delivered_view_coord {R : Type} (valid : (c : Fin 1) → R → Option (Fin 8)) (tr : List (Ev 1 R)) : finalView (runG valid (init (S
~~~

### 285. card_five_prefixes

Source: ControlStack/ScenarioACore.lean:140 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem card_five_prefixes : Fintype.card (Fin 5 → EpPrefix) = 59049
~~~

### 286. lifetime_bound_prefixes

Source: ControlStack/ScenarioACore.lean:145 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lifetime_bound_prefixes {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → (Fin 5 → EpPrefix) → ℝ) (dec : Ω → (Fin 5 → EpPrefix) → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (59049 : ℝ) / 2 ^ 32 ∧ (59049 : ℝ) / 2 ^ 32 ≤ 1 / 2 ^ 16
~~~

### 287. five_episode_core_bound

Source: ControlStack/ScenarioACore.lean:163 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem five_episode_core_bound {Ω R : Type} [Fintype Ω] [Fintype R] [Fintype (Ev 1 R)] (valid : (c : Fin 1) → R → Option (Fin 8)) (L : ℕ) (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → (Fin 5 → Fin L → Ev 1 R) → ℝ) (dec : Ω → (Fin 5 → EpView) → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc (fun ω tr m => dec ω (lifetimeView valid tr) m) ≤ (59049 : ℝ) / 2 ^ 32 ∧ (59049 : ℝ) / 2 ^ 32 ≤ 1 / 2 ^ 16
~~~

### 288. card_varObs

Source: ControlStack/ScenarioACore.lean:202 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem card_varObs : Fintype.card VarObs = 66430
~~~

### 289. varObs_gt

Source: ControlStack/ScenarioACore.lean:208 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem varObs_gt : (2 : ℕ) ^ 16 < 66430
~~~

### 290. varObsEmbed_injective

Source: ControlStack/ScenarioACore.lean:216 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem varObsEmbed_injective : Function.Injective varObsEmbed
~~~

### 291. attainEnc_dist

Source: ControlStack/ScenarioACore.lean:230 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma attainEnc_dist {M V : Type} [Fintype V] [DecidableEq M] [DecidableEq V] [Nonempty V] (e : V → M) (he : Function.Injective e) (m : M) : IsDist (attainEnc e () m)
~~~

### 292. attainDec_dist

Source: ControlStack/ScenarioACore.lean:244 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma attainDec_dist {M V : Type} [Fintype M] [DecidableEq M] (e : V → M) (v : V) : IsDist (attainDec e () v)
~~~

### 293. varObs_attain

Source: ControlStack/ScenarioACore.lean:252 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem varObs_attain : (∀ m, IsDist (attainEnc varObsEmbed () m)) ∧ (∀ v, IsDist (attainDec varObsEmbed () v)) ∧ successProb (Ω
~~~

### 294. varObs_breaks_target

Source: ControlStack/ScenarioACore.lean:265 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem varObs_breaks_target : ∃ (enc : Unit → Fin (2 ^ 32) → VarObs → ℝ) (dec : Unit → VarObs → Fin (2 ^ 32) → ℝ), IsDist (fun _ : Unit => (1 : ℝ)) ∧ (∀ ω m, IsDist (enc ω m)) ∧ (∀ ω v, IsDist (dec ω v)) ∧ (1 : ℝ) / 2 ^ 16 < successProb (fun _ => 1) enc dec
~~~

## ControlStack/ScenarioARepair.lean

### 295. transcript_card

Source: ControlStack/ScenarioARepair.lean:11 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem transcript_card : Fintype.card Transcript = 59049
~~~

### 296. repair_recovery

Source: ControlStack/ScenarioARepair.lean:14 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_recovery {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → Transcript → ℝ) (dec : Ω → Transcript → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (59049 : ℝ) / 2 ^ 32
~~~

### 297. repair_target

Source: ControlStack/ScenarioARepair.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_target {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → Transcript → ℝ) (dec : Ω → Transcript → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ 1 / 2 ^ 16
~~~

## ControlStack/ScenarioASide.lean

### 298. repair_side

Source: ControlStack/ScenarioASide.lean:18 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_side {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ) (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ W enc dec ≤ 59049 * (∑ o, c o) / 2 ^ 32
~~~

### 299. repair_side_target

Source: ControlStack/ScenarioASide.lean:27 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_side_target {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (hL : ∑ o, c o ≤ 65536 / 59049) (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ) (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ W enc dec ≤ 1 / 2 ^ 16
~~~

### 300. card_obs

Source: ControlStack/ScenarioASide.lean:41 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma card_obs : Fintype.card (Transcript × Bool) ≤ 2 ^ 32
~~~

### 301. emb_inj

Source: ControlStack/ScenarioASide.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma emb_inj : Function.Injective emb
~~~

### 302. repair_one_bit_attained

Source: ControlStack/ScenarioASide.lean:56 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_one_bit_attained : ∃ (enc : Unit → Fin (2 ^ 32) → Transcript × Bool → ℝ) (dec : Unit → Transcript × Bool → Fin (2 ^ 32) → ℝ), (∀ ω m, IsDist (enc ω m)) ∧ (∀ ω y, IsDist (dec ω y)) ∧ sideSuccess (fun _ => (1 : ℝ)) idKernel enc dec = 2 * 59049 / 2 ^ 32 ∧ (1 : ℝ) / 2 ^ 16 < 2 * 59049 / 2 ^ 32
~~~

### 303. bsc_lifetime_ok

Source: ControlStack/ScenarioASide.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bsc_lifetime_ok : (2 * (1 - (49 : ℝ) / 100)) ^ 5 ≤ 65536 / 59049
~~~

### 304. bsc_lifetime_fails

Source: ControlStack/ScenarioASide.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bsc_lifetime_fails : (65536 : ℝ) / 59049 < (2 * (1 - (48 : ℝ) / 100)) ^ 5
~~~

## ControlStack/ScenarioAUsefulness.lean

### 305. passProb_eq

Source: ControlStack/ScenarioAUsefulness.lean:28 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma passProb_eq (p : ℝ) : passProb p = 64 * p ^ 63 - 63 * p ^ 64
~~~

### 306. passProb_mono

Source: ControlStack/ScenarioAUsefulness.lean:34 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma passProb_mono : MonotoneOn passProb (Set.Icc 0 1)
~~~

### 307. false_pass_le

Source: ControlStack/ScenarioAUsefulness.lean:55 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem false_pass_le (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 9 / 10) : passProb p ≤ 1 / 80
~~~

### 308. endpoint64

Source: ControlStack/ScenarioAUsefulness.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem endpoint64 : tail 64 (93382 / 100000) ≤ 1 / 80 ∧ 1 / 80 < tail 64 (93383 / 100000)
~~~

### 309. endpoint63

Source: ControlStack/ScenarioAUsefulness.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem endpoint63 : tail 63 (90438 / 100000) ≤ 1 / 80 ∧ 1 / 80 < tail 63 (90439 / 100000)
~~~

### 310. reject62

Source: ControlStack/ScenarioAUsefulness.lean:69 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reject62 : 1 / 80 < tail 62 (9 / 10)
~~~

### 311. endpoints_clear_floor

Source: ControlStack/ScenarioAUsefulness.lean:75 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem endpoints_clear_floor : (9 : ℝ) / 10 ≤ 90438 / 100000 ∧ (90438 : ℝ) / 100000 ≤ 93382 / 100000
~~~

## ControlStack/SideChannel.lean

### 312. per_seed_side

Source: ControlStack/SideChannel.lean:31 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem per_seed_side {M V S O : Type} [Fintype M] [Fintype V] [Fintype S] [Fintype O] (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (enc : M → V × S → ℝ) (dec : V × O → M → ℝ) (henc : ∀ m, IsDist (enc m)) (hdec : ∀ y, IsDist (dec y)) : ∑ m, ∑ x : V × S, enc m x * ∑ o, W x.2 o * dec (x.1, o) m ≤ (Fintype.card V : ℝ) * ∑ o, c o
~~~

### 313. side_bound

Source: ControlStack/SideChannel.lean:78 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem side_bound {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O] [Nonempty M] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ W enc dec ≤ (Fintype.card V : ℝ) * (∑ o, c o) / (Fintype.card M : ℝ)
~~~

### 314. side_bound_uninfluenced

Source: ControlStack/SideChannel.lean:95 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem side_bound_uninfluenced {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O] [Nonempty M] (ρ : Ω → ℝ) (w : O → ℝ) (hw : IsDist w) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ (fun _ => w) enc dec ≤ (Fintype.card V : ℝ) / (Fintype.card M : ℝ)
~~~

### 315. side_bound_trivial

Source: ControlStack/SideChannel.lean:104 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem side_bound_trivial {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O] [Nonempty M] (ρ : Ω → ℝ) (W : S → O → ℝ) (hW : ∀ s, IsDist (W s)) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ W enc dec ≤ (Fintype.card V : ℝ) * (Fintype.card O : ℝ) / (Fintype.card M : ℝ)
~~~

### 316. dom_pi

Source: ControlStack/SideChannel.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dom_pi {E : ℕ} {S O : Fin E → Type} [∀ e, Fintype (O e)] (W : (e : Fin E) → S e → O e → ℝ) (c : (e : Fin E) → O e → ℝ) (hW0 : ∀ e s o, 0 ≤ W e s o) (hc : ∀ e s o, W e s o ≤ c e o) : (∀ (s : (e : Fin E) → S e) (o : (e : Fin E) → O e), ∏ e, W e (s e) (o e) ≤ ∏ e, c e (o e)) ∧ ∑ o : ((e : Fin E) → O e), ∏ e, c e (o e) = ∏ e, ∑ o, c e o
~~~

### 317. side_as_covert

Source: ControlStack/SideChannel.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem side_as_covert {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) : sideSuccess ρ W enc dec = successProb ρ (fun ω m y => ∑ s, enc ω m (y.1, s) * W s y.2) dec
~~~

### 318. bsc_dom

Source: ControlStack/SideChannel.lean:147 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bsc_dom (q : ℝ) (hq : q ≤ 1 / 2) : ∀ s o, bsc q s o ≤ 1 - q
~~~

### 319. bsc_dist

Source: ControlStack/SideChannel.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bsc_dist (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (s : Bool) : IsDist (bsc q s)
~~~

## ControlStack/SoftHockey.lean

### 320. viewLaw_nonneg

Source: ControlStack/SoftHockey.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem viewLaw_nonneg {Z : Type} [Fintype Z] (c : ProbComp Z) (z : Z) : 0 ≤ viewLaw c z
~~~

### 321. viewLaw_sum

Source: ControlStack/SoftHockey.lean:22 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem viewLaw_sum {Z : Type} [Fintype Z] (c : ProbComp Z) : ∑ z, viewLaw c z = 1
~~~

### 322. passRule_isRule

Source: ControlStack/SoftHockey.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem passRule_isRule {Z : Type} (D : Z → ProbComp Bool) : isRule (fun z => (Pr[= true | D z]).toReal)
~~~

### 323. viewLaw_pass

Source: ControlStack/SoftHockey.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem viewLaw_pass {Z : Type} [Fintype Z] (c : ProbComp Z) (D : Z → ProbComp Bool) : ∑ z, viewLaw c z * (Pr[= true | D z]).toReal = (Pr[= true | c >>= D]).toReal
~~~

### 324. hockey_pass_bound

Source: ControlStack/SoftHockey.lean:38 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hockey_pass_bound {Z : Type} [Fintype Z] (η : ℝ) (P Q : Z → ℝ) (D : Z → ProbComp Bool) : (∑ z, P z * (Pr[= true | D z]).toReal) ≤ Real.exp η * (∑ z, Q z * (Pr[= true | D z]).toReal) + hs η P Q
~~~

### 325. operational_hockey_bound

Source: ControlStack/SoftHockey.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem operational_hockey_bound {Z : Type} [Fintype Z] (η δ : ℝ) (H : ProbComp Z) (X : ProbComp Z) (D : Z → ProbComp Bool) (hδ : hs η (viewLaw X) (viewLaw H) ≤ δ) : (Pr[= true | X >>= D]).toReal ≤ Real.exp η * (Pr[= true | H >>= D]).toReal + δ
~~~

### 326. softEndToEndHockey

Source: ControlStack/SoftHockey.lean:71 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem softEndToEndHockey {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) (r η δ : ℝ) (hns : 1 ≤ ns) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hδ0 : 0 ≤ δ) (hrec : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) (hhs : ∀ x, Bad x → hs η (viewLaw (M x)) (viewLaw (H >>= M)) ≤ δ) : (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal ≤ (1 - r) + r * (δ + Real.exp η * ((ns : ℝ) / ((nh : ℝ) + 1)))
~~~

## ControlStack/SoftSlack.lean

### 327. rejection_rate

Source: ControlStack/SoftSlack.lean:32 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rejection_rate (d : ℕ) : (Pr[= true | rejectionCoin d]).toReal = 1 / ((d + 1 : ℕ) : ℝ)
~~~

### 328. survives_step

Source: ControlStack/SoftSlack.lean:39 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survives_step {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (d n : ℕ) : Pr[= true | survives H M D d (n + 1)] = Pr[= true | H >>= M >>= D] * Pr[= false | rejectionCoin d] * Pr[= true | survives H M D d n] + Pr[= false | H >>= M >>= D] * Pr[= true | survives H M D d n]
~~~

### 329. survives_step_real

Source: ControlStack/SoftSlack.lean:58 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survives_step_real {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (d n : ℕ) : (Pr[= true | survives H M D d (n + 1)]).toReal = (1 - (Pr[= true | H >>= M >>= D]).toReal / ((d + 1 : ℕ) : ℝ)) * (Pr[= true | survives H M D d n]).toReal
~~~

### 330. bridge

Source: ControlStack/SoftSlack.lean:75 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bridge : BridgeClaim
~~~

### 331. geom_poly_bound

Source: ControlStack/SoftSlack.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem geom_poly_bound (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (1 + (n : ℝ) * x) * (1 - x) ^ n ≤ 1
~~~

### 332. soft_survival_first_moment

Source: ControlStack/SoftSlack.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem soft_survival_first_moment (nh ns : ℕ) (h : ℝ) (hns : 1 ≤ ns) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : h * (1 - h / (ns : ℝ)) ^ nh ≤ (ns : ℝ) / ((nh : ℝ) + 1)
~~~

### 333. protocol_factorization

Source: ControlStack/SoftSlack.lean:147 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem protocol_factorization {X Z Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) : (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal = ∑ ω, (Pr[= ω | ρ]).toReal * (Pr[= true | survives H M (D ω) (ns - 1) nh]).toReal * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
~~~

### 334. protocol_survival_formula

Source: ControlStack/SoftSlack.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem protocol_survival_formula {X Z Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) (hns : 1 ≤ ns) : (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal = ∑ ω, (Pr[= ω | ρ]).toReal * (1 - (Pr[= true | H >>= M >>= D ω]).toReal / (ns : ℝ)) ^ nh * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
~~~

### 335. softEndToEnd

Source: ControlStack/SoftSlack.lean:188 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem softEndToEnd {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) (r L : ℝ) (hns : 1 ≤ ns) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hrec : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) (hdom : ∀ x, Bad x → ∀ z, (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) : (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal ≤ (1 - r) + r * (L * ((ns : ℝ) / ((nh : ℝ) + 1)))
~~~

## ControlStack/Spike.lean

### 336. distinguish_le_tv

Source: ControlStack/Spike.lean:17 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem distinguish_le_tv {X Z : Type} (M : X → ProbComp Z) (PA PH : ProbComp X) (D : Z → ProbComp Bool) : |Pr[= true | PA >>= M >>= D].toReal - Pr[= true | PH >>= M >>= D].toReal| ≤ tvDist (PA >>= M) (PH >>= M)
~~~

### 337. mediated_tv_le

Source: ControlStack/Spike.lean:24 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mediated_tv_le {X Z : Type} (M : X → ProbComp Z) (PA PH : ProbComp X) : tvDist (PA >>= M) (PH >>= M) ≤ tvDist PA PH
~~~

## ControlStack/StratifiedGame.lean

### 338. classPasses_bridge

Source: ControlStack/StratifiedGame.lean:28 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classPasses_bridge {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (m sc : ℕ) : (Pr[= true | classPasses H M D m sc]).toReal = binCDF m sc (Pr[= true | H >>= M >>= D]).toReal
~~~

### 339. stratifiedSurvives_prob

Source: ControlStack/StratifiedGame.lean:37 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedSurvives_prob {X Z C : Type} (H : C → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (m sc : ℕ) (classes : List C) : (Pr[= true | stratifiedSurvives H M D m sc classes]).toReal = (classes.map fun e => (Pr[= true | classPasses (H e) M D m sc]).toReal).prod
~~~

### 340. stratifiedSurvives_binomial

Source: ControlStack/StratifiedGame.lean:54 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedSurvives_binomial {X Z C : Type} (H : C → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (m sc : ℕ) (classes : List C) : (Pr[= true | stratifiedSurvives H M D m sc classes]).toReal = (classes.map fun e => binCDF m sc (Pr[= true | H e >>= M >>= D]).toReal).prod
~~~

### 341. stratifiedProtocol_factorization

Source: ControlStack/StratifiedGame.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedProtocol_factorization {X Z C Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : Ω → C → ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (classes : List C) (m sc b N : ℕ) : (Pr[= true | stratifiedProtocolGame Bad ρ H M D π A classes m sc b N]).toReal = ∑ ω, (Pr[= ω | ρ]).toReal * (Pr[= true | stratifiedSurvives (H ω) M (D ω) m sc classes]).toReal * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
~~~

### 342. stratifiedProtocol_binomial

Source: ControlStack/StratifiedGame.lean:103 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedProtocol_binomial {X Z C Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : Ω → C → ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (classes : List C) (m sc b N : ℕ) : (Pr[= true | stratifiedProtocolGame Bad ρ H M D π A classes m sc b N]).toReal = ∑ ω, (Pr[= ω | ρ]).toReal * (classes.map fun e => binCDF m sc (Pr[= true | H ω e >>= M >>= D ω]).toReal).prod * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
~~~

### 343. listProduct_nonneg

Source: ControlStack/StratifiedGame.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem listProduct_nonneg {C : Type} (classes : List C) (f : C → ℝ) (hf0 : ∀ e ∈ classes, 0 ≤ f e) : 0 ≤ (classes.map f).prod
~~~

### 344. listProduct_le_one

Source: ControlStack/StratifiedGame.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem listProduct_le_one {C : Type} (classes : List C) (f : C → ℝ) (hf0 : ∀ e ∈ classes, 0 ≤ f e) (hf1 : ∀ e ∈ classes, f e ≤ 1) : (classes.map f).prod ≤ 1
~~~

### 345. listProduct_le_factor

Source: ControlStack/StratifiedGame.lean:148 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem listProduct_le_factor {C : Type} (classes : List C) (f : C → ℝ) (hf0 : ∀ e ∈ classes, 0 ≤ f e) (hf1 : ∀ e ∈ classes, f e ≤ 1) (e : C) (he : e ∈ classes) : (classes.map f).prod ≤ f e
~~~

### 346. stratifiedProtocolEndToEnd

Source: ControlStack/StratifiedGame.lean:179 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedProtocolEndToEnd {X Z C Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (classOf : X → C) (classes : List C) (ρ : ProbComp Ω) (H : Ω → C → ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (m sc b N : ℕ) (r L : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hrec : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) (hclass : ∀ x, Bad x → classOf x ∈ classes) (hdom : ∀ ω x z, Bad x → (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H ω (classOf x) >>= M]).toReal) : (Pr[= true | stratifiedProtocolGame Bad ρ H M D π A classes m sc b N]).toReal ≤ (1 - r) + r * (L * (((sc : ℝ) + 1) / ((m : ℝ) + 1)))
~~~

## ControlStack/TrustedBroker.lean

### 347. initial_safe

Source: ControlStack/TrustedBroker.lean:69 | Family: F8 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem initial_safe (cap : Nat) : Safe (initial cap)
~~~

### 348. initial_coherent

Source: ControlStack/TrustedBroker.lean:77 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem initial_coherent (cap : Nat) : Coherent (initial cap)
~~~

### 349. nonce_history_redundant

Source: ControlStack/TrustedBroker.lean:80 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem nonce_history_redundant (s : State) (coherent : Coherent s) (nonce : Nat) (a : Approval) (lookup : s.approvals nonce = some a) (unused : a.used = false) : nonce ∉ s.consumed
~~~

### 350. committed_nonce_unusable

Source: ControlStack/TrustedBroker.lean:112 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem committed_nonce_unusable (roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease) (now : Nat) (r' : Request) (a' : Approval) (l' : Lease) (sameNonce : r'.nonce = r.nonce) : ¬ Allowed roles (committed s r a l) now r' a' l'
~~~

### 351. transaction_preserves

Source: ControlStack/TrustedBroker.lean:158 | Family: F8 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem transaction_preserves (roles : Roles) (s t : State) (safe : Safe s) (step : Step roles s t) : Safe t
~~~

### 352. halted_absorbing

Source: ControlStack/TrustedBroker.lean:196 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem halted_absorbing (roles : Roles) (s t : State) (halted : s.halted = true) (step : Step roles s t) : t.halted = true ∧ t.releases = s.releases
~~~

### 353. transaction_coherent

Source: ControlStack/TrustedBroker.lean:201 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem transaction_coherent (roles : Roles) (s t : State) (coherent : Coherent s) (step : Step roles s t) : Coherent t
~~~

### 354. trace_preserves

Source: ControlStack/TrustedBroker.lean:233 | Family: F8 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem trace_preserves (roles : Roles) (s t : State) (safe : Safe s) (trace : Trace roles s t) : Safe t
~~~

### 355. trace_coherent

Source: ControlStack/TrustedBroker.lean:239 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem trace_coherent (roles : Roles) (s t : State) (coherent : Coherent s) (trace : Trace roles s t) : Coherent t
~~~

### 356. trace_halt_absorbing

Source: ControlStack/TrustedBroker.lean:245 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem trace_halt_absorbing (roles : Roles) (s t : State) (halted : s.halted = true) (trace : Trace roles s t) : t.halted = true ∧ t.releases = s.releases
~~~

## ControlStack/UseQ.lean

### 357. foldl_add_eq

Source: ControlStack/UseQ.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_add_eq {m : ℕ} (f : Fin m → ℚ) : ∀ (l : List (Fin m)) (acc : ℚ), l.foldl (fun acc i => acc + f i) acc = acc + (l.map f).sum
~~~

### 358. sumQ_eq

Source: ControlStack/UseQ.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sumQ_eq (m : ℕ) (f : Fin m → ℚ) : sumQ m f = ∑ i, f i
~~~

### 359. checkUseQ_spec

Source: ControlStack/UseQ.lean:33 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkUseQ_spec {N m t : ℕ} {rew : Fin t → Fin N → Fin m → ℚ} {K : Fin t → Fin N → Fin m → Fin m → ℚ} {adm : Fin t → Fin N → Fin m → Bool} {W : Fin (N + 1) → Fin m → ℚ} {s₀ : Fin m} {floor : ℚ} (hc : checkUseQ N m t rew K adm W s₀ floor = true) : 0 < t ∧ floor ≤ W (Fin.last N) s₀ ∧ (∀ s, W 0 s ≤ 0) ∧ (∀ i s, ∃ th, adm th i s = true) ∧ (∀ th i s, adm th i s = true → W i.succ s ≤ rew th i s + ∑ s', K th i s s' * W i.castSucc s')
~~~

### 360. selector_exists

Source: ControlStack/UseQ.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem selector_exists {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ) (K : Fin t → Fin N → Fin m → Fin m → ℚ) (adm : Fin t → Fin N → Fin m → Bool) (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ) (hc : checkUseQ N m t rew K adm W s₀ floor = true) : ∃ θ : ℕ → List (Fin m) → Fin m → Fin t, ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true
~~~

### 361. checkUseQ_sound

Source: ControlStack/UseQ.lean:76 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkUseQ_sound {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ) (K : Fin t → Fin N → Fin m → Fin m → ℚ) (adm : Fin t → Fin N → Fin m → Bool) (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ) (θ : ℕ → List (Fin m) → Fin m → Fin t) (hc : checkUseQ N m t rew K adm W s₀ floor = true) (hK : ∀ th i s, adm th i s = true → ∀ s', 0 ≤ K th i s s') (hθ : ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true) : (floor : ℝ) ≤ honestValue rew K θ N s₀ []
~~~

### 362. claim

Source: ControlStack/UseQ.lean:156 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 363. witness

Source: ControlStack/UseQ.lean:163 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## ControlStack/Witnesses/LeakWitness.lean

### 364. K_nonneg

Source: ControlStack/Witnesses/LeakWitness.lean:45 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem K_nonneg (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) (z : Unit × AOut Bool) : 0 ≤ K ε S h z
~~~

### 365. K_sum

Source: ControlStack/Witnesses/LeakWitness.lean:49 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem K_sum (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) : ∑ z, K ε S h z ≤ 1
~~~

### 366. K_cons

Source: ControlStack/Witnesses/LeakWitness.lean:59 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem K_cons (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) (y : Unit) (o : AOut Bool) (hK : K ε S h (y, o) ≠ 0) : o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length))
~~~

### 367. K_dom

Source: ControlStack/Witnesses/LeakWitness.lean:67 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem K_dom (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) (o : AOut Bool) (hf : o.2.2 = false) : ∑ y, K ε S h (y, o) ≤ cl ε (h.map Prod.snd) o
~~~

### 368. cl_nonneg

Source: ControlStack/Witnesses/LeakWitness.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cl_nonneg (g : List (AOut Bool)) (o : AOut Bool) : 0 ≤ cl ε g o
~~~

### 369. leak_mass

Source: ControlStack/Witnesses/LeakWitness.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem leak_mass : mass (dropStop caughtFlag (cl ε)) 2 [] = 2 * (1 - ε)
~~~

### 370. leak_bound

Source: ControlStack/Witnesses/LeakWitness.lean:93 | Family: F6 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem leak_bound : ∑ S : Finset (Fin 2), (if S ∈ AuditBudget.randomSchedules 2 1 then (Nat.choose 2 1 : ℝ)⁻¹ else 0) * val (K ε S) (survInd 1 S) 2 [] ≤ 1 - ε
~~~

## ControlStack/Witnesses/Necessity.lean

### 371. jointSuccess_indep

Source: ControlStack/Witnesses/Necessity.lean:35 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem jointSuccess_indep {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V] (ρ : Ω → ℝ) (enc : Ω → M → V → ℝ) (dec : Ω → V → M → ℝ) : jointSuccess (fun ω _ => ρ ω * (Fintype.card M : ℝ)⁻¹) enc dec = successProb ρ enc dec
~~~

### 372. seed_secret_breaks_covert

Source: ControlStack/Witnesses/Necessity.lean:48 | Family: F2 | Adversary: SHARED_SEED | Status: SOURCE_ONLY

~~~lean
theorem seed_secret_breaks_covert {M : Type} [Fintype M] [DecidableEq M] (hM : 2 ≤ Fintype.card M) : jointSuccess (fun (ω m : M) => if ω = m then (Fintype.card M : ℝ)⁻¹ else 0) (fun (_ _ : M) (_ : Unit) => (1 : ℝ)) (fun (ω : M) (_ : Unit) (m : M) => if m = ω then (1 : ℝ) else 0) = 1 ∧ (Fintype.card Unit : ℝ) / (Fintype.card M : ℝ) < 1
~~~

### 373. comono_dist

Source: ControlStack/Witnesses/Necessity.lean:79 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem comono_dist (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsDist (comono p)
~~~

### 374. comono_marginal

Source: ControlStack/Witnesses/Necessity.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem comono_marginal (p : ℝ) (i : Fin 64) : ∑ x, comono p x * (if x i = true then 1 else 0) = p
~~~

### 375. correlated_lifetimes_break_gate

Source: ControlStack/Witnesses/Necessity.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem correlated_lifetimes_break_gate : (∀ i : Fin 64, ∑ x, comono (9 / 10) x * (if x i = true then 1 else 0) = 9 / 10) ∧ ∑ x, comono (9 / 10) x * (if 63 ≤ count x then 1 else 0) = 9 / 10 ∧ ScenarioAUsefulness.passProb (9 / 10) ≤ 1 / 80 ∧ (1 : ℝ) / 80 < 9 / 10
~~~

### 376. marginal_certs_dont_compose

Source: ControlStack/Witnesses/Necessity.lean:117 | Family: F8 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem marginal_certs_dont_compose : (∀ m b, ∑ o : Bool × Bool, xorLaw m o * (if o.1 = b then 1 else 0) = 1 / 2) ∧ (∀ m b, ∑ o : Bool × Bool, xorLaw m o * (if o.2 = b then 1 else 0) = 1 / 2) ∧ (1 / 2 : ℝ) * ∑ m : Bool, ∑ o : Bool × Bool, xorLaw m o * (if xor o.1 o.2 = m then 1 else 0) = 1
~~~

### 377. shared_score_product_unsound

Source: ControlStack/Witnesses/Necessity.lean:130 | Family: F8 | Adversary: SHARED_SEED | Status: SOURCE_ONLY

~~~lean
theorem shared_score_product_unsound : (∑ s : Bool, scoreLaw s * (if s = false then 1 else 0)) = 1 / 10 ∧ (∑ s : Bool, scoreLaw s * (if s = false ∧ s = false then 1 else 0)) = 1 / 10 ∧ (1 / 10 : ℝ) * (1 / 10) < 1 / 10
~~~

### 378. exhausted_no_audit

Source: ControlStack/Witnesses/Necessity.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exhausted_no_audit {N : ℕ} (B : ℕ) (flags : Fin N → Bool) (A : Finset (Fin N)) (h : ∀ i ∈ A, B ≤ (Finset.univ.filter (fun j : Fin N => j < i ∧ flags j = true)).card) : ∀ i ∈ A, audited B flags i = false
~~~

### 379. audited_last

Source: ControlStack/Witnesses/Necessity.lean:164 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem audited_last (b : Bool × Bool × Bool) : audited 1 (flagsOf b) 3 = (!b.1 && !b.2.1 && !b.2.2)
~~~

### 380. fp_exhaustion_breaks_audit

Source: ControlStack/Witnesses/Necessity.lean:176 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fp_exhaustion_breaks_audit : (∑ b : Bool × Bool × Bool, (1 / 8 : ℚ) * (if audited 1 (flagsOf b) 3 = false then 1 else 0)) = 7 / 8 ∧ (Nat.choose 3 1 : ℚ) / Nat.choose 4 1 = 3 / 4
~~~

## proofs/CANONF1.lean

### 381. k_aren_comp

Source: proofs/CANONF1.lean:4 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_aren_comp (f g : ℕ → ℕ) (a : AExp) : (a.rename f).rename g = a.rename (g ∘ f)
~~~

### 382. k_bren_comp

Source: proofs/CANONF1.lean:7 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_bren_comp (f g : ℕ → ℕ) (b : BExp) : (b.rename f).rename g = b.rename (g ∘ f)
~~~

### 383. k_sren_comp

Source: proofs/CANONF1.lean:10 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_sren_comp (f g : ℕ → ℕ) (s : Stmt) : (s.rename f).rename g = s.rename (g ∘ f)
~~~

### 384. k_pren_comp

Source: proofs/CANONF1.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_pren_comp (f g : ℕ → ℕ) (p : Prog) : (p.rename f).rename g = p.rename (g ∘ f)
~~~

### 385. k_aocc_ren

Source: proofs/CANONF1.lean:16 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_aocc_ren (f : ℕ → ℕ) (a : AExp) : (a.rename f).occ = a.occ.map f
~~~

### 386. k_bocc_ren

Source: proofs/CANONF1.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_bocc_ren (f : ℕ → ℕ) (b : BExp) : (b.rename f).occ = b.occ.map f
~~~

### 387. k_socc_ren

Source: proofs/CANONF1.lean:22 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_socc_ren (f : ℕ → ℕ) (s : Stmt) : (s.rename f).occ = s.occ.map f
~~~

### 388. k_pocc_ren

Source: proofs/CANONF1.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_pocc_ren (f : ℕ → ℕ) (p : Prog) : (p.rename f).occ = p.occ.map f
~~~

### 389. k_aren_congr

Source: proofs/CANONF1.lean:28 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_aren_congr {f g : ℕ → ℕ} (a : AExp) (h : ∀ v ∈ a.occ, f v = g v) : a.rename f = a.rename g
~~~

### 390. k_bren_congr

Source: proofs/CANONF1.lean:43 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_bren_congr {f g : ℕ → ℕ} (b : BExp) (h : ∀ v ∈ b.occ, f v = g v) : b.rename f = b.rename g
~~~

### 391. k_sren_congr

Source: proofs/CANONF1.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_sren_congr {f g : ℕ → ℕ} (s : Stmt) (h : ∀ v ∈ s.occ, f v = g v) : s.rename f = s.rename g
~~~

### 392. k_pren_congr

Source: proofs/CANONF1.lean:85 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_pren_congr {f g : ℕ → ℕ} (p : Prog) (h : ∀ v ∈ p.occ, f v = g v) : p.rename f = p.rename g
~~~

### 393. k_pren_id

Source: proofs/CANONF1.lean:91 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_pren_id (p : Prog) : p.rename id = p
~~~

### 394. k_aeval_ren

Source: proofs/CANONF1.lean:101 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_aeval_ren {f : ℕ → ℕ} {σ τ : State} (a : AExp) (h : ∀ v ∈ a.occ, τ (f v) = σ v) : (a.rename f).eval τ = a.eval σ
~~~

### 395. k_beval_ren

Source: proofs/CANONF1.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_beval_ren {f : ℕ → ℕ} {σ τ : State} (b : BExp) (h : ∀ v ∈ b.occ, τ (f v) = σ v) : (b.rename f).eval τ = b.eval σ
~~~

### 396. k_exec_seq_iff

Source: proofs/CANONF1.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_exec_seq_iff {s t : Stmt} {σ σ'' : State} : Exec (.seq s t) σ σ'' ↔ ∃ σ', Exec s σ σ' ∧ Exec t σ' σ''
~~~

### 397. k_exec_ite_iff

Source: proofs/CANONF1.lean:151 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_exec_ite_iff {b : BExp} {s t : Stmt} {σ σ' : State} : Exec (.ite b s t) σ σ' ↔ (b.eval σ = true ∧ Exec s σ σ') ∨ (b.eval σ = false ∧ Exec t σ σ')
~~~

### 398. k_exec_cfor_iff

Source: proofs/CANONF1.lean:162 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_exec_cfor_iff {i : Stmt} {c : BExp} {st body : Stmt} {σ σ' : State} : Exec (.cfor i c st body) σ σ' ↔ Exec (.seq i (.while c (.seq body st))) σ σ'
~~~

### 399. k_while_mono

Source: proofs/CANONF1.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_while_mono {b : BExp} {s s' : Stmt} (h : ∀ σ σ', Exec s σ σ' → Exec s' σ σ') : ∀ σ σ', Exec (.while b s) σ σ' → Exec (.while b s') σ σ'
~~~

### 400. k_seq_congr

Source: proofs/CANONF1.lean:189 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_seq_congr {s s' t t' : Stmt} (h1 : KSEq s s') (h2 : KSEq t t') : KSEq (.seq s t) (.seq s' t')
~~~

### 401. k_ite_congr

Source: proofs/CANONF1.lean:195 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_ite_congr {b : BExp} {s s' t t' : Stmt} (h1 : KSEq s s') (h2 : KSEq t t') : KSEq (.ite b s t) (.ite b s' t')
~~~

### 402. k_while_congr

Source: proofs/CANONF1.lean:201 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_while_congr {b : BExp} {s s' : Stmt} (h : KSEq s s') : KSEq (.while b s) (.while b s')
~~~

### 403. k_cfor_congr

Source: proofs/CANONF1.lean:206 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_cfor_congr {i i' : Stmt} {c : BExp} {st st' b b' : Stmt} (hi : KSEq i i') (hst : KSEq st st') (hb : KSEq b b') : KSEq (.cfor i c st b) (.cfor i' c st' b')
~~~

### 404. k_sEq_refl

Source: proofs/CANONF1.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_sEq_refl (s : Stmt) : KSEq s s
~~~

### 405. k_forstep_sEq

Source: proofs/CANONF1.lean:214 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_forstep_sEq {s t : Stmt} (h : ForStep s t) : KSEq s t
~~~

### 406. k_eqv_sEq

Source: proofs/CANONF1.lean:234 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_sEq {s t : Stmt} (h : Relation.EqvGen ForStep s t) : KSEq s t
~~~

### 407. k_exec_rename

Source: proofs/CANONF1.lean:243 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_exec_rename {f : ℕ → ℕ} {V : Set ℕ} (hf : Set.InjOn f V) {s : Stmt} {σ σ' : State} (h : Exec s σ σ') : (∀ v ∈ s.occ, v ∈ V) → ∀ τ : State, (∀ v ∈ V, τ (f v) = σ v) → ∃ τ', Exec (s.rename f) τ τ' ∧ ∀ v ∈ V, τ' (f v) = σ' v
~~~

### 408. k_runs_rename

Source: proofs/CANONF1.lean:294 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_runs_rename {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) {ins : List ℤ} {out : ℤ} (h : Runs p ins out) : Runs (p.rename f) ins out
~~~

### 409. k_ren_inverse

Source: proofs/CANONF1.lean:311 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_ren_inverse {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) : ∃ g, Admissible g (p.rename f) ∧ (p.rename f).rename g = p
~~~

### 410. k_runs_rename_iff

Source: proofs/CANONF1.lean:349 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_runs_rename_iff {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) (ins : List ℤ) (out : ℤ) : Runs p ins out ↔ Runs (p.rename f) ins out
~~~

### 411. k_append_assoc

Source: proofs/CANONF1.lean:362 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_append_assoc (a b c : Stmt) : (a.append b).append c = a.append (b.append c)
~~~

### 412. k_FF_step

Source: proofs/CANONF1.lean:369 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_FF_step {s t : Stmt} (h : ForStep s t) : KFF s = KFF t
~~~

### 413. k_FF_eqv

Source: proofs/CANONF1.lean:398 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_FF_eqv {s t : Stmt} (h : Relation.EqvGen ForStep s t) : KFF s = KFF t
~~~

### 414. k_desugar_ren

Source: proofs/CANONF1.lean:405 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_desugar_ren (f : ℕ → ℕ) (s : Stmt) : desugar (s.rename f) = (desugar s).rename f
~~~

### 415. k_append_ren

Source: proofs/CANONF1.lean:408 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_append_ren (f : ℕ → ℕ) (a b : Stmt) : (a.append b).rename f = (a.rename f).append (b.rename f)
~~~

### 416. k_flatten_ren

Source: proofs/CANONF1.lean:417 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_flatten_ren (f : ℕ → ℕ) (s : Stmt) : flatten (s.rename f) = (flatten s).rename f
~~~

### 417. k_FF_ren

Source: proofs/CANONF1.lean:420 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_FF_ren (f : ℕ → ℕ) (s : Stmt) : KFF (s.rename f) = (KFF s).rename f
~~~

### 418. k_occ_append

Source: proofs/CANONF1.lean:423 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_occ_append (a b : Stmt) : (a.append b).occ = a.occ ++ b.occ
~~~

### 419. k_occ_flatten

Source: proofs/CANONF1.lean:430 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_occ_flatten (s : Stmt) : (flatten s).occ = s.occ
~~~

### 420. k_mem_occ_desugar

Source: proofs/CANONF1.lean:433 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_occ_desugar (s : Stmt) (v : ℕ) : v ∈ (desugar s).occ ↔ v ∈ s.occ
~~~

### 421. k_mem_occ_FF

Source: proofs/CANONF1.lean:444 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_occ_FF (s : Stmt) (v : ℕ) : v ∈ (KFF s).occ ↔ v ∈ s.occ
~~~

### 422. k_firstOcc_eq

Source: proofs/CANONF1.lean:451 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_firstOcc_eq (l : List ℕ) : firstOcc l = l.foldl kstep []
~~~

### 423. k_mem_foldl

Source: proofs/CANONF1.lean:453 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_foldl (l acc : List ℕ) (v : ℕ) : v ∈ l.foldl kstep acc ↔ v ∈ acc ∨ v ∈ l
~~~

### 424. k_mem_firstOcc

Source: proofs/CANONF1.lean:472 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_firstOcc (l : List ℕ) (v : ℕ) : v ∈ firstOcc l ↔ v ∈ l
~~~

### 425. k_foldl_map

Source: proofs/CANONF1.lean:476 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_foldl_map {f : ℕ → ℕ} {S : Set ℕ} (hf : Set.InjOn f S) (l acc : List ℕ) (hl : ∀ v ∈ l, v ∈ S) (hacc : ∀ v ∈ acc, v ∈ S) : (l.map f).foldl kstep (acc.map f) = (l.foldl kstep acc).map f
~~~

### 426. k_firstOcc_map

Source: proofs/CANONF1.lean:509 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_firstOcc_map {f : ℕ → ℕ} {S : Set ℕ} (hf : Set.InjOn f S) (l : List ℕ) (hl : ∀ v ∈ l, v ∈ S) : firstOcc (l.map f) = (firstOcc l).map f
~~~

### 427. k_idxOf_map

Source: proofs/CANONF1.lean:515 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_idxOf_map {f : ℕ → ℕ} {S : Set ℕ} (hf : Set.InjOn f S) (v : ℕ) (hv : v ∈ S) : ∀ (L : List ℕ), (∀ w ∈ L, w ∈ S) → (L.map f).idxOf (f v) = L.idxOf v | [], _ => rfl | a :: L, hL => by rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, k_idxOf_map hf v hv L (fun w hw => hL w (by simp [hw]))] have ha : a ∈ S
~~~

### 428. k_canon_eq

Source: proofs/CANONF1.lean:532 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canon_eq (p : Prog) : canon p = kcanon' (desugarProg p)
~~~

### 429. k_mem_locals

Source: proofs/CANONF1.lean:534 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_locals {d : Prog} {v : ℕ} : v ∈ d.locals ↔ v ∈ d.occ ∧ d.nparams ≤ v
~~~

### 430. k_canonMap_ren

Source: proofs/CANONF1.lean:537 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canonMap_ren {f : ℕ → ℕ} {d : Prog} (hA : Admissible f d) (v : ℕ) (hv : v ∈ d.occ) : (d.rename f).canonMap (f v) = d.canonMap v
~~~

### 431. k_canon'_ren

Source: proofs/CANONF1.lean:567 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canon'_ren {f : ℕ → ℕ} {d : Prog} (hA : Admissible f d) : kcanon' (d.rename f) = kcanon' d
~~~

### 432. k_desugarProg_ren

Source: proofs/CANONF1.lean:575 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_desugarProg_ren (f : ℕ → ℕ) (p : Prog) : desugarProg (p.rename f) = (desugarProg p).rename f
~~~

### 433. k_adm_desugar

Source: proofs/CANONF1.lean:581 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_adm_desugar {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) : Admissible f (desugarProg p)
~~~

### 434. k_canon_step

Source: proofs/CANONF1.lean:590 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canon_step {p q : Prog} (h : Step p q) : canon p = canon q
~~~

### 435. k_canon_syn

Source: proofs/CANONF1.lean:599 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canon_syn {p q : Prog} (h : SynEquiv p q) : canon p = canon q
~~~

### 436. k_eqv_map

Source: proofs/CANONF1.lean:608 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_map {φ : Stmt → Stmt} (hφ : ∀ a b, ForStep a b → ForStep (φ a) (φ b)) {a b : Stmt} (h : Relation.EqvGen ForStep a b) : Relation.EqvGen ForStep (φ a) (φ b)
~~~

### 437. k_eqv_seq

Source: proofs/CANONF1.lean:616 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_seq {s s' t t' : Stmt} (h1 : Relation.EqvGen ForStep s s') (h2 : Relation.EqvGen ForStep t t') : Relation.EqvGen ForStep (.seq s t) (.seq s' t')
~~~

### 438. k_eqv_ite

Source: proofs/CANONF1.lean:621 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_ite {b : BExp} {s s' t t' : Stmt} (h1 : Relation.EqvGen ForStep s s') (h2 : Relation.EqvGen ForStep t t') : Relation.EqvGen ForStep (.ite b s t) (.ite b s' t')
~~~

### 439. k_eqv_while

Source: proofs/CANONF1.lean:626 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_while {b : BExp} {s s' : Stmt} (h : Relation.EqvGen ForStep s s') : Relation.EqvGen ForStep (.while b s) (.while b s')
~~~

### 440. k_eqv_cfor

Source: proofs/CANONF1.lean:630 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_cfor {i i' : Stmt} {c : BExp} {st st' body body' : Stmt} (hi : Relation.EqvGen ForStep i i') (hst : Relation.EqvGen ForStep st st') (hb : Relation.EqvGen ForStep body body') : Relation.EqvGen ForStep (.cfor i c st body) (.cfor i' c st' body')
~~~

### 441. k_eqv_append

Source: proofs/CANONF1.lean:640 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_append (a b : Stmt) : Relation.EqvGen ForStep (.seq a b) (a.append b)
~~~

### 442. k_eqv_flatten

Source: proofs/CANONF1.lean:646 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_flatten (s : Stmt) : Relation.EqvGen ForStep s (flatten s)
~~~

### 443. k_eqv_desugar

Source: proofs/CANONF1.lean:655 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_desugar (s : Stmt) : Relation.EqvGen ForStep s (desugar s)
~~~

### 444. k_eqv_FF

Source: proofs/CANONF1.lean:666 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_FF (s : Stmt) : Relation.EqvGen ForStep s (KFF s)
~~~

### 445. k_lift

Source: proofs/CANONF1.lean:669 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_lift {k : ℕ} {ret : AExp} {body body' : Stmt} (h : Relation.EqvGen ForStep body body') : SynEquiv ⟨k, body, ret⟩ ⟨k, body', ret⟩
~~~

### 446. k_adm_canonMap

Source: proofs/CANONF1.lean:677 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_adm_canonMap (d : Prog) : Admissible d.canonMap d
~~~

### 447. k_syn_canon

Source: proofs/CANONF1.lean:693 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_syn_canon (p : Prog) : SynEquiv p (canon p)
~~~

### 448. k_part2

Source: proofs/CANONF1.lean:697 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_part2 (p q : Prog) : canon p = canon q ↔ SynEquiv p q
~~~

### 449. k_runs_step

Source: proofs/CANONF1.lean:705 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_runs_step {p q : Prog} (h : Step p q) (ins : List ℤ) (out : ℤ) : Runs p ins out ↔ Runs q ins out
~~~

### 450. k_runs_syn

Source: proofs/CANONF1.lean:714 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_runs_syn {p q : Prog} (h : SynEquiv p q) (ins : List ℤ) (out : ℤ) : Runs p ins out ↔ Runs q ins out
~~~

### 451. k_part1

Source: proofs/CANONF1.lean:722 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_part1 (p : Prog) (ins : List ℤ) (out : ℤ) : Runs (canon p) ins out ↔ Runs p ins out
~~~

### 452. claim

Source: proofs/CANONF1.lean:725 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 453. witness

Source: proofs/CANONF1.lean:741 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## proofs/SANDBOX2F1.lean

### 454. fp2_split1

Source: proofs/SANDBOX2F1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fp2_split1 (W : Path) (sd : List Path) : PL_SANDBOX2F1.fixedPolicy2 W sd = [.bind [] [] .ro] ++ ([.tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++ sd.map (fun d => .bind d d .rw) ++ hiddenDirs.map .tmpfs ++ [.bind mathlibProj mathlibProj .ro])
~~~

### 455. fp2_split2

Source: proofs/SANDBOX2F1.lean:10 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fp2_split2 (W : Path) (sd : List Path) : PL_SANDBOX2F1.fixedPolicy2 W sd = ([.bind [] [] .ro, .tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++ sd.map (fun d => .bind d d .rw)) ++ (hiddenDirs.map .tmpfs ++ [.bind mathlibProj mathlibProj .ro])
~~~

### 456. part_a

Source: proofs/SANDBOX2F1.lean:16 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_a : ∀ W : Path, ["var", "tmp"] <+: W → ReadsHost (fixedPolicy W [home ++ [".agent-b"]]) (home ++ [".agent-b", "sessions", "s.jsonl"]) (home ++ [".agent-b", "sessions", "s.jsonl"])
~~~

### 457. part_b

Source: proofs/SANDBOX2F1.lean:24 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_b : ∀ (W : Path) (stateDirs : List Path) (canWrite : Path → Prop) (p hp : Path), WritesHost (PL_SANDBOX2F1.fixedPolicy2 W stateDirs) canWrite p hp → W <+: hp ∨ ∃ d ∈ stateDirs, d <+: hp
~~~

### 458. part_c

Source: proofs/SANDBOX2F1.lean:34 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c : ∀ (W : Path) (stateDirs : List Path) (p hp H : Path), ["var", "tmp"] <+: W → H ∈ hiddenDirs → H <+: hp → ReadsHost (PL_SANDBOX2F1.fixedPolicy2 W stateDirs) p hp → mathlibProj <+: hp
~~~

### 459. claim

Source: proofs/SANDBOX2F1.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_SANDBOX2F1.Claim
~~~

### 460. witness

Source: proofs/SANDBOX2F1.lean:66 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_SANDBOX2F1.Witness
~~~

## proofs/SANDBOXF1.lean

### 461. eff_mem

Source: proofs/SANDBOXF1.lean:1 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem eff_mem {pol : Policy} {p : Path} {m : Mount} (h : effective pol p = some m) : m ∈ pol ∧ m.tgt <+: p
~~~

### 462. eff_tail

Source: proofs/SANDBOXF1.lean:6 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem eff_tail {l1 l2 : Policy} {p : Path} {m x : Mount} (h : effective (l1 ++ l2) p = some m) (hx : x ∈ l2) (hP : x.tgt <+: p) : m ∈ l2
~~~

### 463. head_eq

Source: proofs/SANDBOXF1.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem head_eq {a b : String} {as bs l : Path} (h1 : a :: as <+: l) (h2 : b :: bs <+: l) : a = b
~~~

### 464. hidden_head

Source: proofs/SANDBOXF1.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hidden_head : ∀ H ∈ hiddenDirs, ∃ as, H = "home" :: as ∨ H = "tmp" :: as
~~~

### 465. cur_split

Source: proofs/SANDBOXF1.lean:33 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cur_split (W : Path) : currentPolicy W = [.bind [] [] .rw] ++ ([.tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++ hiddenDirs.map .tmpfs ++ [.bind mathlibProj mathlibProj .ro])
~~~

### 466. claim_a

Source: proofs/SANDBOXF1.lean:38 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_a : ∀ W : Path, ["var", "tmp"] <+: W → WritesHost (currentPolicy W) (fun hp => home <+: hp ∨ ["var", "tmp"] <+: hp) (home ++ [".toolchain", "bin", "lake"]) (home ++ [".toolchain", "bin", "lake"])
~~~

### 467. claim_b

Source: proofs/SANDBOXF1.lean:47 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_b : ∀ (W : Path) (stateDirs : List Path) (canWrite : Path → Prop) (p hp : Path), WritesHost (fixedPolicy W stateDirs) canWrite p hp → W <+: hp ∨ ∃ d ∈ stateDirs, d <+: hp
~~~

### 468. claim_c

Source: proofs/SANDBOXF1.lean:57 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_c : ∀ (W p hp H : Path), ["var", "tmp"] <+: W → H ∈ hiddenDirs → H <+: hp → ReadsHost (currentPolicy W) p hp → mathlibProj <+: hp
~~~

### 469. claim

Source: proofs/SANDBOXF1.lean:81 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 470. witness

Source: proofs/SANDBOXF1.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## proofs/TMCERTF1.lean

### 471. claimS

Source: proofs/TMCERTF1.lean:2 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimS : ∀ (S A Θ : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ) (σ : RHist S A → S → A → ℝ) (θ : ℕ → RHist S A → S → A → Θ), AdmKNonneg N G adm → RiskCertUpTo N G adm V → IsPolicy σ → SelectorUpTo N adm θ → ∀ n, n ≤ N → ∀ s h, risk G θ σ n s h ≤ V n s
~~~

### 472. claimP

Source: proofs/TMCERTF1.lean:29 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimP : ∀ (S A Θ : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (σ : RHist S A → S → A → ℝ) (θ : ℕ → RHist S A → S → A → Θ), (∀ n, n < N → ∀ s a th, adm n s a th → 0 ≤ (G th).cat n s a ∧ (∀ s', 0 ≤ (G th).K n s a s') ∧ (G th).cat n s a + ∑ s', (G th).K n s a s' ≤ 1) → IsPolicy σ → SelectorUpTo N adm θ → ∀ n, n ≤ N → ∀ s h, 0 ≤ risk G θ σ n s h ∧ risk G θ σ n s h ≤ 1
~~~

### 473. claimS

Source: proofs/TMCERTF1.lean:63 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimS' : ∀ (S A Θ Ω : Type) [Fintype S] [Fintype A] [Fintype Ω] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ) (ρ : Ω → ℝ) (σ : Ω → RHist S A → S → A → ℝ) (θ : Ω → ℕ → RHist S A → S → A → Θ) (s₀ : S), AdmKNonneg N G adm → RiskCertUpTo N G adm V → (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, IsPolicy (σ ω)) → (∀ ω, SelectorUpTo N adm (θ ω)) → ∑ ω, ρ ω * risk G (θ ω) (σ ω) N s₀ [] ≤ V N s₀
~~~

### 474. claimFx

Source: proofs/TMCERTF1.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimFx : ∀ (S A : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Game S A) (V : ℕ → S → ℝ) (σ : RHist S A → S → A → ℝ) (s₀ : S), (∀ n, n < N → ∀ s a s', 0 ≤ G.K n s a s') → RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V → IsPolicy σ → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ N s₀ [] ≤ V N s₀
~~~

### 475. claimFxGap

Source: proofs/TMCERTF1.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimFxGap : risk (fun _ : Unit => gapG true) (fun _ _ _ _ => ()) (fun _ _ _ => 1) 2 () [] = 1/2 ∧ risk (fun _ : Unit => gapG false) (fun _ _ _ _ => ()) (fun _ _ _ => 1) 2 () [] = 1/2 ∧ risk gapG (fun n _ _ _ => decide (n = 1)) (fun _ _ _ => 1) 2 () [] = 3/4
~~~

### 476. claimObs

Source: proofs/TMCERTF1.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimObs : ∀ (S A O : Type) [Fintype A] (obs : RHist S A → S → O) (π : O → A → ℝ), (∀ o, (∀ a, 0 ≤ π o a) ∧ ∑ a, π o a = 1) → IsPolicy (liftObs obs π)
~~~

### 477. claimT

Source: proofs/TMCERTF1.lean:97 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimT : ∀ (S A : Type) [Fintype S] [Fintype A] [Nonempty A] (G : Game S A), Lawful G → (∀ N, RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) (Vstar G)) ∧ (∀ N V, RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V → ∀ n, n ≤ N → ∀ s, Vstar G n s ≤ V n s) ∧ (∀ n s, 0 ≤ Vstar G n s ∧ Vstar G n s ≤ 1) ∧ ∀ (N : ℕ) (s₀ : S), ∃ σ, IsPolicy σ ∧ (∀ h s a, σ h s a = 0 ∨ σ h s a = 1) ∧ (∀ h h' s, h.length = h'.length → σ h s = σ h' s) ∧ risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ N s₀ [] = Vstar G N s₀
~~~

### 478. claimTR

Source: proofs/TMCERTF1.lean:192 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimTR : ∀ (S A Θ : Type) [Fintype S] [Fintype A] [Fintype Θ] [Nonempty A] [Nonempty Θ] (G : Θ → Game S A), (∀ th, Lawful (G th)) → (∀ N, RiskCertUpTo N G (fun _ _ _ _ => True) (Vrob G)) ∧ (∀ N V, RiskCertUpTo N G (fun _ _ _ _ => True) V → ∀ n, n ≤ N → ∀ s, Vrob G n s ≤ V n s) ∧ ∀ (N : ℕ) (s₀ : S), ∃ σ θ, IsPolicy σ ∧ (∀ h s a, σ h s a = 0 ∨ σ h s a = 1) ∧ (∀ h h' s, h.length = h'.length → σ h s = σ h' s) ∧ (∀ n h h' s a, h.length = h'.length → θ n h s a = θ n h' s a) ∧ risk G θ σ N s₀ [] = Vrob G N s₀
~~~

### 479. claimU

Source: proofs/TMCERTF1.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimU : ∀ (S A Θ : Type) [Fintype S] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (a₀ : A) (rew : Θ → ℕ → S → ℝ) (W : ℕ → S → ℝ) (θ : ℕ → RHist S A → S → Θ), (∀ n, n < N → ∀ s th, adm n s a₀ th → ∀ s', 0 ≤ (G th).K n s a₀ s') → UseCertUpTo N G adm a₀ rew W → (∀ n, n < N → ∀ h s, adm n s a₀ (θ n h s)) → ∀ n, n ≤ N → ∀ s h, W n s ≤ honestER G a₀ rew θ n s h
~~~

### 480. foldl_add_eq

Source: proofs/TMCERTF1.lean:288 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_add_eq {m : ℕ} (f : Fin m → ℚ) : ∀ (l : List (Fin m)) (acc : ℚ), l.foldl (fun acc i => acc + f i) acc = acc + (l.map f).sum
~~~

### 481. sumQ_eq

Source: proofs/TMCERTF1.lean:298 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sumQ_eq (m : ℕ) (f : Fin m → ℚ) : sumQ m f = ∑ i, f i
~~~

### 482. checkRiskQ_spec

Source: proofs/TMCERTF1.lean:301 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkRiskQ_spec {N m k t : ℕ} {cat : Fin t → Fin N → Fin m → Fin k → ℚ} {K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ} {V : Fin (N + 1) → Fin m → ℚ} (hc : checkRiskQ N m k t cat K V = true) : 0 < t ∧ 0 < k ∧ (∀ j s, 0 ≤ V j s) ∧ (∀ th i s a, cat th i s a + ∑ s', K th i s a s' * V i.castSucc s' ≤ V i.succ s)
~~~

### 483. checkLawfulQ_spec

Source: proofs/TMCERTF1.lean:310 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkLawfulQ_spec {N m k t : ℕ} {cat : Fin t → Fin N → Fin m → Fin k → ℚ} {K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ} (hc : checkLawfulQ N m k t cat K = true) : ∀ th i s a, 0 ≤ cat th i s a ∧ (∀ s', 0 ≤ K th i s a s') ∧ cat th i s a + ∑ s', K th i s a s' ≤ 1
~~~

### 484. claimQ

Source: proofs/TMCERTF1.lean:319 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimQ : ∀ (N m k t : ℕ) (cat : Fin t → Fin N → Fin m → Fin k → ℚ) (K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ) (V : Fin (N + 1) → Fin m → ℚ), (checkRiskQ N m k t cat K V = true → RiskCertUpTo N (gameOfQ N m k t cat K) (fun _ _ _ _ => True) (valOfQ N m V) ∧ (∀ n s, 0 ≤ valOfQ N m V n s) ∧ 0 < t ∧ 0 < k) ∧ (checkLawfulQ N m k t cat K = true → ∀ th, Lawful (gameOfQ N m k t cat K th))
~~~

### 485. claimVx

Source: proofs/TMCERTF1.lean:350 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimVx : ∀ (S A ι : Type) [Fintype S] [Fintype ι] (N : ℕ) (Gv : ι → Game S A) (V : ℕ → S → ℝ), RiskCertUpTo N Gv (fun _ _ _ _ => True) V → RiskCertUpTo N (hullGame Gv) (fun _ _ _ lam => Simplex lam) V ∧ ((∀ i n s a s', 0 ≤ (Gv i).K n s a s') → ∀ n s a lam, Simplex lam → ∀ s', 0 ≤ (hullGame Gv lam).K n s a s')
~~~

### 486. claimAbsV

Source: proofs/TMCERTF1.lean:374 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimAbsV : ∀ (Sc Ac S A Θ : Type) [Fintype Sc] [Fintype Ac] [Fintype S] (N : ℕ) (Gc : Game Sc Ac) (α : Sc → S) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ) (σc : RHist Sc Ac → Sc → Ac → ℝ), (∀ n, n < N → ∀ x ac x', 0 ≤ Gc.K n x ac x') → CoveredV N Gc α G adm V → RiskCertUpTo N G adm V → IsPolicy σc → ∀ n, n ≤ N → ∀ x h, risk (fun _ : Unit => Gc) (fun _ _ _ _ => ()) σc n x h ≤ V n (α x)
~~~

### 487. claimAbsEq

Source: proofs/TMCERTF1.lean:400 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimAbsEq : ∀ (Sc Ac S A Θ : Type) [Fintype Sc] [Fintype S] [DecidableEq S] (N : ℕ) (Gc : Game Sc Ac) (α : Sc → S) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ), Covered N Gc α G adm → CoveredV N Gc α G adm V
~~~

### 488. claim

Source: proofs/TMCERTF1.lean:417 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_TMCERTF1.Claim
~~~

### 489. witness

Source: proofs/TMCERTF1.lean:421 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_TMCERTF1.Witness
~~~

## proofs/TMCERTUSF1.lean

### 490. foldl_add_eq

Source: proofs/TMCERTUSF1.lean:1 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_add_eq {m : ℕ} (f : Fin m → ℚ) : ∀ (l : List (Fin m)) (acc : ℚ), l.foldl (fun acc i => acc + f i) acc = acc + (l.map f).sum
~~~

### 491. sumQ_eq

Source: proofs/TMCERTUSF1.lean:8 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sumQ_eq (m : ℕ) (f : Fin m → ℚ) : sumQ m f = ∑ i, f i
~~~

### 492. checkUseQ_spec

Source: proofs/TMCERTUSF1.lean:11 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkUseQ_spec {N m t : ℕ} {rew : Fin t → Fin N → Fin m → ℚ} {K : Fin t → Fin N → Fin m → Fin m → ℚ} {adm : Fin t → Fin N → Fin m → Bool} {W : Fin (N + 1) → Fin m → ℚ} {s₀ : Fin m} {floor : ℚ} (hc : checkUseQ N m t rew K adm W s₀ floor = true) : 0 < t ∧ floor ≤ W (Fin.last N) s₀ ∧ (∀ s, W 0 s ≤ 0) ∧ (∀ i s, ∃ th, adm th i s = true) ∧ (∀ th i s, adm th i s = true → W i.succ s ≤ rew th i s + ∑ s', K th i s s' * W i.castSucc s')
~~~

### 493. selector_exists

Source: proofs/TMCERTUSF1.lean:29 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem selector_exists {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ) (K : Fin t → Fin N → Fin m → Fin m → ℚ) (adm : Fin t → Fin N → Fin m → Bool) (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ) (hc : checkUseQ N m t rew K adm W s₀ floor = true) : ∃ θ : ℕ → List (Fin m) → Fin m → Fin t, ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true
~~~

### 494. checkUseQ_sound

Source: proofs/TMCERTUSF1.lean:45 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkUseQ_sound {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ) (K : Fin t → Fin N → Fin m → Fin m → ℚ) (adm : Fin t → Fin N → Fin m → Bool) (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ) (θ : ℕ → List (Fin m) → Fin m → Fin t) (hc : checkUseQ N m t rew K adm W s₀ floor = true) (hK : ∀ th i s, adm th i s = true → ∀ s', 0 ≤ K th i s s') (hθ : ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true) : (floor : ℝ) ≤ PL_TMCERTUSF1.honestValue rew K θ N s₀ []
~~~

### 495. claim

Source: proofs/TMCERTUSF1.lean:98 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_TMCERTUSF1.Claim
~~~

### 496. witness

Source: proofs/TMCERTUSF1.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_TMCERTUSF1.Witness
~~~

## proofs/TMGACF1.lean

### 497. risk_zero

Source: proofs/TMGACF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_zero' {S A Θ : Type} [Fintype S] [Fintype A] (G : Θ → Game S A) (θ : ℕ → RHist S A → S → A → Θ) (σ : RHist S A → S → A → ℝ) (s : S) (h : RHist S A) : risk G θ σ 0 s h = 0
~~~

### 498. risk_succ_bool

Source: proofs/TMGACF1.lean:10 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_succ_bool {S : Type} [Fintype S] (G : Game S Bool) (σ : RHist S Bool → S → Bool → ℝ) (n : ℕ) (s : S) (h : RHist S Bool) : risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ (n + 1) s h = σ h s true * (G.cat n s true + ∑ s', G.K n s true s' * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' (h ++ [(s, true)])) + σ h s false * (G.cat n s false + ∑ s', G.K n s false s' * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' (h ++ [(s, false)]))
~~~

### 499. risk_hist

Source: proofs/TMGACF1.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_hist {S A : Type} [Fintype S] [Fintype A] (G : Game S A) (σ : RHist S A → S → A → ℝ) (hσ : ∀ h s a, σ h s a = σ [] s a) : ∀ n s h, risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s h = risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s []
~~~

### 500. risk_succ_hf

Source: proofs/TMGACF1.lean:35 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_succ_hf {S : Type} [Fintype S] (G : Game S Bool) (σ : RHist S Bool → S → Bool → ℝ) (hσ : ∀ h s a, σ h s a = σ [] s a) (n : ℕ) (s : S) (h : RHist S Bool) : risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ (n + 1) s h = σ [] s true * (G.cat n s true + ∑ s', G.K n s true s' * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' []) + σ [] s false * (G.cat n s false + ∑ s', G.K n s false s' * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' [])
~~~

### 501. honestER_hist

Source: proofs/TMGACF1.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honestER_hist {S A : Type} [Fintype S] (G : Game S A) (a₀ : A) (rew : Unit → ℕ → S → ℝ) : ∀ n s h, honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) n s h = honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) n s []
~~~

### 502. honestER_succ_hf

Source: proofs/TMGACF1.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honestER_succ_hf {S A : Type} [Fintype S] (G : Game S A) (a₀ : A) (rew : Unit → ℕ → S → ℝ) (n : ℕ) (s : S) (h : RHist S A) : honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) (n + 1) s h = rew () n s + ∑ s', G.K n s a₀ s' * honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) n s' []
~~~

### 503. sup'_bool

Source: proofs/TMGACF1.lean:69 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sup'_bool (g : Bool → ℝ) : (Finset.univ : Finset Bool).sup' Finset.univ_nonempty g = max (g true) (g false)
~~~

### 504. Vstar_succ_bool

Source: proofs/TMGACF1.lean:79 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Vstar_succ_bool {S : Type} [Fintype S] (G : Game S Bool) (n : ℕ) (s : S) : Vstar G (n + 1) s = max (G.cat n s true + ∑ s', G.K n s true s' * Vstar G n s') (G.cat n s false + ∑ s', G.K n s false s' * Vstar G n s')
~~~

### 505. constRed_t

Source: proofs/TMGACF1.lean:84 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem constRed_t {S : Type} (β : ℝ) (h : RHist S Bool) (s : S) : constRed β h s true = β
~~~

### 506. constRed_f

Source: proofs/TMGACF1.lean:85 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem constRed_f {S : Type} (β : ℝ) (h : RHist S Bool) (s : S) : constRed β h s false = 1 - β
~~~

### 507. gac_cat_true

Source: proofs/TMGACF1.lean:89 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_cat_true (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) : (gac C TA TD FA).cat n c true = (if 0 < c.val then 1 - TD n c.val else 1 - TD n c.val + TA n c.val)
~~~

### 508. gac_cat_false

Source: proofs/TMGACF1.lean:93 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_cat_false (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) : (gac C TA TD FA).cat n c false = 0
~~~

### 509. gac_sum_true

Source: proofs/TMGACF1.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_sum_true (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) (F : Fin (C + 1) → ℝ) : ∑ c', (gac C TA TD FA).K n c true c' * F c' = (TD n c.val - TA n c.val) * F c
~~~

### 510. gac_sum_false_zero

Source: proofs/TMGACF1.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_sum_false_zero (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) (hc : c.val = 0) (F : Fin (C + 1) → ℝ) : ∑ c', (gac C TA TD FA).K n c false c' * F c' = F c
~~~

### 511. gac_sum_false_succ

Source: proofs/TMGACF1.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_sum_false_succ (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n k : ℕ) (hk : k + 1 < C + 1) (F : Fin (C + 1) → ℝ) : ∑ c', (gac C TA TD FA).K n ⟨k + 1, hk⟩ false c' * F c' = FA n (k + 1) * F ⟨k, by omega⟩ + (1 - FA n (k + 1)) * F ⟨k + 1, hk⟩
~~~

### 512. conjL

Source: proofs/TMGACF1.lean:130 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjL : ∀ (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ), (∀ n c, 0 ≤ TA n c ∧ TA n c ≤ TD n c ∧ TD n c ≤ 1 ∧ 0 ≤ FA n c ∧ FA n c ≤ 1) → Lawful (gac C TA TD FA)
~~~

### 513. conjLQ

Source: proofs/TMGACF1.lean:159 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjLQ : ∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ), (∀ m c, 0 ≤ qa m c ∧ qa m c ≤ qd m c ∧ qd m c ≤ 1 ∧ 0 ≤ f (qa m c) ∧ f (qa m c) ≤ f (qd m c) ∧ f (qd m c) ≤ 1) → Lawful (gacQ C f qa qd)
~~~

### 514. conjZ

Source: proofs/TMGACF1.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjZ : ∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (β : ℝ), f 0 = 0 → (∀ m, qa m 0 = 0) → ∀ (m : ℕ) (c : Fin (C + 1)), 1 - risk (fun _ : Unit => gacQ C f qa qd) (fun _ _ _ _ => ()) (constRed β) m c [] = zGAC f qa qd β m c.val
~~~

### 515. conjUZ

Source: proofs/TMGACF1.lean:201 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjUZ : ∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (m : ℕ) (c : Fin (C + 1)), honestER (fun _ : Unit => gacQ C f qa qd) false (fun _ n c => usedReward qa qd n c.val) (fun _ _ _ => ()) m c [] = uGAC qa qd m c.val
~~~

### 516. conjM

Source: proofs/TMGACF1.lean:226 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjM : ∀ (S Ω : Type) [Fintype S] [Fintype Ω] (G : Game S Bool) (ρ : Ω → ℝ) (β : Ω → ℝ) (N : ℕ) (s₀ : S) (U : ℝ), (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, 0 ≤ β ω ∧ β ω ≤ 1) → (∀ b : ℝ, 0 ≤ b → b ≤ 1 → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] ≤ U) → ∑ ω, ρ ω * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed (β ω)) N s₀ [] ≤ U
~~~

### 517. rowval_bounds

Source: proofs/TMGACF1.lean:239 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rowval_bounds {S : Type} [Fintype S] (G : Game S Bool) (hG : Lawful G) (n : ℕ) (s : S) (a : Bool) (F : S → ℝ) (hF : ∀ s, 0 ≤ F s ∧ F s ≤ 1) : 0 ≤ G.cat n s a + ∑ s', G.K n s a s' * F s' ∧ G.cat n s a + ∑ s', G.K n s a s' * F s' ≤ 1
~~~

### 518. risk_const_bounds

Source: proofs/TMGACF1.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_const_bounds {S : Type} [Fintype S] (G : Game S Bool) (hG : Lawful G) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : ∀ n s, 0 ≤ risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) n s [] ∧ risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) n s [] ≤ 1
~~~

### 519. rowval_diff

Source: proofs/TMGACF1.lean:267 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rowval_diff {S : Type} [Fintype S] (G : Game S Bool) (hG : Lawful G) (n : ℕ) (s : S) (a : Bool) (F1 F2 : S → ℝ) (e : ℝ) (he : 0 ≤ e) (hF : ∀ s, |F1 s - F2 s| ≤ e) : |(G.cat n s a + ∑ s', G.K n s a s' * F1 s') - (G.cat n s a + ∑ s', G.K n s a s' * F2 s')| ≤ e
~~~

### 520. lip_comb

Source: proofs/TMGACF1.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lip_comb (b b' X Y X' Y' e : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hX0 : 0 ≤ X') (hX1 : X' ≤ 1) (hY0 : 0 ≤ Y') (hY1 : Y' ≤ 1) (hXX : |X - X'| ≤ e) (hYY : |Y - Y'| ≤ e) : |b * X + (1 - b) * Y - (b' * X' + (1 - b') * Y')| ≤ e + |b - b'|
~~~

### 521. conjLip

Source: proofs/TMGACF1.lean:303 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjLip : ∀ (S : Type) [Fintype S] (G : Game S Bool) (N : ℕ) (s₀ : S) (b b' : ℝ), Lawful G → 0 ≤ b → b ≤ 1 → 0 ≤ b' → b' ≤ 1 → |risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] - risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b') N s₀ []| ≤ N * |b - b'|
~~~

### 522. conjGrid

Source: proofs/TMGACF1.lean:329 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjGrid : ∀ (S : Type) [Fintype S] (G : Game S Bool) (N J : ℕ) (s₀ : S) (U : ℝ), Lawful G → 0 < J → (∀ j : ℕ, j ≤ J → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed ((j : ℝ) / J)) N s₀ [] ≤ U) → ∀ b : ℝ, 0 ≤ b → b ≤ 1 → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] ≤ U + N / (2 * J)
~~~

### 523. Vstar_zero

Source: proofs/TMGACF1.lean:364 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Vstar_zero' {S A : Type} [Fintype S] [Fintype A] [Nonempty A] (G : Game S A) (s : S) : Vstar G 0 s = 0
~~~

### 524. conjW

Source: proofs/TMGACF1.lean:368 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjW : ∀ (TA TD FA : ℕ → ℕ → ℝ), (∀ n c, 0 ≤ TA n c ∧ TA n c ≤ TD n c ∧ TD n c ≤ 1 ∧ 0 ≤ FA n c ∧ FA n c ≤ 1) → ∀ (N : ℕ) (c : Fin 1), risk (fun _ : Unit => gac 0 TA TD FA) (fun _ _ _ _ => ()) (constRed 1) N c [] = Vstar (gac 0 TA TD FA) N c
~~~

### 525. ex_row0t

Source: proofs/TMGACF1.lean:399 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_row0t (n : ℕ) (F : Fin 2 → ℝ) : exG3.cat n 0 true + ∑ s', exG3.K n 0 true s' * F s' = 1/4 + 3/4 * F 0
~~~

### 526. ex_row0f

Source: proofs/TMGACF1.lean:404 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_row0f (n : ℕ) (F : Fin 2 → ℝ) : exG3.cat n 0 false + ∑ s', exG3.K n 0 false s' * F s' = F 0
~~~

### 527. ex_row1t

Source: proofs/TMGACF1.lean:408 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_row1t (n : ℕ) (F : Fin 2 → ℝ) : exG3.cat n 1 true + ∑ s', exG3.K n 1 true s' * F s' = 1/4
~~~

### 528. ex_row1f

Source: proofs/TMGACF1.lean:413 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_row1f (n : ℕ) (F : Fin 2 → ℝ) : exG3.cat n 1 false + ∑ s', exG3.K n 1 false s' * F s' = 1/2 * F 0 + 1/2 * F 1
~~~

### 529. ex_step0

Source: proofs/TMGACF1.lean:418 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_step0 (σ : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ) (n : ℕ) (h : RHist (Fin 2) Bool) : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ (n + 1) 0 h = σ h 0 true * (1/4 + 3/4 * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 0 (h ++ [(0, true)])) + σ h 0 false * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 0 (h ++ [(0, false)])
~~~

### 530. ex_step1

Source: proofs/TMGACF1.lean:424 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_step1 (σ : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ) (n : ℕ) (h : RHist (Fin 2) Bool) : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ (n + 1) 1 h = σ h 1 true * (1/4) + σ h 1 false * (1/2 * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 0 (h ++ [(1, false)]) + 1/2 * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 1 (h ++ [(1, false)]))
~~~

### 531. ex_V0

Source: proofs/TMGACF1.lean:431 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_V0 (n : ℕ) : Vstar exG3 (n + 1) 0 = max (1/4 + 3/4 * Vstar exG3 n 0) (Vstar exG3 n 0)
~~~

### 532. ex_V1

Source: proofs/TMGACF1.lean:434 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_V1 (n : ℕ) : Vstar exG3 (n + 1) 1 = max (1/4) (1/2 * Vstar exG3 n 0 + 1/2 * Vstar exG3 n 1)
~~~

### 533. ex_poly

Source: proofs/TMGACF1.lean:438 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_poly (b : ℝ) : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed b) 3 1 [] = 3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3
~~~

### 534. ex_clocked

Source: proofs/TMGACF1.lean:444 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_clocked : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) clocked3 3 1 [] = 11/32
~~~

### 535. ex_coin

Source: proofs/TMGACF1.lean:448 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_coin : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) coinRed 3 1 [] = 9/32
~~~

### 536. ex_Vstar

Source: proofs/TMGACF1.lean:452 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_Vstar : Vstar exG3 3 1 = 11/32
~~~

### 537. conjT5

Source: proofs/TMGACF1.lean:463 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjT5 : (∀ b : ℝ, 0 ≤ b → b ≤ 1 → risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed b) 3 1 [] = 3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3 ∧ 3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3 ≤ 13/50) ∧ risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed (4/5)) 3 1 [] = 13/50 ∧ IsPolicy clocked3 ∧ IsPolicy coinRed ∧ risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) coinRed 3 1 [] = 9/32 ∧ (13/50 : ℝ) < 9/32 ∧ risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) clocked3 3 1 [] = 11/32 ∧ Vstar exG3 3 1 = 11/32 ∧ (13/50 : ℝ) < 11/32
~~~

### 538. sound_unit

Source: proofs/TMGACF1.lean:497 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sound_unit {S A : Type} [Fintype S] [Fintype A] (G : Game S A) (N : ℕ) (V : ℕ → S → ℝ) (σ : RHist S A → S → A → ℝ) (hK : ∀ n, n < N → ∀ s a s', 0 ≤ G.K n s a s') (hV : RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V) (hσ : IsPolicy σ) : ∀ n, n ≤ N → ∀ s h, risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s h ≤ V n s
~~~

### 539. claim

Source: proofs/TMGACF1.lean:516 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_TMGACF1.Claim
~~~

### 540. witness

Source: proofs/TMGACF1.lean:519 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_TMGACF1.Witness
~~~

## proofs/TMLIPF1.lean

### 541. oneStep

Source: proofs/TMLIPF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem oneStep : OneStep
~~~

### 542. transfer

Source: proofs/TMLIPF1.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem transfer : Transfer
~~~

### 543. gridTransfer

Source: proofs/TMLIPF1.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gridTransfer : GridTransfer
~~~

### 544. gridRisk

Source: proofs/TMLIPF1.lean:125 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gridRisk : GridRisk
~~~

### 545. claim

Source: proofs/TMLIPF1.lean:132 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_TMLIPF1.Claim
~~~

### 546. w_lawfulParam

Source: proofs/TMLIPF1.lean:134 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_lawfulParam : ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), LawfulUpTo 1 (paramGame p)
~~~

### 547. w_cover

Source: proofs/TMLIPF1.lean:141 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_cover : ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ q ∈ pGrid, |p - q| ≤ 1 / 8
~~~

### 548. w_lip

Source: proofs/TMLIPF1.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_lip : ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ q ∈ pGrid, RowClose 1 (paramGame q) (paramGame p) (2 * |p - q|)
~~~

### 549. w_gridCert

Source: proofs/TMLIPF1.lean:157 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_gridCert : ∀ q ∈ pGrid, RiskCertUpTo 1 (fun _ : Unit => paramGame q) (fun _ _ _ _ => True) (gridCert q) ∧ InRange 1 (gridCert q) ∧ ∀ s, gridCert q 1 s ≤ 3 / 8
~~~

### 550. witness

Source: proofs/TMLIPF1.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_TMLIPF1.Witness
~~~

## proofs/UMADAPTF1.lean

### 551. adSurv_zero

Source: proofs/UMADAPTF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_zero' {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (h : Hist X Z) : adSurv T M φ keep 0 h = keep h
~~~

### 552. adSurv_succ

Source: proofs/UMADAPTF1.lean:10 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_succ' {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ) (h : Hist X Z) : adSurv T M φ keep (n + 1) h = ∑ x, T h x * ∑ z, M x z * (φ z * adSurv T M φ keep n (h ++ [(x, z, true)]) + (1 - φ z) * adSurv T M φ keep n (h ++ [(x, z, false)]))
~~~

### 553. s_aux

Source: proofs/UMADAPTF1.lean:18 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem s_aux {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hk : ∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) : ∀ (n : ℕ) (h : Hist X Z), (∀ e ∈ h, e.2.2 = false) → adSurv T M (fun _ => 0) keep n h = 1
~~~

### 554. part_s

Source: proofs/UMADAPTF1.lean:39 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_s : ∀ (X Z : Type) [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ), IsKernel M → (∀ h, IsDist (T h)) → (∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) → AcceptsAllFlag T M keep n
~~~

### 555. surv_bounds

Source: proofs/UMADAPTF1.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_bounds {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hφ : IsRule φ) (hk : ∀ h, 0 ≤ keep h ∧ keep h ≤ 1) : ∀ (n : ℕ) (h : Hist X Z), 0 ≤ adSurv T M φ keep n h ∧ adSurv T M φ keep n h ≤ 1
~~~

### 556. Qf_zero

Source: proofs/UMADAPTF1.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_zero {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (h : Hist X Z) : Qf T M w 0 h = 0
~~~

### 557. Qf_succ

Source: proofs/UMADAPTF1.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_succ {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (n : ℕ) (h : Hist X Z) : Qf T M w (n + 1) h = ∑ x, T h x * ∑ z, M x z * (w z + Qf T M w n (h ++ [(x, z, false)]))
~~~

### 558. Qf_nonneg

Source: proofs/UMADAPTF1.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_nonneg {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hw : ∀ z, 0 ≤ w z) : ∀ (n : ℕ) (h : Hist X Z), 0 ≤ Qf T M w n h
~~~

### 559. sum2_add

Source: proofs/UMADAPTF1.lean:105 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum2_add {X Z : Type} [Fintype X] [Fintype Z] (a : X → ℝ) (m : X → Z → ℝ) (f g : X → Z → ℝ) (t : ℝ) : ∑ x, a x * ∑ z, m x z * f x z + t * ∑ x, a x * ∑ z, m x z * g x z = ∑ x, a x * ∑ z, m x z * (f x z + t * g x z)
~~~

### 560. ref_lb

Source: proofs/UMADAPTF1.lean:116 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ref_lb {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ w : Z → ℝ) (t : ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hk : ∀ h, 0 ≤ keep h ∧ keep h ≤ 1) (hφ : IsRule φ) (hw : ∀ z, 0 ≤ w z) (ht : 0 ≤ t) (hφw : ∀ z, φ z ≤ t * w z) : ∀ (n : ℕ) (h : Hist X Z), adSurv T M (fun _ => 0) keep n h - t * Qf T M w n h ≤ adSurv T M φ keep n h
~~~

### 561. Q_sum_le

Source: proofs/UMADAPTF1.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Q_sum_le {X Z Ω : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (S : Finset Ω) (w : Ω → Z → ℝ) (hw1 : ∀ z, ∑ ω ∈ S, w ω z ≤ 1) : ∀ (n : ℕ) (h : Hist X Z), ∑ ω ∈ S, Qf T M (w ω) n h ≤ n
~~~

### 562. ind_sum_le

Source: proofs/UMADAPTF1.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ind_sum_le {X Z C : Type} [DecidableEq C] (c : X → C) (g : Z → C) (S : Finset X) (hinj : Set.InjOn c (S : Set X)) (z : Z) : ∑ ω ∈ S, (if g z = c ω then (1 : ℝ) else 0) ≤ 1
~~~

### 563. classRule_rule

Source: proofs/UMADAPTF1.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classRule_rule {X Z C : Type} [DecidableEq C] (c : X → C) (g : Z → C) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ω : X) : IsRule (classRule c g t ω)
~~~

### 564. conv_a

Source: proofs/UMADAPTF1.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conv_a {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X) (hM : IsKernel M) (hbad : ∀ x ∈ S, Bad x) (hinj : Set.InjOn c (S : Set X)) (hS : 0 < S.card) (g : Z → C) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ) (hTk : AdTester T keep) (hacc : AcceptsAllFlag T M keep n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (r : ℝ) (b N : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hN : 1 ≤ N) : t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z
~~~

### 565. opt_arith

Source: proofs/UMADAPTF1.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem opt_arith (k n : ℝ) (hk : 0 < k) (hn : 1 ≤ n) : min (1 / 2) (k / (4 * n)) ≤ min 1 (k / (2 * n)) * max 0 (1 - min 1 (k / (2 * n)) * n / k)
~~~

### 566. part_a

Source: proofs/UMADAPTF1.lean:288 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_a : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X), Setup Bad M c S → ∃ g : Z → C, (∀ x z, M x z ≠ 0 → g z = c x) ∧ (∀ (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ), AdTester T keep → AcceptsAllFlag T M keep n → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N → t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z
~~~

### 567. adSurv_det

Source: proofs/UMADAPTF1.lean:321 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_det {X : Type} [Fintype X] [DecidableEq X] (T : Hist X X → X → ℝ) (M : X → X → ℝ) (q : Hist X X → X) (hT : ∀ h x, T h x = if x = q h then 1 else 0) (hM : ∀ x z, M x z = if z = x then 1 else 0) (φ : X → ℝ) (keep : Hist X X → ℝ) (n : ℕ) (h : Hist X X) : adSurv T M φ keep (n + 1) h = φ (q h) * adSurv T M φ keep n (h ++ [(q h, q h, true)]) + (1 - φ (q h)) * adSurv T M φ keep n (h ++ [(q h, q h, false)])
~~~

### 568. cat_id1

Source: proofs/UMADAPTF1.lean:331 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_id1 {X : Type} [Fintype X] [DecidableEq X] (M : X → X → ℝ) (hM : ∀ x z, M x z = if z = x then 1 else 0) (φ : X → ℝ) (ω : X) : cat (fun _ : X => True) M φ (seedPolicy (Z
~~~

### 569. det_dist

Source: proofs/UMADAPTF1.lean:336 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem det_dist {X : Type} [Fintype X] [DecidableEq X] (y : X) : IsDist (fun x : X => if x = y then (1 : ℝ) else 0)
~~~

### 570. keep01

Source: proofs/UMADAPTF1.lean:342 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem keep01 (P : Prop) [Decidable P] : 0 ≤ (if P then (1 : ℝ) else 0) ∧ (if P then (1 : ℝ) else 0) ≤ 1
~~~

### 571. setup_id

Source: proofs/UMADAPTF1.lean:346 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem setup_id {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] (M : X → X → ℝ) (hM : ∀ x z, M x z = if z = x then 1 else 0) : Setup (fun _ : X => True) M id (univ : Finset X)
~~~

### 572. misses_allflag

Source: proofs/UMADAPTF1.lean:359 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem misses_allflag {X Z : Type} (h : Hist X Z) (hh : ∀ e ∈ h, e.2.2 = false) : misses h = 0
~~~

### 573. c1_surv

Source: proofs/UMADAPTF1.lean:366 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c1_surv (t : ℝ) (ω : Bool) : adSurv ctrT idM (classRule id id t ω) ctrKeep 3 [] = if ω then 1 - t ^ 2 else (1 - t) + t * (1 - t) ^ 2
~~~

### 574. c1_risk

Source: proofs/UMADAPTF1.lean:372 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c1_risk (t : ℝ) : adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool)) (classRule id id t) (seedPolicy (Z
~~~

### 575. c2_surv

Source: proofs/UMADAPTF1.lean:383 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_surv (t : ℝ) (ω : Fin 3) : adSurv stT idM3 (classRule id id t ω) stKeep 3 [] = if ω = 0 then (1 - t) + t * (1 - t) ^ 2 else if ω = 1 then 1 - t ^ 2 else 1
~~~

### 576. c2_risk

Source: proofs/UMADAPTF1.lean:389 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_risk (t : ℝ) : adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3))) (classRule id id t) (seedPolicy (Z
~~~

### 577. c2_bound

Source: proofs/UMADAPTF1.lean:400 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t - t ^ 3 + t ^ 4 / 3 < 1 / 2
~~~

### 578. w_surv

Source: proofs/UMADAPTF1.lean:404 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_surv (t : ℝ) (ω : Bool) : adSurv wT idM (classRule id id t ω) wKeep 1 [] = if ω then 1 else 1 - t
~~~

### 579. wbad_surv

Source: proofs/UMADAPTF1.lean:409 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wbad_surv (t : ℝ) (ω : Bool) : adSurv wT idM (classRule id id t ω) wKeepBad 1 [] = if ω then 0 else t
~~~

### 580. part_c1

Source: proofs/UMADAPTF1.lean:414 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c1 : (Setup (fun _ : Bool => True) idM id (univ : Finset Bool) ∧ AdTester ctrT ctrKeep ∧ AcceptsAllFlag ctrT idM ctrKeep 3 ∧ (∀ h : Hist Bool Bool, misses h ≤ 1 → ctrKeep h = 1) ∧ adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool)) (classRule id id (3/4)) (seedPolicy (Z
~~~

### 581. part_c2

Source: proofs/UMADAPTF1.lean:439 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c2 : (Setup (fun _ : Fin 3 => True) idM3 id (univ : Finset (Fin 3)) ∧ AdTester stT stKeep ∧ AcceptsAllFlag stT idM3 stKeep 3 ∧ (∀ h : Hist (Fin 3) (Fin 3), misses h ≤ 1 → stKeep h = 1) ∧ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3))) (classRule id id t) (seedPolicy (Z
~~~

### 582. claim

Source: proofs/UMADAPTF1.lean:460 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMADAPTF1.Claim
~~~

### 583. witness

Source: proofs/UMADAPTF1.lean:463 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMADAPTF1.Witness
~~~

## proofs/UMADAPTF2.lean

### 584. adSurv_zero

Source: proofs/UMADAPTF2.lean:6 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_zero' {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (h : Hist X Z) : adSurv T M φ keep 0 h = keep h
~~~

### 585. adSurv_succ

Source: proofs/UMADAPTF2.lean:11 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_succ' {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ) (h : Hist X Z) : adSurv T M φ keep (n + 1) h = ∑ x, T h x * ∑ z, M x z * (φ z * adSurv T M φ keep n (h ++ [(x, z, true)]) + (1 - φ z) * adSurv T M φ keep n (h ++ [(x, z, false)]))
~~~

### 586. s_aux

Source: proofs/UMADAPTF2.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem s_aux {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hk : ∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) : ∀ (n : ℕ) (h : Hist X Z), (∀ e ∈ h, e.2.2 = false) → adSurv T M (fun _ => 0) keep n h = 1
~~~

### 587. part_s

Source: proofs/UMADAPTF2.lean:40 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_s : ∀ (X Z : Type) [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ), IsKernel M → (∀ h, IsDist (T h)) → (∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) → AcceptsAllFlag T M keep n
~~~

### 588. surv_bounds

Source: proofs/UMADAPTF2.lean:49 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_bounds {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hφ : IsRule φ) (hk : ∀ h, 0 ≤ keep h ∧ keep h ≤ 1) : ∀ (n : ℕ) (h : Hist X Z), 0 ≤ adSurv T M φ keep n h ∧ adSurv T M φ keep n h ≤ 1
~~~

### 589. Qf_zero

Source: proofs/UMADAPTF2.lean:84 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_zero {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (h : Hist X Z) : Qf T M w 0 h = 0
~~~

### 590. Qf_succ

Source: proofs/UMADAPTF2.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_succ {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (n : ℕ) (h : Hist X Z) : Qf T M w (n + 1) h = ∑ x, T h x * ∑ z, M x z * (w z + Qf T M w n (h ++ [(x, z, false)]))
~~~

### 591. Qf_nonneg

Source: proofs/UMADAPTF2.lean:93 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_nonneg {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hw : ∀ z, 0 ≤ w z) : ∀ (n : ℕ) (h : Hist X Z), 0 ≤ Qf T M w n h
~~~

### 592. sum2_add

Source: proofs/UMADAPTF2.lean:106 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum2_add {X Z : Type} [Fintype X] [Fintype Z] (a : X → ℝ) (m : X → Z → ℝ) (f g : X → Z → ℝ) (t : ℝ) : ∑ x, a x * ∑ z, m x z * f x z + t * ∑ x, a x * ∑ z, m x z * g x z = ∑ x, a x * ∑ z, m x z * (f x z + t * g x z)
~~~

### 593. ref_lb

Source: proofs/UMADAPTF2.lean:117 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ref_lb {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ w : Z → ℝ) (t : ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hk : ∀ h, 0 ≤ keep h ∧ keep h ≤ 1) (hφ : IsRule φ) (hw : ∀ z, 0 ≤ w z) (ht : 0 ≤ t) (hφw : ∀ z, φ z ≤ t * w z) : ∀ (n : ℕ) (h : Hist X Z), adSurv T M (fun _ => 0) keep n h - t * Qf T M w n h ≤ adSurv T M φ keep n h
~~~

### 594. Q_sum_le

Source: proofs/UMADAPTF2.lean:147 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Q_sum_le {X Z Ω : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (S : Finset Ω) (w : Ω → Z → ℝ) (hw1 : ∀ z, ∑ ω ∈ S, w ω z ≤ 1) : ∀ (n : ℕ) (h : Hist X Z), ∑ ω ∈ S, Qf T M (w ω) n h ≤ n
~~~

### 595. ind_sum_le

Source: proofs/UMADAPTF2.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ind_sum_le {X Z C : Type} [DecidableEq C] (c : X → C) (g : Z → C) (S : Finset X) (hinj : Set.InjOn c (S : Set X)) (z : Z) : ∑ ω ∈ S, (if g z = c ω then (1 : ℝ) else 0) ≤ 1
~~~

### 596. classRule_rule

Source: proofs/UMADAPTF2.lean:184 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classRule_rule {X Z C : Type} [DecidableEq C] (c : X → C) (g : Z → C) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ω : X) : IsRule (classRule c g t ω)
~~~

### 597. conv_a

Source: proofs/UMADAPTF2.lean:188 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conv_a {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X) (hM : IsKernel M) (hbad : ∀ x ∈ S, Bad x) (hinj : Set.InjOn c (S : Set X)) (hS : 0 < S.card) (g : Z → C) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ) (hTk : AdTester T keep) (hacc : AcceptsAllFlag T M keep n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (r : ℝ) (b N : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hN : 1 ≤ N) : t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z
~~~

### 598. opt_arith

Source: proofs/UMADAPTF2.lean:270 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem opt_arith (k n : ℝ) (hk : 0 < k) (hn : 1 ≤ n) : min (1 / 2) (k / (4 * n)) ≤ min 1 (k / (2 * n)) * max 0 (1 - min 1 (k / (2 * n)) * n / k)
~~~

### 599. part_a

Source: proofs/UMADAPTF2.lean:289 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_a : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X), Setup Bad M c S → ∃ g : Z → C, (∀ x z, M x z ≠ 0 → g z = c x) ∧ (∀ (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ), AdTester T keep → AcceptsAllFlag T M keep n → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N → t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z
~~~

### 600. adSurv_det

Source: proofs/UMADAPTF2.lean:322 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_det {X : Type} [Fintype X] [DecidableEq X] (T : Hist X X → X → ℝ) (M : X → X → ℝ) (q : Hist X X → X) (hT : ∀ h x, T h x = if x = q h then 1 else 0) (hM : ∀ x z, M x z = if z = x then 1 else 0) (φ : X → ℝ) (keep : Hist X X → ℝ) (n : ℕ) (h : Hist X X) : adSurv T M φ keep (n + 1) h = φ (q h) * adSurv T M φ keep n (h ++ [(q h, q h, true)]) + (1 - φ (q h)) * adSurv T M φ keep n (h ++ [(q h, q h, false)])
~~~

### 601. cat_id1

Source: proofs/UMADAPTF2.lean:332 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_id1 {X : Type} [Fintype X] [DecidableEq X] (M : X → X → ℝ) (hM : ∀ x z, M x z = if z = x then 1 else 0) (φ : X → ℝ) (ω : X) : cat (fun _ : X => True) M φ (seedPolicy (Z
~~~

### 602. det_dist

Source: proofs/UMADAPTF2.lean:337 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem det_dist {X : Type} [Fintype X] [DecidableEq X] (y : X) : IsDist (fun x : X => if x = y then (1 : ℝ) else 0)
~~~

### 603. keep01

Source: proofs/UMADAPTF2.lean:343 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem keep01 (P : Prop) [Decidable P] : 0 ≤ (if P then (1 : ℝ) else 0) ∧ (if P then (1 : ℝ) else 0) ≤ 1
~~~

### 604. setup_id

Source: proofs/UMADAPTF2.lean:347 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem setup_id {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] (M : X → X → ℝ) (hM : ∀ x z, M x z = if z = x then 1 else 0) : Setup (fun _ : X => True) M id (univ : Finset X)
~~~

### 605. misses_allflag

Source: proofs/UMADAPTF2.lean:360 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem misses_allflag {X Z : Type} (h : Hist X Z) (hh : ∀ e ∈ h, e.2.2 = false) : misses h = 0
~~~

### 606. c1_surv

Source: proofs/UMADAPTF2.lean:367 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c1_surv (t : ℝ) (ω : Bool) : adSurv ctrT idM (PL_UMLOWERF1.classRule id id t ω) ctrKeep 3 [] = if ω then 1 - t ^ 2 else (1 - t) + t * (1 - t) ^ 2
~~~

### 607. c1_risk

Source: proofs/UMADAPTF2.lean:373 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c1_risk (t : ℝ) : adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool)) (classRule id id t) (seedPolicy (Z
~~~

### 608. c2_surv

Source: proofs/UMADAPTF2.lean:384 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_surv (t : ℝ) (ω : Fin 3) : adSurv stT idM3 (PL_UMLOWERF1.classRule id id t ω) stKeep 3 [] = if ω = 0 then (1 - t) + t * (1 - t) ^ 2 else if ω = 1 then 1 - t ^ 2 else 1
~~~

### 609. c2_risk

Source: proofs/UMADAPTF2.lean:390 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_risk (t : ℝ) : adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3))) (classRule id id t) (seedPolicy (Z
~~~

### 610. c2_bound

Source: proofs/UMADAPTF2.lean:401 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t - t ^ 3 + t ^ 4 / 3 < 1 / 2
~~~

### 611. w_surv

Source: proofs/UMADAPTF2.lean:405 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_surv (t : ℝ) (ω : Bool) : adSurv wT idM (PL_UMLOWERF1.classRule id id t ω) wKeep 1 [] = if ω then 1 else 1 - t
~~~

### 612. wbad_surv

Source: proofs/UMADAPTF2.lean:410 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wbad_surv (t : ℝ) (ω : Bool) : adSurv wT idM (PL_UMLOWERF1.classRule id id t ω) wKeepBad 1 [] = if ω then 0 else t
~~~

### 613. part_c1

Source: proofs/UMADAPTF2.lean:415 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c1 : (Setup (fun _ : Bool => True) idM id (univ : Finset Bool) ∧ AdTester ctrT ctrKeep ∧ AcceptsAllFlag ctrT idM ctrKeep 3 ∧ (∀ h : Hist Bool Bool, misses h ≤ 1 → ctrKeep h = 1) ∧ adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool)) (classRule id id (3/4)) (seedPolicy (Z
~~~

### 614. part_c2

Source: proofs/UMADAPTF2.lean:440 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c2 : (Setup (fun _ : Fin 3 => True) idM3 id (univ : Finset (Fin 3)) ∧ AdTester stT stKeep ∧ AcceptsAllFlag stT idM3 stKeep 3 ∧ (∀ h : Hist (Fin 3) (Fin 3), misses h ≤ 1 → stKeep h = 1) ∧ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3))) (classRule id id t) (seedPolicy (Z
~~~

### 615. claim1

Source: proofs/UMADAPTF2.lean:461 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim1 : PL_UMADAPTF1.Claim
~~~

### 616. witness1

Source: proofs/UMADAPTF2.lean:464 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness1 : PL_UMADAPTF1.Witness
~~~

### 617. slope_mono

Source: proofs/UMADAPTF2.lean:494 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
private lemma slope_mono (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : ∀ {n k : ℕ}, n ≤ k → slope b n ≤ slope b k
~~~

### 618. tangent_step

Source: proofs/UMADAPTF2.lean:506 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
private lemma tangent_step (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (m q : ℕ) (hmq : m ≤ q) : b ^ (q + 1) + ((m : ℝ) - ((q + 1 : ℕ) : ℝ)) * slope b (q + 1) ≤ b ^ q + ((m : ℝ) - (q : ℝ)) * slope b q
~~~

### 619. balanced_bound

Source: proofs/UMADAPTF2.lean:522 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem balanced_bound (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (m q : ℕ) : b ^ m ≥ b ^ q + ((m : ℝ) - (q : ℝ)) * (b ^ (q + 1) - b ^ q)
~~~

### 620. aggregate_balanced_budget

Source: proofs/UMADAPTF2.lean:550 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem aggregate_balanced_budget (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k q a : ℕ) (_hk : 0 < k) (ha : a < k) (counts : Fin k → ℕ) (hcounts : ∑ i : Fin k, counts i ≤ k * q + a) : ∑ i : Fin k, b ^ (counts i) ≥ ((k - a : ℕ) : ℝ) * b ^ q + (a : ℝ) * b ^ (q + 1)
~~~

### 621. aggregate_balanced_exact

Source: proofs/UMADAPTF2.lean:591 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem aggregate_balanced_exact (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k n : ℕ) (hk : 0 < k) (counts : Fin k → ℕ) (hcounts : ∑ i : Fin k, counts i = n) : ∑ i : Fin k, b ^ (counts i) ≥ ((k - n % k : ℕ) : ℝ) * b ^ (n / k) + ((n % k : ℕ) : ℝ) * b ^ (n / k + 1)
~~~

### 622. classCount_append_flag

Source: proofs/UMADAPTF2.lean:626 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classCount_append_flag {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (h : SharpHist X Z) (x : X) (z : Z) (ω : Fin k) : classCount g (h ++ [(x, z, false)]) ω = classCount g h ω + (if g z = some ω then 1 else 0)
~~~

### 623. flagFactor

Source: proofs/UMADAPTF2.lean:632 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem flagFactor {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (b : ℝ) (ω : Fin k) (z : Z) : 1 - passProb g (1-b) ω z = if g z = some ω then b else 1
~~~

### 624. passProb_bounds

Source: proofs/UMADAPTF2.lean:646 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem passProb_bounds {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ω : Fin k) (z : Z) : 0 ≤ passProb g t ω z ∧ passProb g t ω z ≤ 1
~~~

### 625. fullSurv_nonneg

Source: proofs/UMADAPTF2.lean:653 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fullSurv_nonneg {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) : ∀ n h ω, 0 ≤ fullSurv T M g t keep ω n h
~~~

### 626. fullSurv_ge_flagOnly

Source: proofs/UMADAPTF2.lean:684 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fullSurv_ge_flagOnly {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) : ∀ n h ω, flagOnly T M g t keep ω n h ≤ fullSurv T M g t keep ω n h
~~~

### 627. refSurv_eq_fullSurv_zero

Source: proofs/UMADAPTF2.lean:730 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refSurv_eq_fullSurv_zero {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (keep : SharpHist X Z → ℝ) : ∀ n h ω, refSurv T M keep n h = fullSurv T M g 0 keep ω n h
~~~

### 628. classPower_append_flag

Source: proofs/UMADAPTF2.lean:756 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classPower_append_flag {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (b : ℝ) (h : SharpHist X Z) (x : X) (z : Z) (ω : Fin k) : b ^ classCount g h ω * (if g z = some ω then b else 1) = b ^ classCount g (h ++ [(x,z,false)]) ω
~~~

### 629. weightedFactor_append

Source: proofs/UMADAPTF2.lean:763 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
private theorem weightedFactor_append {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (b : ℝ) (h : SharpHist X Z) (x : X) (z : Z) (ω : Fin k) (f : ℝ) : b ^ classCount g (h ++ [(x,z,false)]) ω * f = b ^ classCount g h ω * ((1 - passProb g (1-b) ω z) * f)
~~~

### 630. weighted_double_sum

Source: proofs/UMADAPTF2.lean:779 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem weighted_double_sum {α β : Type} [Fintype α] [Fintype β] (a : α → ℝ) (c : β → ℝ) (f : α → β → ℝ) : (∑ i, a i * ∑ j, c j * f i j) = ∑ j, c j * ∑ i, a i * f i j
~~~

### 631. weightedFlag_succ

Source: proofs/UMADAPTF2.lean:799 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem weightedFlag_succ {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (b : ℝ) (keep : SharpHist X Z → ℝ) (n : ℕ) (h : SharpHist X Z) : weightedFlag T M g b keep (n+1) h = ∑ x, T h x * ∑ z, M x z * weightedFlag T M g b keep n (h ++ [(x,z,false)])
~~~

### 632. count_sum_le

Source: proofs/UMADAPTF2.lean:886 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem count_sum_le {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (h : SharpHist X Z) : (∑ ω : Fin k, classCount g h ω) ≤ h.length
~~~

### 633. weightedFlag_lower

Source: proofs/UMADAPTF2.lean:928 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem weightedFlag_lower {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (N : ℕ) : ∀ n h, h.length + n = N → balancedTarget k N b * refSurv T M keep n h ≤ weightedFlag T M g b keep n h
~~~

### 634. sharp_survival

Source: proofs/UMADAPTF2.lean:992 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_survival {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : refSurv T M keep n [] = 1) : balancedTarget k n (1-t) ≤ ∑ ω : Fin k, fullSurv T M g t keep ω n []
~~~

### 635. sharp_uniform_cat

Source: proofs/UMADAPTF2.lean:1022 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_uniform_cat {k : ℕ} (hkpos : 0 < k) (t : ℝ) (ht0 : 0 ≤ t) (n : ℕ) (surv cat : Fin k → ℝ) (hsurv : ∀ i, 0 ≤ surv i) (hcat : ∀ i, t ≤ cat i) (hsum : balancedTarget k n (1-t) ≤ ∑ i : Fin k, surv i) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ (1 / (k : ℝ)) * ∑ i : Fin k, surv i * cat i
~~~

### 636. seedDecoder_eq_some_iff

Source: proofs/UMADAPTF2.lean:1058 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seedDecoder_eq_some_iff {X C Z : Type} [DecidableEq C] {k : ℕ} (seed : Fin k → X) (c : X → C) (g : Z → C) (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (z : Z) (i : Fin k) : seedDecoder seed c g z = some i ↔ g z = c (seed i)
~~~

### 637. seedDecoder_pass_eq

Source: proofs/UMADAPTF2.lean:1088 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seedDecoder_pass_eq {X C Z : Type} [DecidableEq C] {k : ℕ} (seed : Fin k → X) (c : X → C) (g : Z → C) (t : ℝ) (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (i : Fin k) (z : Z) : passProb (seedDecoder seed c g) t i z = classPass c g t (seed i) z
~~~

### 638. refSurv_eq_passSurv_zero

Source: proofs/UMADAPTF2.lean:1109 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refSurv_eq_passSurv_zero {X : Type} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (keep : SharpHist X Z → ℝ) : ∀ n h, refSurv T M keep n h = passSurv T M (fun _ => 0) keep n h
~~~

### 639. fullSurv_eq_passSurv_seed

Source: proofs/UMADAPTF2.lean:1126 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fullSurv_eq_passSurv_seed {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (seed : Fin k → X) (c : X → C) (g : Z → C) (t : ℝ) (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (keep : SharpHist X Z → ℝ) (i : Fin k) : ∀ n h, fullSurv T M (seedDecoder seed c g) t keep i n h = passSurv T M (classPass c g t (seed i)) keep n h
~~~

### 640. sharp_seedset_survival

Source: proofs/UMADAPTF2.lean:1148 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_seedset_survival {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : refSurv T M keep n [] = 1) : balancedTarget k n (1-t) ≤ ∑ i : Fin k, passSurv T M (classPass c g t ((e i).val)) keep n []
~~~

### 641. sharp_seedset_catRisk

Source: proofs/UMADAPTF2.lean:1177 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_seedset_catRisk {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : refSurv T M keep n [] = 1) (cat : Fin k → ℝ) (hcat : ∀ i, t ≤ cat i) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ (1 / (k : ℝ)) * ∑ i : Fin k, passSurv T M (classPass c g t ((e i).val)) keep n [] * cat i
~~~

### 642. adSurv_reference_eq

Source: proofs/UMADAPTF2.lean:1234 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_reference_eq {X Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (keep : SharpHist X Z → ℝ) : ∀ n h, refSurv T M keep n h = adSurv T M (fun _ => 0) keep n h
~~~

### 643. accepts_all_flag_reference

Source: proofs/UMADAPTF2.lean:1240 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem accepts_all_flag_reference {X Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (keep : SharpHist X Z → ℝ) (n : ℕ) (hacc : adSurv T M (fun _ => 0) keep n [] = 1) : refSurv T M keep n [] = 1
~~~

### 644. sharp_uniform_seed_risk

Source: proofs/UMADAPTF2.lean:1250 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_uniform_seed_risk {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : adSurv T M (fun _ => 0) keep n [] = 1) (cat : Fin k → ℝ) (hcat : ∀ i, t ≤ cat i) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ (1 / (k : ℝ)) * ∑ i : Fin k, adSurv T M (classRule c g t ((e i).val)) keep n [] * cat i
~~~

### 645. protocolCatModel_eq

Source: proofs/UMADAPTF2.lean:1281 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem protocolCatModel_eq {X : Type} [Fintype X] [DecidableEq X] (S : Finset X) (surv cat : X → ℝ) : protocolCatModel S surv cat = (1 / (S.card : ℝ)) * ∑ x : {x // x ∈ S}, surv x.val * cat x.val
~~~

### 646. sum_finEquiv_eq_sum_seed

Source: proofs/UMADAPTF2.lean:1301 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_finEquiv_eq_sum_seed {X : Type} {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (f : {x // x ∈ S} → ℝ) : (∑ i : Fin k, f (e i)) = ∑ x : {x // x ∈ S}, f x
~~~

### 647. sharp_uniform_adProtocolCatModel

Source: proofs/UMADAPTF2.lean:1305 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_uniform_adProtocolCatModel {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] [DecidableEq X] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : adSurv T M (fun _ => 0) keep n [] = 1) (cat : X → ℝ) (hcat : ∀ x ∈ S, t ≤ cat x) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ protocolCatModel S (fun x => adSurv T M (classRule c g t x) keep n []) cat
~~~

### 648. sharp_surv_eq_campaign

Source: proofs/UMADAPTF2.lean:1357 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_surv_eq_campaign {X Z : Type} [Fintype X] [Fintype Z] (T : _root_.PL_UMPROTF1.Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : _root_.PL_UMPROTF1.Hist X Z → ℝ) : ∀ n h, SharpUM.adSurv T M φ keep n h = _root_.PL_UMADAPTF1.adSurv T M φ keep n h
~~~

### 649. conv_a_sharp

Source: proofs/UMADAPTF2.lean:1379 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conv_a_sharp {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X) (hM : IsKernel M) (hbad : ∀ x ∈ S, Bad x) (hinj : Set.InjOn c (S : Set X)) (hS : 0 < S.card) (g : Z → C) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ) (hTk : AdTester T keep) (hacc : AcceptsAllFlag T M keep n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (r : ℝ) (b N : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hN : 1 ≤ N) : (t / (S.card : ℝ)) * balancedTarget S.card n (1-t) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (_root_.PL_UMLOWERF1.classRule c g t) (seedPolicy (Z
~~~

### 650. sharpTarget_eq

Source: proofs/UMADAPTF2.lean:1439 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharpTarget_eq (k n : ℕ) (b : ℝ) : PL_UMADAPTF2.sharpTarget k n b = balancedTarget k n b
~~~

### 651. claim

Source: proofs/UMADAPTF2.lean:1442 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMADAPTF2.Claim
~~~

### 652. rr_surv

Source: proofs/UMADAPTF2.lean:1451 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rr_surv (t : ℝ) (ω : Bool) : PL_UMADAPTF1.adSurv rrT idM (PL_UMLOWERF1.classRule id id t ω) rrKeep 3 [] = if ω then 1 - t else (1 - t) ^ 2
~~~

### 653. witness

Source: proofs/UMADAPTF2.lean:1456 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMADAPTF2.Witness
~~~

## proofs/UMCERTF1.lean

### 654. capB_mono

Source: proofs/UMCERTF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB_mono (r : ℝ) (b : ℕ) (hr : 0 ≤ r) {a a' : ℝ} (h : a ≤ a') : capB r b a ≤ capB r b a'
~~~

### 655. capB_nonneg

Source: proofs/UMCERTF1.lean:12 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB_nonneg (r : ℝ) (b : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ capB r b a
~~~

### 656. capB_le

Source: proofs/UMCERTF1.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB_le (r : ℝ) (b : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {a : ℝ} (ha : a ≤ 1) : capB r b a ≤ 1 - r + r * a
~~~

### 657. capB_one

Source: proofs/UMCERTF1.lean:26 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB_one (r : ℝ) (b : ℕ) : capB r b 1 = 1
~~~

### 658. E_const

Source: proofs/UMCERTF1.lean:32 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_const {Z : Type} [Fintype Z] (P : Z → ℝ) (hP : ∑ z, P z = 1) (t : ℝ) : E P (fun _ => t) = t
~~~

### 659. E_push

Source: proofs/UMCERTF1.lean:37 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_push {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (P : X → ℝ) (ψ : Z → ℝ) : E (push M P) ψ = ∑ x, P x * E (M x) ψ
~~~

### 660. unit_dist

Source: proofs/UMCERTF1.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unit_dist : IsDist (fun _ : Unit => (1 : ℝ))
~~~

### 661. point_dist

Source: proofs/UMCERTF1.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem point_dist {X : Type} [Fintype X] [DecidableEq X] (x : X) : IsDist (fun x' : X => if x' = x then (1 : ℝ) else 0)
~~~

### 662. cat_empty

Source: proofs/UMCERTF1.lean:60 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_empty {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (b : ℕ) (hB : ∀ x, ¬ Bad x) : ∀ n u h, cat Bad M φ π r b n u h = 0
~~~

### 663. cat_oneshot

Source: proofs/UMCERTF1.lean:71 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_oneshot {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] [DecidableEq X] (M : X → Z → ℝ) (ψ : Z → ℝ) (r : ℝ) (b N : ℕ) (x : X) (hM : IsKernel M) (hx : Bad x) (hN : 1 ≤ N) : cat Bad M ψ (fun _ x' => if x' = x then 1 else 0) r b N 0 [] = capB r b (E (M x) ψ)
~~~

### 664. exists_worst

Source: proofs/UMCERTF1.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exists_worst {X : Type} [Fintype X] (Bad : X → Prop) [DecidablePred Bad] (f : X → ℝ) (hex : ∃ x, Bad x) : ∃ x0, Bad x0 ∧ ∀ x, Bad x → f x ≤ f x0
~~~

### 665. oneshot_value

Source: proofs/UMCERTF1.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem oneshot_value {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] [DecidableEq X] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (ψ : Z → ℝ) (x : X) (hM : IsKernel M) (hP : IsDist PH) (hx : Bad x) (hN : 1 ≤ N) : protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (fun _ => ψ) (fun _ _ x' => if x' = x then 1 else 0) = survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ)
~~~

### 666. strat_oneshot_value

Source: proofs/UMCERTF1.lean:108 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem strat_oneshot_value {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (g : Z → C) (Es : Finset C) (m sc b N : ℕ) (r t : ℝ) (x : X) (hK : IsKernel K) (hdec : ∀ e z, K e z ≠ 0 → g z = e) (hx : Bad x) (hcx : c x ∈ Es) (hN : 1 ≤ N) : stratProtocolCat Bad K c Es m sc r b N (fun _ : Unit => 1) (fun _ z => if g z = c x then t else 0) (fun _ _ x' => if x' = x then 1 else 0) = binCDF m sc t * capB r b t
~~~

### 667. seed_le

Source: proofs/UMCERTF1.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seed_le {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (hM : IsKernel M) (hP : IsDist PH) (hφ : IsRule φ) (hπ : ∀ h, IsDist (π h)) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hU : 0 ≤ U) (hyp : ∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) ≤ U) : surv (push M PH) φ κ nh 0 * cat Bad M φ π r b N 0 [] ≤ U
~~~

### 668. reduce_le

Source: proofs/UMCERTF1.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reduce_le {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) (hM : IsKernel M) (hP : IsDist PH) (hρ : IsDist ρ) (hφ : ∀ ω, IsRule (φ ω)) (hπ : ∀ ω h, IsDist (π ω h)) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hU : 0 ≤ U) (hyp : ∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) ≤ U) : protocolCat Bad M PH κ nh r b N ρ φ π ≤ U
~~~

### 669. survH_aux

Source: proofs/UMCERTF1.lean:167 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survH_aux (κ : ℕ → ℝ) (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ 1) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) : ∀ n j, (1 - κ j) * survH h κ n (j + 1) ≤ survH h κ n j
~~~

### 670. survH_anti

Source: proofs/UMCERTF1.lean:190 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survH_anti (κ : ℕ → ℝ) (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ 1) : ∀ n j (s t : ℝ), 0 ≤ s → s ≤ t → t ≤ 1 → survH t κ n j ≤ survH s κ n j
~~~

### 671. GridOK_cons2

Source: proofs/UMCERTF1.lean:218 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem GridOK_cons2 (S F : ℝ → ℝ) (U s t : ℝ) (rest : List ℝ) : GridOK S F U (s :: t :: rest) ↔ s ≤ t ∧ S s * F t ≤ U ∧ GridOK S F U (t :: rest)
~~~

### 672. GridOK_single

Source: proofs/UMCERTF1.lean:221 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem GridOK_single (S F : ℝ → ℝ) (U a : ℝ) : GridOK S F U [a] ↔ True
~~~

### 673. grid_aux

Source: proofs/UMCERTF1.lean:223 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem grid_aux (S F : ℝ → ℝ) (U : ℝ) (hS : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s) (hF : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t) (h0 : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t) : ∀ (rest : List ℝ) (a b : ℝ), GridOK S F U (a :: b :: rest) → (a :: b :: rest).getLast? = some 1 → 0 ≤ a → a ≤ 1 ∧ ∀ t, a ≤ t → t ≤ 1 → S t * F t ≤ U
~~~

### 674. grid_cert

Source: proofs/UMCERTF1.lean:263 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem grid_cert (S F : ℝ → ℝ) (U : ℝ) (ts : List ℝ) (hS : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s) (hF : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t) (h0 : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t) (hG : GridCert S F U ts) : ∀ t, 0 ≤ t → t ≤ 1 → S t * F t ≤ U
~~~

### 675. bin_anti

Source: proofs/UMCERTF1.lean:282 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bin_anti (m sc : ℕ) : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → binCDF m sc t ≤ binCDF m sc s
~~~

### 676. bin_nonneg

Source: proofs/UMCERTF1.lean:287 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bin_nonneg (m sc : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ binCDF m sc t
~~~

### 677. dom_content

Source: proofs/UMCERTF1.lean:293 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dom_content {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] (K : C → Z → ℝ) (c : X → C) (PH : X → ℝ) (p : ℝ) (hK : IsKernel K) (hP : IsDist PH) (hp : 0 < p) (x : X) (hcov : p ≤ contentLaw c PH (c x)) (z : Z) : (fun x => K (c x)) x z ≤ (1 / p) * push (fun x => K (c x)) PH z
~~~

### 678. claim_R

Source: proofs/UMCERTF1.lean:315 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_R : ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ), IsKernel M → IsDist PH → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N → 0 ≤ U → ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ↔ (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) ≤ U))
~~~

### 679. claim_C

Source: proofs/UMCERTF1.lean:333 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_C : ∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (env : ℝ → ℝ) (U : ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 0 ≤ U → (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ env (E (push M PH) ψ)) → (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b (min 1 (env t)) ≤ U) → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U
~~~

### 680. claim_E1

Source: proofs/UMCERTF1.lean:355 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_E1 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (L : ℝ) (x : X), (∀ z, M x z ≤ L * push M PH z) → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ L * E (push M PH) ψ
~~~

### 681. claim_E2

Source: proofs/UMCERTF1.lean:361 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_E2 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (η δ : ℝ) (x : X), hs η (M x) (push M PH) ≤ δ → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ Real.exp η * E (push M PH) ψ + δ
~~~

### 682. claim_G0

Source: proofs/UMCERTF1.lean:368 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_G0 : ∀ (κ : ℕ → ℝ) (n j : ℕ) (s t : ℝ), (∀ i, 0 ≤ κ i ∧ κ i ≤ 1) → 0 ≤ s → s ≤ t → t ≤ 1 → survH t κ n j ≤ survH s κ n j
~~~

### 683. claim_G

Source: proofs/UMCERTF1.lean:372 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_G : ∀ (S F : ℝ → ℝ) (U : ℝ) (ts : List ℝ), (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s) → (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t) → (∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t) → GridCert S F U ts → ∀ t, 0 ≤ t → t ≤ 1 → S t * F t ≤ U
~~~

### 684. claim_CG

Source: proofs/UMCERTF1.lean:379 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_CG : ∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (env : ℝ → ℝ) (U : ℝ) (ts : List ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ env (E (push M PH) ψ)) → (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → env s ≤ env t) → (∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ env t) → GridCert (fun t => survH t κ nh 0) (fun t => capB r b (min 1 (env t))) U ts → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U
~~~

### 685. claim_S1

Source: proofs/UMCERTF1.lean:404 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_S1 : ∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 → (∀ x, Bad x → c x ∈ Es) → (∀ t : ℝ, 0 ≤ t → t ≤ 1 → binCDF m sc t * capB r b t ≤ U) → stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U
~~~

### 686. claim_SG

Source: proofs/UMCERTF1.lean:440 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_SG : ∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ) (ts : List ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 → (∀ x, Bad x → c x ∈ Es) → GridCert (fun t => binCDF m sc t) (fun t => capB r b t) U ts → stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U
~~~

### 687. claim_D1

Source: proofs/UMCERTF1.lean:455 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_D1 : ∀ (n s b : ℕ) (r L t : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ L → 0 ≤ t → t ≤ 1 → survH t (hardKill s) n 0 * capB r b (min 1 (L * t)) ≤ (1 - r) + r * (L * (((s : ℝ) + 1) / ((n : ℝ) + 1)))
~~~

### 688. claim_D2

Source: proofs/UMCERTF1.lean:468 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_D2 : ∀ (n ns b : ℕ) (r L t : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ L → 1 ≤ ns → 0 ≤ t → t ≤ 1 → survH t (softKill ns) n 0 * capB r b (min 1 (L * t)) ≤ (1 - r) + r * (L * ((ns : ℝ) / ((n : ℝ) + 1)))
~~~

### 689. claim_F

Source: proofs/UMCERTF1.lean:487 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_F : ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ), IsKernel M → IsDist PH → 1 ≤ N → (∃ x, Bad x) → (∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b t ≤ U
~~~

### 690. claim_X

Source: proofs/UMCERTF1.lean:504 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_X : ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ), IsKernel M → IsDist PH → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N → (∃ x, Bad x) → (∀ x, Bad x → ∀ z, M x z ≤ push M PH z) → ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ↔ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b t ≤ U))
~~~

### 691. claim_Xp

Source: proofs/UMCERTF1.lean:532 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_Xp : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (g : Z → C) (PH : X → ℝ) (p : ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ), IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → IsDist PH → 0 < p → (∀ x, Bad x → p ≤ contentLaw c PH (c x)) → (∃ x, Bad x ∧ contentLaw c PH (c x) = p) → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N → ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → protocolCat Bad (fun x => K (c x)) PH κ nh r b N ρ φ π ≤ U) ↔ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b (min 1 ((1 / p) * t)) ≤ U))
~~~

### 692. claim_S2

Source: proofs/UMCERTF1.lean:620 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_S2 : ∀ (X Z C : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (g : Z → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ), IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → 0 ≤ r → r ≤ 1 → 1 ≤ N → (∃ x, Bad x) → (∀ x, Bad x → c x ∈ Es) → ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U) ↔ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → binCDF m sc t * capB r b t ≤ U))
~~~

### 693. claim

Source: proofs/UMCERTF1.lean:646 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMCERTF1.Claim
~~~

### 694. bin12

Source: proofs/UMCERTF1.lean:652 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bin12 (s : ℝ) : binCDF 12 1 s = (1 - s) ^ 12 + 12 * s * (1 - s) ^ 11
~~~

### 695. bin30

Source: proofs/UMCERTF1.lean:655 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bin30 (s : ℝ) : binCDF 30 1 s = (1 - s) ^ 30 + 30 * s * (1 - s) ^ 29
~~~

### 696. soft5

Source: proofs/UMCERTF1.lean:658 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem soft5 (t : ℝ) : survH t (softKill 5) 100 0 = (1 - 1 / 5 * t) ^ 100
~~~

### 697. hard1

Source: proofs/UMCERTF1.lean:665 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hard1 (t : ℝ) : survH t (hardKill 1) 30 0 = binCDF 30 1 t
~~~

### 698. capB11

Source: proofs/UMCERTF1.lean:668 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB11 (a : ℝ) : capB 1 1 a = a
~~~

### 699. capBk

Source: proofs/UMCERTF1.lean:672 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capBk (a : ℝ) : capB (9 / 10) 1 a = 1 / 10 + 9 / 10 * a
~~~

### 700. idK_kernel

Source: proofs/UMCERTF1.lean:676 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem idK_kernel : IsKernel idK
~~~

### 701. idK_dec

Source: proofs/UMCERTF1.lean:684 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem idK_dec : ∀ e z : Bool, idK e z ≠ 0 → id z = e
~~~

### 702. ptTrue_dist

Source: proofs/UMCERTF1.lean:691 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ptTrue_dist : IsDist ptTrue
~~~

### 703. w_main

Source: proofs/UMCERTF1.lean:698 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_main : GridCert (fun t => binCDF 12 1 t) (fun t => capB 1 1 t) (7/100) gridMain
~~~

### 704. w_soft

Source: proofs/UMCERTF1.lean:704 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_soft : GridCert (fun t => survH t (softKill 5) 100 0) (fun t => capB 1 1 (min 1 (1 * t))) (19/1000) gridSoft
~~~

### 705. w_kink

Source: proofs/UMCERTF1.lean:711 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_kink : GridCert (fun t => survH t (hardKill 1) 30 0) (fun t => capB (9/10) 1 (min 1 (4 * t))) (17/100) gridKink
~~~

### 706. w_strat

Source: proofs/UMCERTF1.lean:718 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_strat : (6833/100000 : ℝ) ≤ stratProtocolCat (fun x : Bool => x = true) idK id Finset.univ 12 1 1 1 1 (fun _ : Unit => 1) (fun _ z => if z = true then 1/8 else 0) (fun _ _ x => if x = true then 1 else 0)
~~~

### 707. w_prot

Source: proofs/UMCERTF1.lean:727 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_prot : (6833/100000 : ℝ) ≤ protocolCat (fun x : Bool => x = true) idK ptTrue (hardKill 1) 12 1 1 1 (fun _ : Unit => 1) (fun _ _ => 1/8) (fun _ _ x => if x = true then 1 else 0)
~~~

### 708. witness

Source: proofs/UMCERTF1.lean:738 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMCERTF1.Witness
~~~

## proofs/UMDEFERF1.lean

### 709. mul_le_mul_of_pos_imp

Source: proofs/UMDEFERF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mul_le_mul_of_pos_imp {p x y : ℝ} (hp : 0 ≤ p) (h : 0 < p → x ≤ y) : p * x ≤ p * y
~~~

### 710. conv01

Source: proofs/UMDEFERF1.lean:11 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conv01 {p v w : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : 0 ≤ p * v + (1 - p) * w ∧ p * v + (1 - p) * w ≤ 1
~~~

### 711. wsum01

Source: proofs/UMDEFERF1.lean:18 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum01 {Y : Type} [Fintype Y] (w f : Y → ℝ) (hw : IsDist w) (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) : 0 ≤ ∑ y, w y * f y ∧ ∑ y, w y * f y ≤ 1
~~~

### 712. prod3_nonneg

Source: proofs/UMDEFERF1.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prod3_nonneg {p q c : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hc : 0 ≤ c) : 0 ≤ p * q * c
~~~

### 713. prod3_le_one

Source: proofs/UMDEFERF1.lean:26 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prod3_le_one {p q c : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : p * q * c ≤ 1
~~~

### 714. theta_bounds

Source: proofs/UMDEFERF1.lean:31 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem theta_bounds {η α : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : 0 ≤ theta η α ∧ theta η α ≤ 1
~~~

### 715. one_sub_theta

Source: proofs/UMDEFERF1.lean:38 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem one_sub_theta (η α : ℝ) : 1 - theta η α = (1 - η) * (1 - α)
~~~

### 716. retry_zero

Source: proofs/UMDEFERF1.lean:43 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_zero (A θ : ℝ) : retry A θ 0 = 0
~~~

### 717. retry_succ

Source: proofs/UMDEFERF1.lean:45 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_succ (A θ : ℝ) (n : ℕ) : retry A θ (n + 1) = A + (1 - A) * (1 - θ) * retry A θ n
~~~

### 718. retry_bounds

Source: proofs/UMDEFERF1.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_bounds {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : ∀ n, 0 ≤ retry A θ n ∧ retry A θ n ≤ 1
~~~

### 719. retry_le_succ

Source: proofs/UMDEFERF1.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_le_succ {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ1 : θ ≤ 1) : ∀ n, retry A θ n ≤ retry A θ (n + 1)
~~~

### 720. retry_mono

Source: proofs/UMDEFERF1.lean:73 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_mono {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ1 : θ ≤ 1) {m n : ℕ} (hmn : m ≤ n) : retry A θ m ≤ retry A θ n
~~~

### 721. retry_closed

Source: proofs/UMDEFERF1.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_closed (A θ : ℝ) : ∀ n, (θ + A * (1 - θ)) * retry A θ n = A * (1 - ((1 - A) * (1 - θ)) ^ n)
~~~

### 722. retry_le_ratio

Source: proofs/UMDEFERF1.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_le_ratio (A θ : ℝ) (n : ℕ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hD : 0 < θ + A * (1 - θ)) : retry A θ n ≤ A / (θ + A * (1 - θ))
~~~

### 723. retry_limit

Source: proofs/UMDEFERF1.lean:93 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_limit (A θ : ℝ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hD : 0 < θ + A * (1 - θ)) : Tendsto (fun n : ℕ => retry A θ n) atTop (𝓝 (A / (θ + A * (1 - θ))))
~~~

### 724. theta_retry_le

Source: proofs/UMDEFERF1.lean:112 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem theta_retry_le {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ) : θ * retry A θ n ≤ A
~~~

### 725. fc_zero

Source: proofs/UMDEFERF1.lean:121 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_zero (r A θ : ℝ) (b u : ℕ) : finiteCap r A θ b 0 u = 0
~~~

### 726. fc_ge

Source: proofs/UMDEFERF1.lean:124 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_ge (r A θ : ℝ) {b u : ℕ} (n : ℕ) (hbu : b ≤ u) : finiteCap r A θ b n u = retry A θ n
~~~

### 727. fc_lt

Source: proofs/UMDEFERF1.lean:132 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_lt (r A θ : ℝ) {b u : ℕ} (n : ℕ) (hu : u < b) : finiteCap r A θ b (n + 1) u = max (1 - r + r * A) (retry A θ (n + 1 - (b - u)))
~~~

### 728. fc_le_succ

Source: proofs/UMDEFERF1.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_le_succ {r A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (b n u : ℕ) : finiteCap r A θ b n u ≤ finiteCap r A θ b (n + 1) u
~~~

### 729. fc_step

Source: proofs/UMDEFERF1.lean:151 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_step {r A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {b u : ℕ} (n : ℕ) (hu : u < b) : finiteCap r A θ b n (u + 1) ≤ finiteCap r A θ b (n + 1) u
~~~

### 730. catV_eta_one

Source: proofs/UMDEFERF1.lean:174 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catV_eta_one (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (a : Service X Z) (b : ℕ) : ∀ n u h, catV Bad M φ π r 1 a b n u h = cat Bad M φ π r b n u h
~~~

### 731. catV_bounds

Source: proofs/UMDEFERF1.lean:185 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catV_bounds (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η : ℝ) (a : Service X Z) (b : ℕ) (hc : Core M φ π r η) (ha : IsService a) : ∀ n u h, 0 ≤ catV Bad M φ π r η a b n u h ∧ catV Bad M φ π r η a b n u h ≤ 1
~~~

### 732. catD_cap

Source: proofs/UMDEFERF1.lean:221 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catD_cap (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α A : ℝ) (b : ℕ) (hc : Core M φ π r η) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hbad : ∀ x, Bad x → E (M x) φ ≤ A) : ∀ n u h, catD Bad M φ π r η α b n u h ≤ finiteCap r A (theta η α) b n u
~~~

### 733. bridge

Source: proofs/UMDEFERF1.lean:306 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bridge (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α : ℝ) (a : Service X Z) (b n0 u0 : ℕ) (h0 : Hist X Z) (hc : Core M φ π r η) (ha : IsService a) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hfl : UniformFloor Bad M φ π η a b n0 u0 h0 α) : ∀ n u h, Reach Bad M φ π η a b n0 u0 h0 n u h → catV Bad M φ π r η a b n u h ≤ catD Bad M φ π r η α b n u h
~~~

### 734. attain

Source: proofs/UMDEFERF1.lean:382 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attain [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (r η α A : ℝ) (b u : ℕ) (x : X) (hM : IsKernel M) (hx : Bad x) (hbu : b ≤ u) : ∀ n (h : Hist X Z), catD Bad M (fun _ => A) (fun _ x' => if x' = x then 1 else 0) r η α b n u h = retry A (theta η α) n
~~~

### 735. seed_bound

Source: proofs/UMDEFERF1.lean:403 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seed_bound {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r η α L : ℝ) (a : Service X Z) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (hPH : IsDist PH) (hc : Core M φ π r η) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hL : 0 ≤ L) (ha : IsService a) (hfl : UniformFloor Bad M φ π η a b N 0 [] α) (hdom : ∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ surv (push M PH) φ (hardKill ns) nh 0 * catV Bad M φ π r η a b N 0 [] ≤ survH t (hardKill ns) nh 0 * finiteCap r (min 1 (L * t)) (theta η α) b N 0
~~~

### 736. cert

Source: proofs/UMDEFERF1.lean:427 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cert {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r η α L U : ℝ) (a : Ω → Service X Z) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) (hpc : PairCore M PH ρ φ π r η) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hL : 0 ≤ L) (hfl : ProtocolFloor Bad M φ π η a b N α) (hdom : ∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) (hU : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t (hardKill ns) nh 0 * finiteCap r (min 1 (L * t)) (theta η α) b N 0 ≤ U) : protocolCatV Bad M PH (hardKill ns) nh r η a b N ρ φ π ≤ U
~~~

### 737. coarse_bound

Source: proofs/UMDEFERF1.lean:445 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem coarse_bound (r θ L t : ℝ) (b N nh ns : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : survH t (hardKill ns) nh 0 * finiteCap r (min 1 (L * t)) θ b N 0 ≤ max (if 0 < b then (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) else 0) (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)) / θ)
~~~

### 738. cnt_append

Source: proofs/UMDEFERF1.lean:486 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cnt_append (h : Hist Bool Bool) (x z c : Bool) : ((h ++ [(x, z, c)]).filter (fun e => e.2.2 = false)).length = (h.filter (fun e => e.2.2 = false)).length + (if c = false then 1 else 0)
~~~

### 739. attack_phase

Source: proofs/UMDEFERF1.lean:491 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attack_phase (r t : ℝ) (b : ℕ) : ∀ n (u : ℕ) (h : Hist Bool Bool), b ≤ u → b ≤ (h.filter (fun e => e.2.2 = false)).length → catV (X
~~~

### 740. burn_phase

Source: proofs/UMDEFERF1.lean:511 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem burn_phase (r t : ℝ) (b : ℕ) : ∀ n k (u : ℕ) (h : Hist Bool Bool), u = (h.filter (fun e => e.2.2 = false)).length → u + k = b → catV (X
~~~

### 741. nogo_eq

Source: proofs/UMDEFERF1.lean:533 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nogo_eq (PH : Bool → ℝ) (nh ns b N : ℕ) (r t : ℝ) (hPH : IsDist PH) : protocolCatD (X
~~~

### 742. nogo_lb

Source: proofs/UMDEFERF1.lean:549 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nogo_lb (PH : Bool → ℝ) (nh ns b N : ℕ) (t : ℝ) (hPH : IsDist PH) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (1 - t) ^ nh * (1 - (1 - t) ^ (N - b)) ≤ binCDF nh ns (PH true * t) * (1 - (1 - t) ^ (N - b))
~~~

### 743. limit_e

Source: proofs/UMDEFERF1.lean:576 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem limit_e' (nh : ℕ) : Tendsto (fun K : ℕ => (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ nh * (1 - (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ K)) atTop (𝓝 1)
~~~

### 744. claim

Source: proofs/UMDEFERF1.lean:625 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMDEFERF1.Claim
~~~

### 745. witness

Source: proofs/UMDEFERF1.lean:665 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMDEFERF1.Witness
~~~

## proofs/UMHSF1.lean

### 746. mul_le_max0

Source: proofs/UMHSF1.lean:1 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mul_le_max0 (a φ : ℝ) (h0 : 0 ≤ φ) (h1 : φ ≤ 1) : a * φ ≤ max 0 a
~~~

### 747. t2

Source: proofs/UMHSF1.lean:8 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t2 : ∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q φ : Z → ℝ), IsRule φ → E P φ ≤ Real.exp η * E Q φ + hs η P Q
~~~

### 748. t2att

Source: proofs/UMHSF1.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t2att : ∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q : Z → ℝ), ∃ φ, IsRule φ ∧ E P φ = Real.exp η * E Q φ + hs η P Q
~~~

### 749. hs0_symm

Source: proofs/UMHSF1.lean:35 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hs0_symm {Z : Type} [Fintype Z] (P Q : Z → ℝ) (hP : ∑ z, P z = 1) (hQ : ∑ z, Q z = 1) : hs 0 Q P = hs 0 P Q
~~~

### 750. t1

Source: proofs/UMHSF1.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t1 : ∀ (Z : Type) [Fintype Z] (P Q φ : Z → ℝ), IsDist P → IsDist Q → IsRule φ → |E P φ - E Q φ| ≤ hs 0 P Q
~~~

### 751. max0_sum_le

Source: proofs/UMHSF1.lean:60 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem max0_sum_le {X : Type} [Fintype X] (w f : X → ℝ) (hw : ∀ x, 0 ≤ w x) : max 0 (∑ x, w x * f x) ≤ ∑ x, w x * max 0 (f x)
~~~

### 752. t4a

Source: proofs/UMHSF1.lean:66 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4a : ∀ (X Z : Type) [Fintype X] [Fintype Z] (η : ℝ) (K : X → Z → ℝ) (P Q : X → ℝ), IsKernel K → hs η (push K P) (push K Q) ≤ hs η P Q
~~~

### 753. push_contentLaw

Source: proofs/UMHSF1.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_contentLaw {X Z C : Type} [Fintype X] [Fintype C] [DecidableEq C] (K : C → Z → ℝ) (c : X → C) (P : X → ℝ) : push K (contentLaw c P) = push (fun x => K (c x)) P
~~~

### 754. t4b

Source: proofs/UMHSF1.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4b : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η : ℝ) (M : X → Z → ℝ) (c : X → C) (PA PH : X → ℝ), ContentOnly M c → hs η (push M PA) (push M PH) ≤ hs η (contentLaw c PA) (contentLaw c PH)
~~~

### 755. delta_dist

Source: proofs/UMHSF1.lean:106 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem delta_dist {C : Type} [Fintype C] [DecidableEq C] (e : C) : IsDist (delta e)
~~~

### 756. push_decode

Source: proofs/UMHSF1.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_decode {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (P : X → ℝ) : push (fun z => delta (g z)) (push M P) = contentLaw c P
~~~

### 757. t4c

Source: proofs/UMHSF1.lean:126 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4c : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η : ℝ) (M : X → Z → ℝ) (c : X → C) (PA PH : X → ℝ), IsKernel M → ContentPreserving M c → hs η (contentLaw c PA) (contentLaw c PH) ≤ hs η (push M PA) (push M PH)
~~~

### 758. t5d

Source: proofs/UMHSF1.lean:135 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t5d : ∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q P' Q' : Z → ℝ), hs η P Q ≤ hs η P' Q' + ∑ z, max 0 (P z - P' z) + Real.exp η * ∑ z, max 0 (Q' z - Q z)
~~~

### 759. sum_max0_mix

Source: proofs/UMHSF1.lean:153 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_max0_mix {Z C : Type} [Fintype Z] [Fintype C] (w : Z → ℝ) (hw : ∀ z, 0 ≤ w z) (f : Z → C → ℝ) : ∑ e, max 0 (∑ z, w z * f z e) ≤ ∑ z, w z * ∑ e, max 0 (f z e)
~~~

### 760. sum_max0_delta_sub_le

Source: proofs/UMHSF1.lean:161 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_max0_delta_sub_le {C : Type} [Fintype C] [DecidableEq C] (a b : C) : ∑ e, max 0 (delta a e - delta b e) ≤ 1
~~~

### 761. inner_A

Source: proofs/UMHSF1.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inner_A {Z C : Type} [Fintype Z] [Fintype C] [DecidableEq C] (m : Z → ℝ) (hm : IsDist m) (a : C) (g : Z → C) : ∑ e, max 0 (delta a e - ∑ z, m z * delta (g z) e) ≤ ∑ z, m z * (if g z = a then 0 else 1)
~~~

### 762. inner_H

Source: proofs/UMHSF1.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inner_H {Z C : Type} [Fintype Z] [Fintype C] [DecidableEq C] (m : Z → ℝ) (hm : IsDist m) (a : C) (g : Z → C) : ∑ e, max 0 (∑ z, m z * delta (g z) e - delta a e) ≤ ∑ z, m z * (if g z = a then 0 else 1)
~~~

### 763. push_push

Source: proofs/UMHSF1.lean:203 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_push {X Z C : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (D : Z → C → ℝ) (P : X → ℝ) (e : C) : push D (push M P) e = ∑ x, P x * ∑ z, M x z * D z e
~~~

### 764. approx_A

Source: proofs/UMHSF1.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem approx_A {X Z C : Type} [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (γ : ℝ) (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PA : X → ℝ) (hM : IsKernel M) (hPA : IsDist PA) (hγ : ∀ x, ∑ z, M x z * (if g z = c x then 0 else 1) ≤ γ) : ∑ e, max 0 (contentLaw c PA e - push (fun z => delta (g z)) (push M PA) e) ≤ γ
~~~

### 765. approx_H

Source: proofs/UMHSF1.lean:231 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem approx_H {X Z C : Type} [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (γ : ℝ) (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PH : X → ℝ) (hM : IsKernel M) (hPH : IsDist PH) (hγ : ∀ x, ∑ z, M x z * (if g z = c x then 0 else 1) ≤ γ) : ∑ e, max 0 (push (fun z => delta (g z)) (push M PH) e - contentLaw c PH e) ≤ γ
~~~

### 766. t4c_approx

Source: proofs/UMHSF1.lean:250 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4c_approx : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η γ : ℝ) (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PA PH : X → ℝ), IsKernel M → IsDist PA → IsDist PH → (∀ x, ∑ z, M x z * (if g z = c x then 0 else 1) ≤ γ) → hs η (contentLaw c PA) (contentLaw c PH) ≤ hs η (push M PA) (push M PH) + (1 + Real.exp η) * γ
~~~

### 767. t4c'1

Source: proofs/UMHSF1.lean:266 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4c'1 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (B : Finset X) (hB : B.Nonempty) (Q : Z → ℝ) (L : ℝ), IsKernel M → IsDist Q → (∀ x ∈ B, ∀ z, M x z ≤ L * Q z) → ∑ z, B.sup' hB (fun x => M x z) ≤ L
~~~

### 768. t4c'2

Source: proofs/UMHSF1.lean:275 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4c'2 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (B : Finset X) (hB : B.Nonempty), IsKernel M → ∃ Q, IsDist Q ∧ ∀ x ∈ B, ∀ z, M x z ≤ (∑ z', B.sup' hB (fun x' => M x' z')) * Q z
~~~

### 769. dom

Source: proofs/UMHSF1.lean:299 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dom : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (PH : X → ℝ) (Bad : X → Prop) (p : ℝ), ContentOnly M c → IsDist PH → 0 < p → (∀ x, Bad x → p ≤ contentLaw c PH (c x)) → ∀ x, Bad x → ∀ z, M x z ≤ (1 / p) * push M PH z
~~~

### 770. claim

Source: proofs/UMHSF1.lean:320 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 771. idKernel

Source: proofs/UMHSF1.lean:323 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem idKernel : IsKernel (fun (x : Bool) (z : Bool) => if z = x then (1 : ℝ) else 0)
~~~

### 772. witness

Source: proofs/UMHSF1.lean:329 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## proofs/UMLOWERF1.lean

### 773. pat_sum_prod

Source: proofs/UMLOWERF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pat_sum_prod {n : ℕ} (f : Fin n → Bool → ℝ) : ∑ pat : Fin n → Bool, ∏ i, f i (pat i) = ∏ i, ∑ b, f i b
~~~

### 774. bern_nonneg

Source: proofs/UMLOWERF1.lean:7 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bern_nonneg {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (pat : Fin n → Bool) : 0 ≤ ∏ i, (if pat i then a i else 1 - a i)
~~~

### 775. bern_sum

Source: proofs/UMLOWERF1.lean:15 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bern_sum {n : ℕ} (a : Fin n → ℝ) : ∑ pat : Fin n → Bool, ∏ i, (if pat i then a i else 1 - a i) = 1
~~~

### 776. bern_mean

Source: proofs/UMLOWERF1.lean:20 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bern_mean {n : ℕ} (a : Fin n → ℝ) : ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) * ((univ.filter (fun i => pat i = true)).card : ℝ) = ∑ i, a i
~~~

### 777. keep_lb

Source: proofs/UMLOWERF1.lean:49 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem keep_lb (ns : ℕ) (k : ℝ) (m : ℕ) (hk0 : 0 ≤ k) (hk : m ≤ ns → k = 1) : 1 - (m : ℝ) / ((ns : ℝ) + 1) ≤ k
~~~

### 778. inner_lb

Source: proofs/UMLOWERF1.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inner_lb {n : ℕ} (ns : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (kp : (Fin n → Bool) → ℝ) (hk0 : ∀ pat, 0 ≤ kp pat) (hk1 : ∀ pat, (univ.filter (fun i => pat i = true)).card ≤ ns → kp pat = 1) : 1 - (∑ i, a i) / ((ns : ℝ) + 1) ≤ ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) * kp pat
~~~

### 779. inner_nonneg

Source: proofs/UMLOWERF1.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inner_nonneg {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (kp : (Fin n → Bool) → ℝ) (hk0 : ∀ pat, 0 ≤ kp pat) : 0 ≤ ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) * kp pat
~~~

### 780. pass_eq

Source: proofs/UMLOWERF1.lean:82 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pass_eq {X Z C : Type} [Fintype Z] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (t : ℝ) (x ω : X) : ∑ z, M x z * (if g z = c ω then t else 0) = if c x = c ω then t else 0
~~~

### 781. class_sum_le

Source: proofs/UMLOWERF1.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem class_sum_le {X C : Type} [DecidableEq C] (c : X → C) (S : Finset X) (hinj : Set.InjOn c (S : Set X)) (t : ℝ) (ht : 0 ≤ t) (x : X) : ∑ ω ∈ S, (if c x = c ω then t else 0) ≤ t
~~~

### 782. cat_ge

Source: proofs/UMLOWERF1.lean:104 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_ge {X Z : Type} [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (r : ℝ) (b N : ℕ) (ω : X) (hM : IsKernel M) (hφ : IsRule φ) (hr1 : r ≤ 1) (hN : 1 ≤ N) (hω : Bad ω) : ∑ z, M ω z * φ z ≤ cat Bad M φ (fun _ x => if x = ω then 1 else 0) r b N 0 []
~~~

### 783. surv_sum_lb

Source: proofs/UMLOWERF1.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_sum_lb {X Ω : Type} [Fintype X] (n ns : ℕ) (D : (Fin n → X) → ℝ) (hD : IsDist D) (keep : (Fin n → X) → (Fin n → Bool) → ℝ) (hkeep : ∀ xs pat, 0 ≤ keep xs pat) (hkeep1 : ∀ xs pat, (univ.filter (fun i => pat i = true)).card ≤ ns → keep xs pat = 1) (S : Finset Ω) (a : Ω → X → ℝ) (ha : ∀ ω x, 0 ≤ a ω x ∧ a ω x ≤ 1) (t : ℝ) (hsumA : ∀ x, ∑ ω ∈ S, a ω x ≤ t) : (S.card : ℝ) - n * t / ((ns : ℝ) + 1) ≤ ∑ ω ∈ S, ∑ xs, D xs * ∑ pat : Fin n → Bool, (∏ i, (if pat i then a ω (xs i) else 1 - a ω (xs i))) * keep xs pat
~~~

### 784. combine

Source: proofs/UMLOWERF1.lean:151 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem combine {X : Type} [Fintype X] [DecidableEq X] (S : Finset X) (n ns : ℕ) (sv ct : X → ℝ) (t : ℝ) (hS : 0 < S.card) (ht : 0 ≤ t) (hsv0 : ∀ ω, 0 ≤ sv ω) (hct : ∀ ω ∈ S, t ≤ ct ω) (hsum : (S.card : ℝ) - n * t / ((ns : ℝ) + 1) ≤ ∑ ω ∈ S, sv ω) : t * (1 - t * (n : ℝ) / ((S.card : ℝ) * ((ns : ℝ) + 1))) ≤ ∑ ω, (if ω ∈ S then 1 / (S.card : ℝ) else 0) * sv ω * ct ω
~~~

### 785. claim

Source: proofs/UMLOWERF1.lean:176 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMLOWERF1.Claim
~~~

### 786. none_pass

Source: proofs/UMLOWERF1.lean:227 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem none_pass {n : ℕ} (a : Fin n → ℝ) : ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) * (if (univ.filter (fun i => pat i = true)).card ≤ 0 then (1 : ℝ) else 0) = ∏ i, (1 - a i)
~~~

### 787. witness

Source: proofs/UMLOWERF1.lean:252 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMLOWERF1.Witness
~~~

## proofs/UMNOGOF1.lean

### 788. submit_sum

Source: proofs/UMNOGOF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma submit_sum {X Z : Type} [Fintype X] (xs : X) (ω : Unit) (h : Hist X Z) (f : X → ℝ) : ∑ x, submit (Z
~~~

### 789. submit_dist

Source: proofs/UMNOGOF1.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma submit_dist {X Z : Type} [Fintype X] (xs : X) (ω : Unit) (h : Hist X Z) : IsDist (submit (Z
~~~

### 790. classMonitor_rule

Source: proofs/UMNOGOF1.lean:22 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma classMonitor_rule {Z C : Type} [DecidableEq C] (g : Z → C) (e : C) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : ∀ ω, IsRule (classMonitor g e t ω)
~~~

### 791. protocolCat_unit

Source: proofs/UMNOGOF1.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma protocolCat_unit {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (φ : Unit → Z → ℝ) (π : Unit → Hist X Z → X → ℝ) : protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) φ π = surv (push M PH) (φ ()) κ nh 0 * cat Bad M (φ ()) (π ()) r b N 0 []
~~~

### 792. cat_submit

Source: proofs/UMNOGOF1.lean:39 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma cat_submit {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (xs : X) (hx : Bad xs) (r : ℝ) (b N : ℕ) (hN : 1 ≤ N) : cat Bad M φ (submit (Z
~~~

### 793. rate_eq

Source: proofs/UMNOGOF1.lean:47 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma rate_eq {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (PH : X → ℝ) (e : C) (t : ℝ) : ∑ z, push M PH z * classMonitor g e t () z = t * contentLaw c PH e
~~~

### 794. pass_sum

Source: proofs/UMNOGOF1.lean:70 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma pass_sum {X Z C : Type} [Fintype Z] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (xs : X) (t K : ℝ) : ∑ z, M xs z * (classMonitor g (c xs) t () z * 1 + (1 - classMonitor g (c xs) t () z) * K) = t + (1 - t) * K
~~~

### 795. prot_formula

Source: proofs/UMNOGOF1.lean:82 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma prot_formula {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PH : X → ℝ) (xs : X) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (hPH : IsDist PH) (hx : Bad xs) (t : ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (hN : 1 ≤ N) : protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (classMonitor g (c xs) t) (submit (Z
~~~

### 796. survH_ge

Source: proofs/UMNOGOF1.lean:93 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma survH_ge (h : ℝ) (κ : ℕ → ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1) : ∀ n j, (1 - h) ^ n ≤ survH h κ n j
~~~

### 797. contentLaw_nonneg

Source: proofs/UMNOGOF1.lean:112 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma contentLaw_nonneg {X C : Type} [Fintype X] [DecidableEq C] (c : X → C) (PH : X → ℝ) (hPH : IsDist PH) (e : C) : 0 ≤ contentLaw c PH e
~~~

### 798. classes_sum_le

Source: proofs/UMNOGOF1.lean:122 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma classes_sum_le {X C : Type} [Fintype X] [DecidableEq C] (c : X → C) (PH : X → ℝ) (hPH : IsDist PH) (S : Finset X) (hinj : Set.InjOn c (S : Set X)) : ∑ x ∈ S, contentLaw c PH (c x) ≤ 1
~~~

### 799. claim

Source: proofs/UMNOGOF1.lean:145 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMNOGOF1.Claim
~~~

### 800. witnessM_kernel

Source: proofs/UMNOGOF1.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witnessM_kernel : IsKernel witnessM
~~~

### 801. witnessM_dec

Source: proofs/UMNOGOF1.lean:195 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witnessM_dec : ∀ x z, witnessM x z ≠ 0 → (id : Fin 4 → Fin 4) z = id x
~~~

### 802. witnessPH_dist

Source: proofs/UMNOGOF1.lean:202 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witnessPH_dist : IsDist witnessPH
~~~

### 803. witness_content

Source: proofs/UMNOGOF1.lean:209 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witness_content : contentLaw (id : Fin 4 → Fin 4) witnessPH 2 = 1 / 4
~~~

### 804. witnessS_card

Source: proofs/UMNOGOF1.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witnessS_card : witnessS.card = 4
~~~

### 805. witness

Source: proofs/UMNOGOF1.lean:215 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMNOGOF1.Witness
~~~

## proofs/UMPROTF1.lean

### 806. wsum_le

Source: proofs/UMPROTF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum_le {Y : Type} [Fintype Y] (w f : Y → ℝ) (c : ℝ) (hw : IsDist w) (hf : ∀ y, f y ≤ c) : ∑ y, w y * f y ≤ c
~~~

### 807. wsum_nonneg

Source: proofs/UMPROTF1.lean:9 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum_nonneg {Y : Type} [Fintype Y] (w f : Y → ℝ) (hw : ∀ y, 0 ≤ w y) (hf : ∀ y, 0 ≤ f y) : 0 ≤ ∑ y, w y * f y
~~~

### 808. t3a

Source: proofs/UMPROTF1.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t3a {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r A : ℝ) (b : ℕ) (hM : IsKernel M) (hφ : IsRule φ) (hπ : ∀ h, IsDist (π h)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hbad : ∀ x, Bad x → E (M x) φ ≤ A) : ∀ n u h, 0 ≤ cat Bad M φ π r b n u h ∧ cat Bad M φ π r b n u h ≤ (if u < b then 1 - r + r * A else A)
~~~

### 809. cat_le

Source: proofs/UMPROTF1.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_le {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r A : ℝ) (b : ℕ) (hM : IsKernel M) (hφ : IsRule φ) (hπ : ∀ h, IsDist (π h)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hbad : ∀ x, Bad x → E (M x) φ ≤ A) (n u : ℕ) (h : Hist X Z) : 0 ≤ cat Bad M φ π r b n u h ∧ cat Bad M φ π r b n u h ≤ 1 - r + r * A
~~~

### 810. push_dist

Source: proofs/UMPROTF1.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_dist {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (hM : IsKernel M) (hP : IsDist PH) : IsDist (push M PH)
~~~

### 811. prot_bound

Source: proofs/UMPROTF1.lean:108 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prot_bound {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) (C : ℝ) (hM : IsKernel M) (hρ : IsDist ρ) (hφ : ∀ ω, IsRule (φ ω)) (hπ : ∀ ω h, IsDist (π ω h)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hω : ∀ ω, ∃ A, 0 ≤ A ∧ A ≤ 1 ∧ (∀ x, Bad x → E (M x) (φ ω) ≤ A) ∧ 0 ≤ surv (push M PH) (φ ω) κ nh 0 ∧ surv (push M PH) (φ ω) κ nh 0 * (1 - r + r * A) ≤ C) : protocolCat Bad M PH κ nh r b N ρ φ π ≤ C
~~~

### 812. rate_facts

Source: proofs/UMPROTF1.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rate_facts {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (φ : Z → ℝ) (hM : IsKernel M) (hP : IsDist PH) (hφ : IsRule φ) : 0 ≤ ∑ z, push M PH z * φ z ∧ ∑ z, push M PH z * φ z ≤ 1
~~~

### 813. E_le_one

Source: proofs/UMPROTF1.lean:133 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_le_one {X Z : Type} [Fintype Z] (M : X → Z → ℝ) (φ : Z → ℝ) (hM : IsKernel M) (hφ : IsRule φ) (x : X) : E (M x) φ ≤ 1
~~~

### 814. surv_eq

Source: proofs/UMPROTF1.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_eq {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (φ : Z → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (hM : IsKernel M) (hP : IsDist PH) : surv (push M PH) φ κ nh 0 = survH (∑ z, push M PH z * φ z) κ nh 0
~~~

### 815. final_dom

Source: proofs/UMPROTF1.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem final_dom (S h L r A B : ℝ) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hA : A ≤ L * h) (hB : h * S ≤ B) : S * (1 - r + r * A) ≤ (1 - r) + r * (L * B)
~~~

### 816. final_hs

Source: proofs/UMPROTF1.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem final_hs (S h r A δ c B : ℝ) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hA : A ≤ c * h + δ) (hB : h * S ≤ B) : S * (1 - r + r * A) ≤ (1 - r) + r * (δ + c * B)
~~~

### 817. hardKill_prob

Source: proofs/UMPROTF1.lean:170 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hardKill_prob (ns : ℕ) : ∀ i, 0 ≤ hardKill ns i ∧ hardKill ns i ≤ 1
~~~

### 818. E_dom

Source: proofs/UMPROTF1.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_dom {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (φ : Z → ℝ) (hφ : IsRule φ) (L : ℝ) (x : X) (hd : ∀ z, M x z ≤ L * push M PH z) : E (M x) φ ≤ L * ∑ z, push M PH z * φ z
~~~

### 819. claim

Source: proofs/UMPROTF1.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMPROTF1.Claim
~~~

### 820. witness

Source: proofs/UMPROTF1.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMPROTF1.Witness
~~~

## proofs/UMSTRATF1.lean

### 821. surv_eq_bin

Source: proofs/UMSTRATF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_eq_bin {Z : Type} [Fintype Z] (q φ : Z → ℝ) (hq : ∑ z, q z = 1) (m sc : ℕ) : surv q φ (hardKill sc) m 0 = binCDF m sc (E q φ)
~~~

### 822. rate01

Source: proofs/UMSTRATF1.lean:9 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rate01 {Z : Type} [Fintype Z] (q φ : Z → ℝ) (hq : IsDist q) (hφ : IsRule φ) : 0 ≤ E q φ ∧ E q φ ≤ 1
~~~

### 823. factor01

Source: proofs/UMSTRATF1.lean:14 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem factor01 {Z : Type} [Fintype Z] (q φ : Z → ℝ) (hq : IsDist q) (hφ : IsRule φ) (m sc : ℕ) : 0 ≤ surv q φ (hardKill sc) m 0 ∧ surv q φ (hardKill sc) m 0 ≤ 1
~~~

### 824. strat01

Source: proofs/UMSTRATF1.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem strat01 {Z C : Type} [Fintype Z] (K : C → Z → ℝ) (Es : Finset C) (φ : Z → ℝ) (m sc : ℕ) (hK : IsKernel K) (hφ : IsRule φ) : 0 ≤ stratSurv K Es φ m sc ∧ stratSurv K Es φ m sc ≤ 1
~~~

### 825. strat_le_factor

Source: proofs/UMSTRATF1.lean:31 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem strat_le_factor {Z C : Type} [Fintype Z] (K : C → Z → ℝ) (Es : Finset C) (φ : Z → ℝ) (m sc : ℕ) (hK : IsKernel K) (hφ : IsRule φ) (e : C) (he : e ∈ Es) : stratSurv K Es φ m sc ≤ surv (K e) φ (hardKill sc) m 0
~~~

### 826. exists_A

Source: proofs/UMSTRATF1.lean:44 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exists_A {X Z C : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (φ : Z → ℝ) (m sc : ℕ) (hK : IsKernel K) (hφ : IsRule φ) (hEs : ∀ x, Bad x → c x ∈ Es) : ∃ A, 0 ≤ A ∧ A ≤ 1 ∧ (∀ x, Bad x → E (K (c x)) φ ≤ A) ∧ A * stratSurv K Es φ m sc ≤ ((sc : ℝ) + 1) / ((m : ℝ) + 1)
~~~

### 827. claim1

Source: proofs/UMSTRATF1.lean:72 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim1 : ∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r : ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 → (∀ x, Bad x → c x ∈ Es) → stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ (1 - r) + r * (((sc : ℝ) + 1) / ((m : ℝ) + 1))
~~~

### 828. binCDF_at_zero

Source: proofs/UMSTRATF1.lean:98 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem binCDF_at_zero (m sc : ℕ) : binCDF m sc 0 = 1
~~~

### 829. E_dec

Source: proofs/UMSTRATF1.lean:103 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_dec {Z C : Type} [Fintype Z] [DecidableEq C] (K : C → Z → ℝ) (g : Z → C) (t : ℝ) (e0 e : C) (hK : IsKernel K) (hdec : ∀ e z, K e z ≠ 0 → g z = e) : E (K e) (fun z => if g z = e0 then t else 0) = if e = e0 then t else 0
~~~

### 830. strat_att

Source: proofs/UMSTRATF1.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem strat_att {Z C : Type} [Fintype Z] [DecidableEq C] (K : C → Z → ℝ) (g : Z → C) (Es : Finset C) (t : ℝ) (e0 : C) (m sc : ℕ) (hK : IsKernel K) (hdec : ∀ e z, K e z ≠ 0 → g z = e) (he0 : e0 ∈ Es) : stratSurv K Es (fun z => if g z = e0 then t else 0) m sc = binCDF m sc t
~~~

### 831. cat_point

Source: proofs/UMSTRATF1.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_point {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] [DecidableEq X] (M : X → Z → ℝ) (φ : Z → ℝ) (r : ℝ) (b N : ℕ) (x : X) (hM : IsKernel M) (hx : Bad x) (hN : 1 ≤ N) (hb : 1 ≤ b) : cat Bad M φ (fun _ x' => if x' = x then 1 else 0) r b N 0 [] = 1 - r + r * E (M x) φ
~~~

### 832. claim2

Source: proofs/UMSTRATF1.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim2 : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq C] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (g : Z → C) (Es : Finset C) (m sc b N : ℕ) (r t : ℝ) (x : X), IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → Bad x → c x ∈ Es → 1 ≤ N → 1 ≤ b → 0 ≤ t → t ≤ 1 → stratProtocolCat Bad K c Es m sc r b N (fun _ : Unit => 1) (fun _ z => if g z = c x then t else 0) (fun _ _ x' => if x' = x then 1 else 0) = binCDF m sc t * (1 - r + r * t)
~~~

### 833. claim

Source: proofs/UMSTRATF1.lean:166 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMSTRATF1.Claim
~~~

### 834. wK

Source: proofs/UMSTRATF1.lean:168 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wK : IsKernel witnessK
~~~

### 835. wdec

Source: proofs/UMSTRATF1.lean:176 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wdec : ∀ e z : Bool, witnessK e z ≠ 0 → id z = e
~~~

### 836. wval

Source: proofs/UMSTRATF1.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wval : stratProtocolCat (fun x : Bool => x = true) witnessK id (Finset.univ : Finset Bool) 12 1 1 1 1 (fun _ : Unit => 1) witnessPhi witnessPi = binCDF 12 1 (1 / 6) * (1 - 1 + 1 * (1 / 6 : ℝ))
~~~

### 837. wbin

Source: proofs/UMSTRATF1.lean:190 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wbin : binCDF 12 1 (1 / 6 : ℝ) = (5 / 6) ^ 12 + 12 * (1 / 6) * (5 / 6) ^ 11
~~~

### 838. witness

Source: proofs/UMSTRATF1.lean:194 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMSTRATF1.Witness
~~~

## proofs/UMSURVF1.lean

### 839. binTerm_pascal

Source: proofs/UMSURVF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binTerm_pascal (n k : ℕ) (h : ℝ) : ((n + 1).choose (k + 1) : ℝ) * h ^ (k + 1) * (1 - h) ^ (n + 1 - (k + 1)) = h * ((n.choose k : ℝ) * h ^ k * (1 - h) ^ (n - k)) + (1 - h) * ((n.choose (k + 1) : ℝ) * h ^ (k + 1) * (1 - h) ^ (n - (k + 1)))
~~~

### 840. binCDF_zero_n

Source: proofs/UMSURVF1.lean:21 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binCDF_zero_n (s : ℕ) (h : ℝ) : binCDF 0 s h = 1
~~~

### 841. binCDF_n_zero

Source: proofs/UMSURVF1.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binCDF_n_zero (n : ℕ) (h : ℝ) : binCDF n 0 h = (1 - h) ^ n
~~~

### 842. binCDF_pascal

Source: proofs/UMSURVF1.lean:34 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binCDF_pascal (n s : ℕ) (h : ℝ) : binCDF (n + 1) (s + 1) h = (1 - h) * binCDF n (s + 1) h + h * binCDF n s h
~~~

### 843. survH_hard

Source: proofs/UMSURVF1.lean:43 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma survH_hard (h : ℝ) (ns : ℕ) : ∀ n j, j ≤ ns → survH h (hardKill ns) n j = binCDF n (ns - j) h
~~~

### 844. survH_const

Source: proofs/UMSURVF1.lean:66 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma survH_const (h k : ℝ) : ∀ (n j : ℕ), survH h (fun _ => k) n j = (1 - k * h) ^ n
~~~

### 845. survH_prob

Source: proofs/UMSURVF1.lean:75 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma survH_prob (h : ℝ) (κ : ℕ → ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ 1) : ∀ n j, 0 ≤ survH h κ n j ∧ survH h κ n j ≤ 1
~~~

### 846. binCDF_le_one

Source: proofs/UMSURVF1.lean:99 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binCDF_le_one (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : binCDF n s h ≤ 1
~~~

### 847. first_moment

Source: proofs/UMSURVF1.lean:106 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma first_moment (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : ((n : ℝ) + 1) * (h * binCDF n s h) ≤ (s : ℝ) + 1
~~~

### 848. first_moment

Source: proofs/UMSURVF1.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma first_moment' (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : h * binCDF n s h ≤ ((s : ℝ) + 1) / ((n : ℝ) + 1)
~~~

### 849. claim

Source: proofs/UMSURVF1.lean:152 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 850. witness

Source: proofs/UMSURVF1.lean:191 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## proofs/UMUSEF1.lean

### 851. usef_split

Source: proofs/UMUSEF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_split {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (μ : X → ℝ) (φ : Z → ℝ) (hM : IsKernel M) (hμ : IsDist μ) (A B : ℝ) : ∑ x, μ x * ∑ z, M x z * (φ z * A + (1 - φ z) * B) = (1 - flagRate M μ φ) * A + flagRate M μ φ * B
~~~

### 852. usef_flag01

Source: proofs/UMUSEF1.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_flag01 {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (μ : X → ℝ) (φ : Z → ℝ) (hM : IsKernel M) (hφ : IsRule φ) (hμ : IsDist μ) : 0 ≤ flagRate M μ φ ∧ flagRate M μ φ ≤ 1
~~~

### 853. usef_halt

Source: proofs/UMUSEF1.lean:37 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_halt {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (μ : X → ℝ) (b : ℕ) (hM : IsKernel M) (hμ : IsDist μ) (hsupp : ∀ x, μ x ≠ 0 → ¬ Bad x) : ∀ n u h, 1 - haltP Bad M φ (fun _ => μ) b n u h = survH (flagRate M μ φ) (hardKill b) n u
~~~

### 854. usef_bin01

Source: proofs/UMUSEF1.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_bin01 (n s : ℕ) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : 0 ≤ binCDF n s a ∧ binCDF n s a ≤ 1
~~~

### 855. usef_hc

Source: proofs/UMUSEF1.lean:80 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_hc {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh b N : ℕ) (φ₀ : Z → ℝ) (μ : X → ℝ) (hM : IsKernel M) (hP : IsDist PH) (hμ : IsDist μ) (hsupp : ∀ x, μ x ≠ 0 → ¬ Bad x) : honestCompletion Bad M PH κ nh b N φ₀ μ = survH (missRate M PH φ₀) κ nh 0 * binCDF N b (flagRate M μ φ₀)
~~~

### 856. usef_vb

Source: proofs/UMUSEF1.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_vb {X Z : Type} [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r h : ℝ) (b N : ℕ) (x : X) (hM : IsKernel M) (hP : IsDist PH) (hx : Bad x) (hN : 1 ≤ N) : viewBlindRisk Bad M PH κ nh r b N h x = survH h κ nh 0 * (h + (if 0 < b then (1 - r) * (1 - h) else 0))
~~~

### 857. usefB_nonneg

Source: proofs/UMUSEF1.lean:120 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_nonneg (n : ℕ) (a : ℝ) (j : ℕ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : 0 ≤ usefB n a j
~~~

### 858. usefB_step

Source: proofs/UMUSEF1.lean:123 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_step (n : ℕ) (a : ℝ) (g : ℕ → ℝ) : ∑ j ∈ range (n + 1 + 1), usefB (n + 1) a j * g j = (1 - a) * ∑ j ∈ range (n + 1), usefB n a j * g j + a * ∑ j ∈ range (n + 1), usefB n a j * g (j + 1)
~~~

### 859. usefB_m0

Source: proofs/UMUSEF1.lean:154 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_m0 (a : ℝ) : ∀ n : ℕ, ∑ j ∈ range (n + 1), usefB n a j = 1
~~~

### 860. usefB_m1

Source: proofs/UMUSEF1.lean:164 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_m1 (a : ℝ) : ∀ n : ℕ, ∑ j ∈ range (n + 1), usefB n a j * (j : ℝ) = n * a
~~~

### 861. usefB_m2

Source: proofs/UMUSEF1.lean:181 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_m2 (a : ℝ) : ∀ n : ℕ, ∑ j ∈ range (n + 1), usefB n a j * (j : ℝ) ^ 2 = n * a * (1 - a) + (n * a) ^ 2
~~~

### 862. usefB_var

Source: proofs/UMUSEF1.lean:200 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_var (a c : ℝ) (n : ℕ) : ∑ j ∈ range (n + 1), usefB n a j * ((j : ℝ) - c) ^ 2 = n * a * (1 - a) + (n * a - c) ^ 2
~~~

### 863. usefB_ext

Source: proofs/UMUSEF1.lean:210 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_ext (n K : ℕ) (a : ℝ) (g : ℕ → ℝ) (hK : n + 1 ≤ K) : ∑ j ∈ range K, usefB n a j * g j = ∑ j ∈ range (n + 1), usefB n a j * g j
~~~

### 864. usef_cant_alg

Source: proofs/UMUSEF1.lean:220 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_cant_alg (d σ W : ℝ) (hd : 0 < d) (hσ : 0 ≤ σ) (hW : 0 ≤ W) (h : ∀ t, 0 ≤ t → (d + t) ^ 2 * W ≤ σ + t ^ 2) : d ^ 2 * W ≤ σ * (1 - W)
~~~

### 865. usef_lower

Source: proofs/UMUSEF1.lean:246 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_lower (n s : ℕ) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : (max 0 ((n : ℝ) * a - s)) ^ 2 * binCDF n s a ≤ n * a * (1 - a) * (1 - binCDF n s a)
~~~

### 866. usef_upper

Source: proofs/UMUSEF1.lean:284 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_upper (n s : ℕ) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : (max 0 ((s : ℝ) + 1 - n * a)) ^ 2 * (1 - binCDF n s a) ≤ n * a * (1 - a) * binCDF n s a
~~~

### 867. usef_cat_r

Source: proofs/UMUSEF1.lean:337 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_cat_r {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r r' : ℝ) : ∀ n u h, cat Bad M φ π r 0 n u h = cat Bad M φ π r' 0 n u h
~~~

### 868. claim

Source: proofs/UMUSEF1.lean:349 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMUSEF1.Claim
~~~

### 869. wM_k

Source: proofs/UMUSEF1.lean:486 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wM_k : IsKernel wM
~~~

### 870. wPH_d

Source: proofs/UMUSEF1.lean:494 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wPH_d : IsDist wPH
~~~

### 871. w_supp

Source: proofs/UMUSEF1.lean:518 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_supp : ∀ x, wμ x ≠ 0 → ¬ x = true
~~~

### 872. w_miss

Source: proofs/UMUSEF1.lean:524 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_miss : missRate wM wPH wφ = 9 / 40
~~~

### 873. w_flag

Source: proofs/UMUSEF1.lean:528 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_flag : flagRate wM wμ wφ = 13 / 40
~~~

### 874. w_hs

Source: proofs/UMUSEF1.lean:532 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_hs : hs 0 (push wM wμ) (push wM wPH) = 1 / 2
~~~

### 875. witness

Source: proofs/UMUSEF1.lean:536 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMUSEF1.Witness
~~~

## Reviewer obligations

Check fully elaborated Lean goals and quantified premises; inspect what Bad, observations, harm, authority and budgets mean; review model-to-runtime correspondence independently.
