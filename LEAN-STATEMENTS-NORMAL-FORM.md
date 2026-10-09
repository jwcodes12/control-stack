# All Lean statements — source-normalized review catalog

Every indexed theorem and lemma is listed with its source statement, registry metadata and source location; no proof bodies. This is NOT kernel-elaborated normal form: inherited section variables, typeclasses, namespace elaboration, coercions and definitions can hide important premises. Run Lean #print and #print axioms for authoritative statements. No deployment assurance is implied.

Indexed declarations: 1297; UNKNOWN adversary: 1231; SOURCE_ONLY: 1265.

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

## ControlStack/Core/Cert.lean

### 68. AllHold.append

Source: ControlStack/Core/Cert.lean:69 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem AllHold.append {ps qs : List Premise} (h : AllHold (ps ++ qs)) : AllHold ps ∧ AllHold qs
~~~

### 69. AllHold.cons

Source: ControlStack/Core/Cert.lean:72 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem AllHold.cons {p : Premise} {ps : List Premise} (h : AllHold (p :: ps)) : p.holds ∧ AllHold ps
~~~

### 70. prob_nonneg

Source: ControlStack/Core/Cert.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prob_nonneg (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (A : Ω → Prop) : 0 ≤ prob μ A
~~~

### 71. prob_mono

Source: ControlStack/Core/Cert.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prob_mono (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (A B : Ω → Prop) (h : ∀ ω, A ω → B ω) : prob μ A ≤ prob μ B
~~~

### 72. prob_or_le

Source: ControlStack/Core/Cert.lean:101 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prob_or_le (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (A B : Ω → Prop) : prob μ (fun ω => A ω ∨ B ω) ≤ prob μ A + prob μ B
~~~

### 73. prob_empty

Source: ControlStack/Core/Cert.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prob_empty (μ : Ω → ℝ) (A : Ω → Prop) (h : ∀ ω, ¬A ω) : prob μ A = 0
~~~

### 74. product_needs_independence

Source: ControlStack/Core/Cert.lean:166 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem product_needs_independence : prob Necessity.scoreLaw (fun s => s = false) = 1 / 10 ∧ prob Necessity.scoreLaw (fun s => s = false ∧ s = false) = 1 / 10 ∧ (1 / 10 : ℝ) * (1 / 10) < prob Necessity.scoreLaw (fun s => s = false ∧ s = false) ∧ prob Necessity.scoreLaw (fun s => s = false ∧ s = false) ≠ prob Necessity.scoreLaw (fun s => s = false) * prob Necessity.scoreLaw (fun s => s = false)
~~~

### 75. f6_of

Source: ControlStack/Core/Cert.lean:254 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem f6_of (Bh : ℕ) (r : ℝ) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hp : AllHold (f6Premises Bh r K σ)) : (∀ g, IsDist (σ g)) ∧ (∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) ∧ (∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) ∧ (∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1))
~~~

### 76. design_attack_rounds

Source: ControlStack/Core/Cert.lean:335 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem design_attack_rounds : ∑ j ∈ range 100, hypMiss 100 10 (j + 1) (1 / 2) ≤ 19
~~~

### 77. stack_sound

Source: ControlStack/Core/Cert.lean:360 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stack_sound (μ : Ω → ℝ) (R : SC26.Roles) (cap : ℕ) (C : SC26.Checks) (trace : Ω → List SC26.Op) (y0 : Y) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (D F G : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (hG : 0 ≤ G) (dmg : List (AOut Unit) → ℝ) (T t0 e0 G' : ℕ) (e lat ep : ℕ → ℕ → ℕ) (hp : AllHold (stackExample μ R cap C trace y0 K σ D F G hD hF hG dmg T t0 e0 G' e lat ep).premises) : ∀ c ∈ (stackExample μ R cap C trace y0 K σ D F G hD hF hG dmg T t0 e0 G' e lat ep).claims, c.2
~~~

### 78. stack_claims

Source: ControlStack/Core/Cert.lean:369 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stack_claims (μ : Ω → ℝ) (R : SC26.Roles) (cap : ℕ) (C : SC26.Checks) (trace : Ω → List SC26.Op) (y0 : Y) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (D F G : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (hG : 0 ≤ G) (dmg : List (AOut Unit) → ℝ) (T t0 e0 G' : ℕ) (e lat ep : ℕ → ℕ → ℕ) (hp : AllHold (stackExample μ R cap C trace y0 K σ D F G hD hF hG dmg T t0 e0 G' e lat ep).premises) : prob μ (fun ω => ¬ SC26.Good R cap (SC26.run R cap C SC26.init (trace ω))) ≤ 0 ∧ ∑ S : Finset (Fin 100), pU 100 10 S * val (K S) (fun t => (DamageBound.ucX 100 t : ℝ)) 100 [] ≤ 19 ∧ ∑ S : Finset (Fin 100), pU 100 10 S * val (K S) dmg 100 [] ≤ Min.min G (D * 19 + F) ∧ (((DistributedHalt.sinkRun true t0 1 e0 G' (DistributedHalt.stream 1000 T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) : ℕ) : ℝ) ≤ Min.min (G' : ℝ) 10000 ∧ (((DistributedHalt.sinkRun true t0 1 e0 G' (DistributedHalt.stream 1000 T e lat ep)).countP (fun ev => decide (t0 + 1 ≤ ev.1)) : ℕ) : ℝ) ≤ 0
~~~

### 79. stack_ledger_eq

Source: ControlStack/Core/Cert.lean:417 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stack_ledger_eq (μ : Ω → ℝ) (R : SC26.Roles) (cap : ℕ) (C : SC26.Checks) (trace : Ω → List SC26.Op) (y0 : Y) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (D F G : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (hG : 0 ≤ G) (dmg : List (AOut Unit) → ℝ) (T t0 e0 G' : ℕ) (e lat ep : ℕ → ℕ → ℕ) : ledger (stackExample μ R cap C trace y0 K σ D F G hD hF hG dmg T t0 e0 G' e lat ep).premises = stackLedger
~~~

## ControlStack/Core/Compose.lean

### 80. lefts_append

Source: ControlStack/Core/Compose.lean:39 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem lefts_append (l m : List (Eff₁ ⊕ Eff₂)) : lefts (l ++ m) = lefts l ++ lefts m
~~~

### 81. rights_append

Source: ControlStack/Core/Compose.lean:42 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem rights_append (l m : List (Eff₁ ⊕ Eff₂)) : rights (l ++ m) = rights l ++ rights m
~~~

### 82. lefts_inl

Source: ControlStack/Core/Compose.lean:45 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem lefts_inl (l : List Eff₁) : lefts (l.map (Sum.inl : Eff₁ → Eff₁ ⊕ Eff₂)) = l
~~~

### 83. rights_inl

Source: ControlStack/Core/Compose.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem rights_inl (l : List Eff₁) : rights (l.map (Sum.inl : Eff₁ → Eff₁ ⊕ Eff₂)) = []
~~~

### 84. lefts_inr

Source: ControlStack/Core/Compose.lean:51 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem lefts_inr (l : List Eff₂) : lefts (l.map (Sum.inr : Eff₂ → Eff₁ ⊕ Eff₂)) = []
~~~

### 85. rights_inr

Source: ControlStack/Core/Compose.lean:54 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem rights_inr (l : List Eff₂) : rights (l.map (Sum.inr : Eff₂ → Eff₁ ⊕ Eff₂)) = l
~~~

### 86. append_newEffects

Source: ControlStack/Core/Compose.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem append_newEffects {St Op Eff : Type} (G : System St Op Eff) (s s' : St) (h : G.effects s <+: G.effects s') : G.effects s ++ newEffects G s s' = G.effects s'
~~~

### 87. prodInit_coherent

Source: ControlStack/Core/Compose.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prodInit_coherent (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (s₁ : St₁) (s₂ : St₂) : Coherent G₁ G₂ (prodInit G₁ G₂ s₁ s₂)
~~~

### 88. stepL_coherent

Source: ControlStack/Core/Compose.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stepL_coherent (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (p : PSt St₁ St₂ Eff₁ Eff₂) (s' : St₁) (hc : Coherent G₁ G₂ p) (hpre : G₁.effects p.s₁ <+: G₁.effects s') : Coherent G₁ G₂ (stepL G₁ p s')
~~~

### 89. stepR_coherent

Source: ControlStack/Core/Compose.lean:108 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stepR_coherent (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (p : PSt St₁ St₂ Eff₁ Eff₂) (s' : St₂) (hc : Coherent G₁ G₂ p) (hpre : G₂.effects p.s₂ <+: G₂.effects s') : Coherent G₁ G₂ (stepR G₂ p s')
~~~

### 90. tagOk_of_coherent

Source: ControlStack/Core/Compose.lean:121 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tagOk_of_coherent {G₁ : System St₁ Op₁ Eff₁} {G₂ : System St₂ Op₂ Eff₂} (S₁ : Spec G₁) (S₂ : Spec G₂) (p : PSt St₁ St₂ Eff₁ Eff₂) (h1 : S₁.Inv p.s₁) (h2 : S₂.Inv p.s₂) (hc : Coherent G₁ G₂ p) : ∀ e ∈ p.log, tagOk S₁ S₂ p e
~~~

### 91. prod_trace_safe

Source: ControlStack/Core/Compose.lean:153 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prod_trace_safe {G₁ : System St₁ Op₁ Eff₁} {G₂ : System St₂ Op₂ Eff₂} (S₁ : Spec G₁) (S₂ : Spec G₂) (s₁ : St₁) (s₂ : St₂) (h1 : S₁.Inv s₁) (h2 : S₂.Inv s₂) (ops : List (Op₁ ⊕ Op₂)) : let p
~~~

### 92. prod_halt_freezes

Source: ControlStack/Core/Compose.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prod_halt_freezes (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (p : PSt St₁ St₂ Eff₁ Eff₂) (ops : List (HOp (Op₁ ⊕ Op₂))) : let q
~~~

### 93. separate_halt_leaves_other_running

Source: ControlStack/Core/Compose.lean:189 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem separate_halt_leaves_other_running : let q
~~~

### 94. admissible_of_step

Source: ControlStack/Core/Compose.lean:238 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem admissible_of_step {G₁ : System St₁ Op₁ Eff₁} {G₂ : System St₂ Op₂ Eff₂} (S₁ : Spec G₁) (S₂ : Spec G₂) (b : St₁ → St₂ → St₂) (f : St₁ → St₂ → Op₂) (hb : ∀ s₁ s₂, b s₁ s₂ = G₂.step s₂ (f s₁ s₂)) : BridgeAdmissible S₁ S₂ b
~~~

### 95. bridge_breaks_joint

Source: ControlStack/Core/Compose.lean:275 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bridge_breaks_joint : let p
~~~

## ControlStack/Core/Gate.lean

### 96. System.run_nil

Source: ControlStack/Core/Gate.lean:41 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem System.run_nil {St Op Eff : Type} (G : System St Op Eff) (s : St) : G.run s [] = s
~~~

### 97. System.run_cons

Source: ControlStack/Core/Gate.lean:43 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem System.run_cons {St Op Eff : Type} (G : System St Op Eff) (s : St) (o : Op) (ops : List Op) : G.run s (o :: ops) = G.run (G.step s o) ops
~~~

### 98. Spec.trace_safe

Source: ControlStack/Core/Gate.lean:55 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem Spec.trace_safe {St Op Eff : Type} {G : System St Op Eff} (S : Spec G) (s : St) (ops : List Op) (h : S.Inv s) : S.Inv (G.run s ops) ∧ G.effects s <+: G.effects (G.run s ops) ∧ ∀ e ∈ G.effects (G.run s ops), S.ok (G.run s ops) e
~~~

### 99. NoAgentEffects.agent_trace_inert

Source: ControlStack/Core/Gate.lean:70 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem NoAgentEffects.agent_trace_inert {St Op Eff : Type} {G : System St Op Eff} {agent : Op → Prop} (H : NoAgentEffects G agent) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, agent o) : G.effects (G.run s ops) = G.effects s
~~~

### 100. halt_absorbing

Source: ControlStack/Core/Gate.lean:97 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem halt_absorbing {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List (HOp Op)) : (withHalt G).run (s, true) ops = (s, true)
~~~

### 101. halt_freezes

Source: ControlStack/Core/Gate.lean:104 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List (HOp Op)) : (withHalt G).effects ((withHalt G).run (s, false) (.halt :: ops)) = G.effects s
~~~

## ControlStack/Core/Leakage.lean

### 102. transfer

Source: ControlStack/Core/Leakage.lean:54 | Family: F2 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem transfer {X T A : Type} [Fintype X] [Fintype T] [Fintype A] (p : X → ℝ) (lik : X → T → ℝ) (c : T → ℝ) (δ : T → A → ℝ) (u : X → A → ℝ) (b : ℝ) (hp : ∀ x, 0 ≤ p x) (hc : ∀ x t, lik x t ≤ c t) (hc0 : ∀ t, 0 ≤ c t) (hδ : ∀ t, IsDist (δ t)) (hu : ∀ x a, 0 ≤ u x a) (hb : ∀ a, ∑ x, p x * u x a ≤ b) : ∑ x, p x * ∑ t, lik x t * ∑ a, δ t a * u x a ≤ (∑ t, c t) * b
~~~

### 103. covert_from_transfer

Source: ControlStack/Core/Leakage.lean:84 | Family: F2 | Adversary: NON_ADAPTIVE | Status: SOURCE_ONLY

~~~lean
theorem covert_from_transfer {M V : Type} [Fintype M] [Fintype V] [DecidableEq M] [Nonempty M] (enc : M → V → ℝ) (dec : V → M → ℝ) (henc : ∀ m, IsDist (enc m)) (hdec : ∀ v, IsDist (dec v)) : ∑ m, (Fintype.card M : ℝ)⁻¹ * ∑ v, enc m v * ∑ a, dec v a * (if a = m then 1 else 0) ≤ (Fintype.card V : ℝ) * (Fintype.card M : ℝ)⁻¹
~~~

### 104. cval_nonneg

Source: ControlStack/Core/Leakage.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_nonneg (c : List O → O → ℝ) (B : List O → ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hB : ∀ g, 0 ≤ B g) : ∀ n g, 0 ≤ cval c B n g
~~~

### 105. cval_mono

Source: ControlStack/Core/Leakage.lean:125 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_mono (c : List O → O → ℝ) (B B' : List O → ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hBB : ∀ g, B g ≤ B' g) : ∀ n g, cval c B n g ≤ cval c B' n g
~~~

### 106. cval_wsum

Source: ControlStack/Core/Leakage.lean:131 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_wsum {X : Type} [Fintype X] (c : List O → O → ℝ) (p : X → ℝ) (B : X → List O → ℝ) : ∀ n g, ∑ x, p x * cval c (B x) n g = cval c (fun t => ∑ x, p x * B x t) n g
~~~

### 107. cval_smul

Source: ControlStack/Core/Leakage.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_smul (c : List O → O → ℝ) (b : ℝ) (B : List O → ℝ) : ∀ n g, cval c (fun t => b * B t) n g = b * cval c B n g
~~~

### 108. val_le_cval

Source: ControlStack/Core/Leakage.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_le_cval (K : List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (pay : List O → ℝ) (hK0 : ∀ h z, 0 ≤ K h z) (hdom : Dominated K c) (hc0 : ∀ g o, 0 ≤ c g o) (hpay : ∀ g, 0 ≤ pay g) : ∀ n h, val K pay n h ≤ cval c pay n (h.map Prod.snd)
~~~

### 109. seq_transfer

Source: ControlStack/Core/Leakage.lean:178 | Family: F8 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem seq_transfer {X : Type} [Fintype X] (p : X → ℝ) (K : X → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (pay : X → List O → ℝ) (B : List O → ℝ) (n : ℕ) (hp : ∀ x, 0 ≤ p x) (hK0 : ∀ x h z, 0 ≤ K x h z) (hdom : ∀ x, Dominated (K x) c) (hc0 : ∀ g o, 0 ≤ c g o) (hpay : ∀ x g, 0 ≤ pay x g) (hB : ∀ t, ∑ x, p x * pay x t ≤ B t) : ∑ x, p x * val (K x) (pay x) n [] ≤ cval c B n []
~~~

### 110. seq_transfer_const

Source: ControlStack/Core/Leakage.lean:192 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seq_transfer_const {X : Type} [Fintype X] (p : X → ℝ) (K : X → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (pay : X → List O → ℝ) (b : ℝ) (n : ℕ) (hp : ∀ x, 0 ≤ p x) (hK0 : ∀ x h z, 0 ≤ K x h z) (hdom : ∀ x, Dominated (K x) c) (hc0 : ∀ g o, 0 ≤ c g o) (hpay : ∀ x g, 0 ≤ pay x g) (hb : ∀ t, ∑ x, p x * pay x t ≤ b) : ∑ x, p x * val (K x) (pay x) n [] ≤ b * mass c n []
~~~

### 111. mass_le_prod

Source: ControlStack/Core/Leakage.lean:204 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mass_le_prod (c : List O → O → ℝ) (Lr : ℕ → ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hLr0 : ∀ i, 0 ≤ Lr i) (hL : ∀ g, ∑ o, c g o ≤ Lr g.length) : ∀ n g, mass c n g ≤ ∏ j ∈ range n, Lr (g.length + j)
~~~

### 112. mass_le_pow

Source: ControlStack/Core/Leakage.lean:224 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mass_le_pow (c : List O → O → ℝ) (L : ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hL0 : 0 ≤ L) (hL : ∀ g, ∑ o, c g o ≤ L) (n : ℕ) (g : List O) : mass c n g ≤ L ^ n
~~~

### 113. mass_const

Source: ControlStack/Core/Leakage.lean:229 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mass_const (w : O → ℝ) : ∀ n g, mass (fun _ o => w o) n g = (∑ o, w o) ^ n
~~~

### 114. covert_seq

Source: ControlStack/Core/Leakage.lean:248 | Family: F2 | Adversary: SHARED_SEED | Status: SOURCE_ONLY

~~~lean
theorem covert_seq {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (dec : Ω → List O → M → ℝ) (n : ℕ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c) (hc0 : ∀ g o, 0 ≤ c g o) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ mass c n [] / (Fintype.card M : ℝ)
~~~

### 115. covert_seq_seed

Source: ControlStack/Core/Leakage.lean:270 | Family: F2 | Adversary: SHARED_SEED | Status: SOURCE_ONLY

~~~lean
theorem covert_seq_seed {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : Ω → List O → O → ℝ) (dec : Ω → List O → M → ℝ) (n : ℕ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) (c ω)) (hc0 : ∀ ω g o, 0 ≤ c ω g o) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ (∑ ω, ρ ω * mass (c ω) n []) / (Fintype.card M : ℝ)
~~~

### 116. episode_dom

Source: ControlStack/Core/Leakage.lean:293 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem episode_dom {V S Z : Type} [Fintype V] [Fintype S] [Fintype Z] (enc : List (S × (V × Z)) → V × S → ℝ) (W : List (S × (V × Z)) → S → Z → ℝ) (cs : List (V × Z) → Z → ℝ) (henc : ∀ h, IsDist (enc h)) (hcs0 : ∀ g z, 0 ≤ cs g z) (hW : ∀ h s z, W h s z ≤ cs (h.map Prod.snd) z) : Dominated (fun h (y : S × (V × Z)) => enc h (y.2.1, y.1) * W h y.1 y.2.2) (fun g o => cs g o.2)
~~~

### 117. episode_mass

Source: ControlStack/Core/Leakage.lean:314 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem episode_mass {V Z : Type} [Fintype V] [Fintype Z] (cs : List (V × Z) → Z → ℝ) (g : List (V × Z)) : ∑ o : V × Z, cs g o.2 = (Fintype.card V : ℝ) * ∑ z, cs g z
~~~

### 118. sc01_adaptive_target

Source: ControlStack/Core/Leakage.lean:322 | Family: F2 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem sc01_adaptive_target {Ω Y Z : Type} [Fintype Ω] [Fintype Y] [Fintype Z] (ρ : Ω → ℝ) (K : Ω → Fin (2 ^ 32) → List (Y × (Option (Fin 8) × Z)) → Y × (Option (Fin 8) × Z) → ℝ) (cs : List (Option (Fin 8) × Z) → Z → ℝ) (lam : ℕ → ℝ) (dec : Ω → List (Option (Fin 8) × Z) → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) (fun g o => cs g o.2)) (hcs0 : ∀ g z, 0 ≤ cs g z) (hlam : ∀ g, ∑ z, cs g z ≤ lam g.length) (hlam0 : ∀ i, 0 ≤ lam i) (hprod : ∏ i ∈ range 5, lam i ≤ 65536 / 59049) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card (Fin (2 ^ 32)) : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) 5 []) ≤ (2 : ℝ)⁻¹ ^ 16
~~~

### 119. covert_side_bound

Source: ControlStack/Core/Leakage.lean:348 | Family: F2 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem covert_side_bound {Ω M V Y Z : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype V] [Fintype Y] [Fintype Z] (ρ : Ω → ℝ) (K : Ω → M → List (Y × (V × Z)) → Y × (V × Z) → ℝ) (cs : List (V × Z) → Z → ℝ) (lam : ℕ → ℝ) (dec : Ω → List (V × Z) → M → ℝ) (n : ℕ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) (fun g o => cs g o.2)) (hcs0 : ∀ g z, 0 ≤ cs g z) (hlam : ∀ g, ∑ z, cs g z ≤ lam g.length) (hlam0 : ∀ i, 0 ≤ lam i) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ (Fintype.card V : ℝ) ^ n * (∏ i ∈ range n, lam i) / (Fintype.card M : ℝ)
~~~

### 120. cval_live

Source: ControlStack/Core/Leakage.lean:381 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_live (st : O → Bool) (c : List O → O → ℝ) : ∀ n g, cval c (liveInd st) n g = liveInd st g * mass (dropStop st c) n g
~~~

### 121. val_congr_on

Source: ControlStack/Core/Leakage.lean:432 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_congr_on {Y O : Type} [Fintype Y] [Fintype O] (K : List (Y × O) → Y × O → ℝ) (P : List O → Prop) (pay pay' : List O → ℝ) (hP : ∀ h y o, K h (y, o) ≠ 0 → P (h.map Prod.snd) → P (h.map Prod.snd ++ [o])) (hagree : ∀ t, P t → pay t = pay' t) : ∀ n h, P (h.map Prod.snd) → val K pay n h = val K pay' n h
~~~

### 122. consistent_append

Source: ControlStack/Core/Leakage.lean:449 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem consistent_append (S : Finset (Fin N)) (g : List (AOut Z)) (o : AOut Z) (hg : Consistent S g) (ho : o.2.2 = (o.1 && decide (memN S g.length))) : Consistent S (g ++ [o])
~~~

### 123. surv_live

Source: ControlStack/Core/Leakage.lean:462 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_live (k : ℕ) (S : Finset (Fin N)) (t : List (AOut Z)) (ht : Consistent S t) : survInd k S t = survInd k S t * liveInd caughtFlag t
~~~

### 124. blind_audit

Source: ControlStack/Core/Leakage.lean:491 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem blind_audit (k B : ℕ) (hB : B ≤ N) (t : List (AOut Z)) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * survInd k S t ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

### 125. liveInd_nonneg

Source: ControlStack/Core/Leakage.lean:511 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem liveInd_nonneg {O : Type} (st : O → Bool) (t : List O) : 0 ≤ liveInd st t
~~~

### 126. survInd_nonneg

Source: ControlStack/Core/Leakage.lean:515 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survInd_nonneg (k : ℕ) (S : Finset (Fin N)) (t : List (AOut Z)) : 0 ≤ survInd k S t
~~~

### 127. audit_leak_bound_all

Source: ControlStack/Core/Leakage.lean:525 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem audit_leak_bound_all (k B : ℕ) (hB : B ≤ N) (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (hK0 : ∀ S h z, 0 ≤ K S h z) (hK1 : ∀ S h, ∑ z, K S h z ≤ 1) (hcons : ∀ S h y o, K S h (y, o) ≠ 0 → o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length))) (hdom : ∀ S h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o) (hcl0 : ∀ g o, 0 ≤ cl g o) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (K S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * mass (dropStop caughtFlag cl) N []
~~~

### 128. audit_leak_bound

Source: ControlStack/Core/Leakage.lean:579 | Family: F6 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem audit_leak_bound (k B : ℕ) (hB : B ≤ N) (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1) (hcons : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h y o, K S h (y, o) ≠ 0 → o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length))) (hdom : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o) (hcl0 : ∀ g o, 0 ≤ cl g o) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (K S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * mass (dropStop caughtFlag cl) N []
~~~

### 129. audit_leak_prod

Source: ControlStack/Core/Leakage.lean:616 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem audit_leak_prod (k B : ℕ) (hB : B ≤ N) (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (Lr : ℕ → ℝ) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1) (hcons : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h y o, K S h (y, o) ≠ 0 → o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length))) (hdom : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o) (hcl0 : ∀ g o, 0 ≤ cl g o) (hLr0 : ∀ i, 0 ≤ Lr i) (hL : ∀ g, ∑ o, dropStop caughtFlag cl g o ≤ Lr g.length) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (K S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * ∏ i ∈ range N, Lr i
~~~

### 130. audit_adaptive_hidden

Source: ControlStack/Core/Leakage.lean:644 | Family: F6 | Adversary: ADAPTIVE_FEEDBACK | Status: SOURCE_ONLY

~~~lean
theorem audit_adaptive_hidden (k B : ℕ) (hB : B ≤ N) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) : ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (hiddenK σ S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

## ControlStack/CovertChannel.lean

### 131. per_seed_le

Source: ControlStack/CovertChannel.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem per_seed_le {M V : Type} [Fintype M] [Fintype V] (enc : M → V → ℝ) (dec : V → M → ℝ) (henc : ∀ m, IsDist (enc m)) (hdec : ∀ v, IsDist (dec v)) : ∑ m, ∑ v, enc m v * dec v m ≤ (Fintype.card V : ℝ)
~~~

### 132. covert_bound

Source: ControlStack/CovertChannel.lean:48 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem covert_bound {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V] [Nonempty M] (ρ : Ω → ℝ) (enc : Ω → M → V → ℝ) (dec : Ω → V → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (Fintype.card V : ℝ) / (Fintype.card M : ℝ)
~~~

### 133. covert_bound_schema

Source: ControlStack/CovertChannel.lean:63 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem covert_bound_schema {Ω M S : Type} [Fintype Ω] [Fintype M] [Fintype S] [Nonempty M] [DecidableEq S] (n : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → (Fin n → S) → ℝ) (dec : Ω → (Fin n → S) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (Fintype.card S : ℝ) ^ n / (Fintype.card M : ℝ)
~~~

### 134. attain_injective

Source: ControlStack/CovertChannel.lean:72 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attain_injective {M V : Type} [Fintype M] [Fintype V] [DecidableEq M] [DecidableEq V] [Nonempty M] (code : M → V) (decode : V → M) (hinv : ∀ m, decode (code m) = m) : successProb (Ω
~~~

### 135. design_point

Source: ControlStack/CovertChannel.lean:89 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem design_point {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → (Fin 16 → Bool) → ℝ) (dec : Ω → (Fin 16 → Bool) → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ 1 / 2 ^ 16
~~~

### 136. attain_embedding

Source: ControlStack/CovertChannel.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attain_embedding {M V : Type} [Fintype M] [Fintype V] [DecidableEq M] [DecidableEq V] [Nonempty M] [Nonempty V] (e : V → M) (he : Function.Injective e) : successProb (Ω
~~~

### 137. covert_bound_lifetime

Source: ControlStack/CovertChannel.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem covert_bound_lifetime {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] {E : ℕ} (V : Fin E → Type) [∀ e, Fintype (V e)] [∀ e, DecidableEq (V e)] (ρ : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ) (dec : Ω → ((e : Fin E) → V e) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (∏ e, (Fintype.card (V e) : ℝ)) / (Fintype.card M : ℝ)
~~~

## ControlStack/CovertNoGo.lean

### 138. controllable_leak

Source: ControlStack/CovertNoGo.lean:22 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem controllable_leak {M T V : Type} [Fintype M] [Fintype T] [DecidableEq M] [DecidableEq T] [DecidableEq V] (N : ℕ) (hN : 0 < N) (view : T → V) (realize : Fin N → T) (hdist : Function.Injective (fun i => view (realize i))) (e : Fin N → M) (he : Function.Injective e) : ∃ (enc : M → T → ℝ) (dec : V → M → ℝ), (∀ m, IsDist (enc m)) ∧ (∀ v, IsDist (dec v)) ∧ successView view enc dec = (N : ℝ) / (Fintype.card M : ℝ)
~~~

### 139. one_bit_coordinates

Source: ControlStack/CovertNoGo.lean:73 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem one_bit_coordinates {T V : Type} [Fintype T] [DecidableEq T] [DecidableEq V] (view : T → V) (t0 t1 : T) (h : view t0 ≠ view t1) : ∃ (enc : Bool → T → ℝ) (dec : V → Bool → ℝ), (∀ m, IsDist (enc m)) ∧ (∀ v, IsDist (dec v)) ∧ successView view enc dec = 1
~~~

## ControlStack/DeferGame.lean

### 140. deployV_step

Source: ControlStack/DeferGame.lean:58 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployV_step {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) : Pr[= true | deployV Bad π M D A Halt Svc b (n+1) u h] = ∑ x, Pr[= x | π h] * ∑ z, Pr[= z | M x] * (Pr[= true | D z] * Pr[= true | (if Bad x then pure true else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,true)]) : ProbComp Bool)] + Pr[= false | D z] * (if u < b then Pr[= true | (if Bad x then (fun caught => !caught) <$> A h x z else deployV Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)]) : ProbComp Bool)] else Pr[= true | (if Bad x then do let halt ← Halt h x z if halt then pure false else do let caught ← Svc h x z if caught then pure false else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) else do let halt ← Halt h x z if halt then pure false else deployV Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) : ProbComp Bool)]))
~~~

### 141. halt_then_prob

Source: ControlStack/DeferGame.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_then_prob (H K : ProbComp Bool) : Pr[= true | do let halt ← H; if halt then pure false else K] = Pr[= false | H] * Pr[= true | K]
~~~

### 142. halt_then_real

Source: ControlStack/DeferGame.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_then_real (H K : ProbComp Bool) : (Pr[= true | do let halt ← H; if halt then pure false else K]).toReal = (1 - (Pr[= true | H]).toReal) * (Pr[= true | K]).toReal
~~~

### 143. halt_service_continue_real

Source: ControlStack/DeferGame.lean:101 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_service_continue_real (H S C : ProbComp Bool) : (Pr[= true | do let halt ← H if halt then pure false else do let caught ← S if caught then pure false else C]).toReal = (1 - (Pr[= true | H]).toReal) * (1 - (Pr[= true | S]).toReal) * (Pr[= true | C]).toReal
~~~

### 144. calibrated_exhausted_benign_real

Source: ControlStack/DeferGame.lean:112 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem calibrated_exhausted_benign_real (H C : ProbComp Bool) (η : ℝ) (hH : (Pr[= true | H]).toReal = η) : (Pr[= true | do let halt ← H; if halt then pure false else C]).toReal = (1 - η) * (Pr[= true | C]).toReal
~~~

### 145. calibrated_exhausted_bad_real

Source: ControlStack/DeferGame.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem calibrated_exhausted_bad_real (H S C : ProbComp Bool) (η a c : ℝ) (hH : (Pr[= true | H]).toReal = η) (hS : (Pr[= true | S]).toReal = a) (hC : (Pr[= true | C]).toReal = c) : (Pr[= true | do let halt ← H if halt then pure false else do let caught ← S if caught then pure false else C]).toReal = (1 - η) * (1 - a) * c
~~~

### 146. calibrated_audit_escape_real

Source: ControlStack/DeferGame.lean:129 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem calibrated_audit_escape_real (A : ProbComp Bool) (r : ℝ) (hA : (Pr[= true | A]).toReal = r) : (Pr[= true | (fun caught => !caught) <$> A]).toReal = 1 - r
~~~

### 147. exhausted_benign_probability

Source: ControlStack/DeferGame.lean:159 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exhausted_benign_probability (H C : ProbComp Bool) : Pr[= true | do let halt ← H if halt then pure false else C] = Pr[= false | H] * Pr[= true | C]
~~~

### 148. exhausted_bad_then_probability

Source: ControlStack/DeferGame.lean:169 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exhausted_bad_then_probability (H S C : ProbComp Bool) : Pr[= true | do let halt ← H if halt then pure false else do let caught ← S if caught then pure false else C] = Pr[= false | H] * Pr[= false | S] * Pr[= true | C]
~~~

### 149. deployV_eq_catVE

Source: ControlStack/DeferGame.lean:200 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployV_eq_catVE {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) : ∀ n u h, Pr[= true | deployV Bad π M D A Halt Svc b n u h] = catVE Bad π M D A Halt Svc b n u h
~~~

### 150. catVE_ne_top

Source: ControlStack/DeferGame.lean:219 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_ne_top {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) : catVE Bad π M D A Halt Svc b n u h ≠ ⊤
~~~

### 151. catVE_transition_ne_top

Source: ControlStack/DeferGame.lean:229 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_transition_ne_top {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) (x : X) (z : Z) : (Pr[= true | D z] * (if Bad x then 1 else catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,true)])) + Pr[= false | D z] * (if u < b then (if Bad x then Pr[= false | A h x z] else catVE Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)])) else if Bad x then Pr[= false | Halt h x z] * Pr[= false | Svc h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) else Pr[= false | Halt h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]))) ≠ ⊤
~~~

### 152. catVE_inner_ne_top

Source: ControlStack/DeferGame.lean:274 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_inner_ne_top {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) (x : X) : (∑ z, Pr[= z | M x] * (Pr[= true | D z] * (if Bad x then 1 else catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,true)])) + Pr[= false | D z] * (if u < b then (if Bad x then Pr[= false | A h x z] else catVE Bad π M D A Halt Svc b n (u+1) (h ++ [(x,z,false)])) else if Bad x then Pr[= false | Halt h x z] * Pr[= false | Svc h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)]) else Pr[= false | Halt h x z] * catVE Bad π M D A Halt Svc b n u (h ++ [(x,z,false)])))) ≠ ⊤
~~~

### 153. catVE_toReal_eq_catV

Source: ControlStack/DeferGame.lean:296 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_toReal_eq_catV {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) (r η : ℝ) (a : Service X Z) (hA : ∀ h x z, Bad x → (Pr[= true | A h x z]).toReal = r) (hH : ∀ h x z, (Pr[= true | Halt h x z]).toReal = η) (hS : ∀ h x z, Bad x → (Pr[= true | Svc h x z]).toReal = a h x z) : ∀ n u h, (catVE Bad π M D A Halt Svc b n u h).toReal = catV Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D z]).toReal) (fun h x => (Pr[= x | π h]).toReal) r η a b n u h
~~~

### 154. defer_bridge

Source: ControlStack/DeferGame.lean:330 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem defer_bridge : DeferBridgeClaim
~~~

## ControlStack/DeferMono.lean

### 155. catVE_toReal_le_catV

Source: ControlStack/DeferMono.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catVE_toReal_le_catV {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (Halt : Hist X Z → X → Z → ProbComp Bool) (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) (r η : ℝ) (a : Service X Z) (hA : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) (hH : ∀ h x z, η ≤ (Pr[= true | Halt h x z]).toReal) (hS : ∀ h x z, Bad x → a h x z ≤ (Pr[= true | Svc h x z]).toReal) : ∀ n u h, (catVE Bad π M D A Halt Svc b n u h).toReal ≤ catV Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D z]).toReal) (fun h x => (Pr[= x | π h]).toReal) r η a b n u h
~~~

### 156. defer_mono

Source: ControlStack/DeferMono.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem defer_mono : DeferMonoClaim
~~~

## ControlStack/EgressGate.lean

### 157. lookup_pinned

Source: ControlStack/EgressGate.lean:26 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lookup_pinned (p : Policy) (key : String) (peer : Peer) (h : lookup p key = some peer) : peer ∈ p.map Rule.peer
~~~

### 158. direct_no_effect

Source: ControlStack/EgressGate.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem direct_no_effect (p : Policy) (s : State) (peer : Peer) (h : Invariant p s) : step p s (.directAttempt peer) = s
~~~

### 159. step_safe

Source: ControlStack/EgressGate.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_safe (p : Policy) (s : State) (a : Action) (h : Invariant p s) : Invariant p (step p s a)
~~~

### 160. trace_safe

Source: ControlStack/EgressGate.lean:126 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem trace_safe (p : Policy) (s : State) (actions : List Action) (h : Invariant p s) : Invariant p (run p s actions)
~~~

### 161. failed_launch

Source: ControlStack/EgressGate.lean:132 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem failed_launch (p : Policy) (s : State) (t : Topology) (h : safe t = false) : (step p s (.launch t)).active = false
~~~

### 162. crash_closed

Source: ControlStack/EgressGate.lean:135 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem crash_closed (p : Policy) (s : State) (key : String) : (step p (step p s .crashGateway) (.request key)).attempts = s.attempts
~~~

## ControlStack/Families/F2/ChannelInstances.lean

### 163. covert_rounds

Source: ControlStack/Families/F2/ChannelInstances.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem covert_rounds (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (Lr : ℕ → ℝ) (dec : Ω → List O → M → ℝ) (n : ℕ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c) (hc0 : ∀ g o, 0 ≤ c g o) (hLr0 : ∀ i, 0 ≤ Lr i) (hL : ∀ g, ∑ o, c g o ≤ Lr g.length) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ (∏ i ∈ range n, Lr i) / (Fintype.card M : ℝ)
~~~

### 164. covert_alphabet

Source: ControlStack/Families/F2/ChannelInstances.lean:79 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem covert_alphabet (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (dec : Ω → List O → M → ℝ) (n : ℕ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hK1 : ∀ ω m h, ∑ z, K ω m h z ≤ 1) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ (Fintype.card O : ℝ) ^ n / (Fintype.card M : ℝ)
~~~

### 165. sc02_accumulated

Source: ControlStack/Families/F2/ChannelInstances.lean:105 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem sc02_accumulated (k E : ℕ) (ρ : Ω → ℝ) (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (L : ℕ → ℝ) (dec : Ω → List O → Fin (2 ^ k) → ℝ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c) (hc0 : ∀ g o, 0 ≤ c g o) (hL0 : ∀ i, 0 ≤ L i) (hL : ∀ g, ∑ o, c g o ≤ L g.length) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * (((2 : ℝ) ^ k)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) E []) ≤ (∏ e ∈ range E, L e) / 2 ^ k
~~~

### 166. prod_epoch

Source: ControlStack/Families/F2/ChannelInstances.lean:116 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prod_epoch (n a E : ℕ) (L : ℝ) (h : a + E ≤ n) : ∏ i ∈ range n, (if a ≤ i ∧ i < a + E then L else 1) = L ^ E
~~~

### 167. rekey_epoch

Source: ControlStack/Families/F2/ChannelInstances.lean:130 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rekey_epoch {M : Type} [Fintype M] [Nonempty M] (n a E : ℕ) (hE : a + E ≤ n) (L : ℝ) (hL0 : 0 ≤ L) (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (dec : Ω → List O → M → ℝ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c) (hc0 : ∀ g o, 0 ≤ c g o) (hin : ∀ g, a ≤ g.length ∧ g.length < a + E → ∑ o, c g o ≤ L) (hout : ∀ g, ¬(a ≤ g.length ∧ g.length < a + E) → ∑ o, c g o ≤ 1) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []) ≤ L ^ E / (Fintype.card M : ℝ)
~~~

### 168. sc02_example

Source: ControlStack/Families/F2/ChannelInstances.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc02_example : ((21 : ℝ) / 20) ^ 20 / 2 ^ 16 ≤ 1 / 20000
~~~

### 169. sc02_no_rekey

Source: ControlStack/Families/F2/ChannelInstances.lean:153 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc02_no_rekey : (1 : ℝ) / 4 ≤ ((21 : ℝ) / 20) ^ 200 / 2 ^ 16
~~~

### 170. canonical_seq

Source: ControlStack/Families/F2/ChannelInstances.lean:162 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem canonical_seq {Ω M Y : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] (Kc m : ℕ) (ρ : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ) (dec : Ω → List (Fin Kc) → M → ℝ) (hρ : IsDist ρ) (hK0 : ∀ ω x h z, 0 ≤ K ω x h z) (hK1 : ∀ ω x h, ∑ z, K ω x h z ≤ 1) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ x, val (K ω x) (fun t => dec ω t x) m []) ≤ (Kc : ℝ) ^ m / (Fintype.card M : ℝ)
~~~

### 171. log_channel

Source: ControlStack/Families/F2/ChannelInstances.lean:176 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem log_channel {Ω M Y : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] (Kt f Q m : ℕ) (ρ : Ω → ℝ) (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) → Y × (Fin Kt × (Fin f → Fin Q)) → ℝ) (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ) (hρ : IsDist ρ) (hK0 : ∀ ω x h z, 0 ≤ K ω x h z) (hK1 : ∀ ω x h, ∑ z, K ω x h z ≤ 1) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ x, val (K ω x) (fun t => dec ω t x) m []) ≤ (Kt : ℝ) ^ m * (Q : ℝ) ^ (f * m) / (Fintype.card M : ℝ)
~~~

### 172. log_example

Source: ControlStack/Families/F2/ChannelInstances.lean:188 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem log_example : ((8 : ℝ) ^ 4 * (4 : ℝ) ^ (2 * 4)) / 2 ^ 64 = 1 / 2 ^ 36
~~~

### 173. free_text_leaks

Source: ControlStack/Families/F2/ChannelInstances.lean:192 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem free_text_leaks (n : ℕ) : successProb (Ω
~~~

### 174. gpu_bound

Source: ControlStack/Families/F2/ChannelInstances.lean:216 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gpu_bound {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] (m : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → List (Bool × Fin J) → Bool → ℝ) (W : Bool → Fin J → ℝ) (dec : Ω → List (Fin J) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω x h, IsDist (enc ω x h)) (hW : ∀ s o, 0 ≤ W s o) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ x, val (gpuK enc W ω x) (fun t => dec ω t x) m []) ≤ (∑ o, wmax W o) ^ m / (Fintype.card M : ℝ)
~~~

### 175. gpu_partition

Source: ControlStack/Families/F2/ChannelInstances.lean:241 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gpu_partition (W : Bool → Fin J → ℝ) (hW : IsDist (W false)) (hsame : ∀ o, W true o = W false o) : ∑ o, wmax W o = 1
~~~

### 176. gpu_jitter

Source: ControlStack/Families/F2/ChannelInstances.lean:248 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gpu_jitter (W : Bool → Fin J → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hW : IsDist (W false)) (hratio : ∀ o, W true o ≤ (1 + δ) * W false o) : ∑ o, wmax W o ≤ 1 + δ
~~~

### 177. gpuW_mass

Source: ControlStack/Families/F2/ChannelInstances.lean:261 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gpuW_mass : ∑ o, wmax gpuW o = 14 / 10
~~~

### 178. gpu_example

Source: ControlStack/Families/F2/ChannelInstances.lean:266 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gpu_example {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 16) → List (Bool × Fin 4) → Bool → ℝ) (dec : Ω → List (Fin 4) → Fin (2 ^ 16) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω x h, IsDist (enc ω x h)) (hdec : ∀ ω t, IsDist (dec ω t)) : ∑ ω, ρ ω * ((Fintype.card (Fin (2 ^ 16)) : ℝ)⁻¹ * ∑ x, val (gpuK enc gpuW ω x) (fun t => dec ω t x) 10 []) ≤ 1 / 2000
~~~

### 179. gpu_jitter_example

Source: ControlStack/Families/F2/ChannelInstances.lean:284 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gpu_jitter_example : ∑ o, wmax gpuWj o = 102 / 100 ∧ ∑ o, wmax gpuWj o ≤ 1 + 1 / 12
~~~

## ControlStack/Families/F3/DistributedHalt.lean

### 180. sum_window

Source: ControlStack/Families/F3/DistributedHalt.lean:57 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_window (T ρ lo hi : ℕ) (e : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P] (he : ∀ t, e t ≤ ρ) (hz : ∀ t, P t → e t ≠ 0 → lo ≤ t ∧ t < hi) : ∑ t ∈ range T, (if P t then e t else 0) ≤ ρ * (hi - lo)
~~~

### 181. initiated_after_le

Source: ControlStack/Families/F3/DistributedHalt.lean:104 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem initiated_after_le (n T t0 ρ Δ : ℕ) (e : ℕ → ℕ → ℕ) (δ : ℕ → ℕ) (hr : Rate ρ e) (hh : HaltAbsorbs t0 δ e) (hd : Delivered n Δ δ) : initiatedAfter n T t0 e ≤ ∑ i ∈ range n, ρ * δ i ∧ initiatedAfter n T t0 e ≤ n * ρ * Δ
~~~

### 182. landed_after_le

Source: ControlStack/Families/F3/DistributedHalt.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem landed_after_le (n T t0 ρ Δ L : ℕ) (e lat : ℕ → ℕ → ℕ) (δ : ℕ → ℕ) (hr : Rate ρ e) (hh : HaltAbsorbs t0 δ e) (hd : Delivered n Δ δ) (hl : Latency L lat) : landedAfter n T t0 e lat ≤ n * ρ * (L + Δ)
~~~

### 183. foldl_sublist

Source: ControlStack/Families/F3/DistributedHalt.lean:143 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_sublist (fence : Bool) (t0 ε e0 G : ℕ) : ∀ (evs : List (ℕ × ℕ)) (s : List (ℕ × ℕ)), ∃ l, evs.foldl (sinkStep fence t0 ε e0 G) s = s ++ l ∧ l.Sublist (evs.filter (accepts fence t0 ε e0))
~~~

### 184. foldl_len

Source: ControlStack/Families/F3/DistributedHalt.lean:166 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_len (fence : Bool) (t0 ε e0 G : ℕ) : ∀ (evs : List (ℕ × ℕ)) (s : List (ℕ × ℕ)), s.length ≤ G → (evs.foldl (sinkStep fence t0 ε e0 G) s).length ≤ G
~~~

### 185. sink_sublist

Source: ControlStack/Families/F3/DistributedHalt.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sink_sublist (fence : Bool) (t0 ε e0 G : ℕ) (evs : List (ℕ × ℕ)) : (sinkRun fence t0 ε e0 G evs).Sublist (evs.filter (accepts fence t0 ε e0))
~~~

### 186. sink_budget

Source: ControlStack/Families/F3/DistributedHalt.lean:189 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sink_budget (fence : Bool) (t0 ε e0 G : ℕ) (evs : List (ℕ × ℕ)) : (sinkRun fence t0 ε e0 G evs).length ≤ G
~~~

### 187. sink_count

Source: ControlStack/Families/F3/DistributedHalt.lean:193 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sink_count (fence : Bool) (t0 ε e0 G : ℕ) (evs : List (ℕ × ℕ)) (q : ℕ × ℕ → Bool) : (sinkRun fence t0 ε e0 G evs).countP q ≤ evs.countP (fun ev => q ev && accepts fence t0 ε e0 ev)
~~~

### 188. fenced_after_eps

Source: ControlStack/Families/F3/DistributedHalt.lean:201 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fenced_after_eps (t0 ε e0 G : ℕ) (evs : List (ℕ × ℕ)) (hold : ∀ ev ∈ evs, ev.2 ≤ e0) : (sinkRun true t0 ε e0 G evs).countP (fun ev => decide (t0 + ε ≤ ev.1)) = 0
~~~

### 189. listsum_range

Source: ControlStack/Families/F3/DistributedHalt.lean:219 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem listsum_range (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i
~~~

### 190. stream_countP

Source: ControlStack/Families/F3/DistributedHalt.lean:224 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stream_countP (n T : ℕ) (e lat ep : ℕ → ℕ → ℕ) (q : ℕ × ℕ → Bool) : (stream n T e lat ep).countP q = ∑ i ∈ range n, ∑ t ∈ range T, (if q (t + lat i t, ep i t) = true then e i t else 0)
~~~

### 191. stream_epochs

Source: ControlStack/Families/F3/DistributedHalt.lean:239 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stream_epochs (n T : ℕ) (e lat ep : ℕ → ℕ → ℕ) (e0 : ℕ) (hold : HoldsOld e0 ep) : ∀ ev ∈ stream n T e lat ep, ev.2 ≤ e0
~~~

### 192. fenced_window

Source: ControlStack/Families/F3/DistributedHalt.lean:248 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fenced_window (n T t0 ε e0 G ρ L : ℕ) (e lat ep : ℕ → ℕ → ℕ) (hr : Rate ρ e) (hl : Latency L lat) (hold : HoldsOld e0 ep) : (sinkRun true t0 ε e0 G (stream n T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) ≤ n * ρ * (L + ε)
~~~

### 193. unfenced_composed

Source: ControlStack/Families/F3/DistributedHalt.lean:270 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unfenced_composed (n T t0 ε e0 G ρ Δ L : ℕ) (e lat ep : ℕ → ℕ → ℕ) (δ : ℕ → ℕ) (hr : Rate ρ e) (hh : HaltAbsorbs t0 δ e) (hd : Delivered n Δ δ) (hl : Latency L lat) : (sinkRun false t0 ε e0 G (stream n T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) ≤ min G (n * ρ * (L + Δ))
~~~

### 194. fenced_composed

Source: ControlStack/Families/F3/DistributedHalt.lean:285 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fenced_composed (n T t0 ε e0 G ρ L : ℕ) (e lat ep : ℕ → ℕ → ℕ) (hr : Rate ρ e) (hl : Latency L lat) (hold : HoldsOld e0 ep) : (sinkRun true t0 ε e0 G (stream n T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) ≤ min G (n * ρ * (L + ε)) ∧ (sinkRun true t0 ε e0 G (stream n T e lat ep)).countP (fun ev => decide (t0 + ε ≤ ev.1)) = 0
~~~

### 195. foldl_all

Source: ControlStack/Families/F3/DistributedHalt.lean:295 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_all (fence : Bool) (t0 ε e0 G : ℕ) : ∀ (evs s : List (ℕ × ℕ)), (∀ ev ∈ evs, accepts fence t0 ε e0 ev = true) → s.length + evs.length ≤ G → evs.foldl (sinkStep fence t0 ε e0 G) s = s ++ evs
~~~

### 196. partition_count

Source: ControlStack/Families/F3/DistributedHalt.lean:315 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem partition_count (T t0 : ℕ) : ∑ i ∈ range 1, ∑ t ∈ range T, (if t0 ≤ t + 0 then partitionE i t else 0) = T - t0
~~~

### 197. stream_length

Source: ControlStack/Families/F3/DistributedHalt.lean:322 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stream_length (n T : ℕ) (e lat ep : ℕ → ℕ → ℕ) : (stream n T e lat ep).length = ∑ i ∈ range n, ∑ t ∈ range T, e i t
~~~

### 198. partition_unbounded

Source: ControlStack/Families/F3/DistributedHalt.lean:329 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem partition_unbounded (t0 ε e0 M : ℕ) : ∃ T, M < (sinkRun false t0 ε e0 (T + 1) (stream 1 T partitionE (fun _ _ => 0) (fun _ _ => e0))).countP (fun ev => decide (t0 ≤ ev.1))
~~~

### 199. partition_fenced

Source: ControlStack/Families/F3/DistributedHalt.lean:346 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem partition_fenced (t0 ε e0 G T : ℕ) : (sinkRun true t0 ε e0 G (stream 1 T partitionE (fun _ _ => 0) (fun _ _ => e0))).countP (fun ev => decide (t0 ≤ ev.1)) ≤ ε
~~~

### 200. token_leak

Source: ControlStack/Families/F3/DistributedHalt.lean:355 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem token_leak (t0 ε e0 : ℕ) : (sinkRun true t0 ε e0 1 [(t0 + ε, e0 + 1)]).countP (fun ev => decide (t0 + ε ≤ ev.1)) = 1
~~~

### 201. example_unfenced

Source: ControlStack/Families/F3/DistributedHalt.lean:362 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem example_unfenced (T t0 ε e0 G : ℕ) (e lat ep : ℕ → ℕ → ℕ) (δ : ℕ → ℕ) (hr : Rate 10 e) (hh : HaltAbsorbs t0 δ e) (hd : Delivered 1000 5 δ) (hl : Latency 0 lat) : (sinkRun false t0 ε e0 G (stream 1000 T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) ≤ 50000
~~~

### 202. example_fenced

Source: ControlStack/Families/F3/DistributedHalt.lean:368 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem example_fenced (T t0 e0 G : ℕ) (e lat ep : ℕ → ℕ → ℕ) (hr : Rate 10 e) (hl : Latency 0 lat) (hold : HoldsOld e0 ep) : (sinkRun true t0 1 e0 G (stream 1000 T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) ≤ 10000 ∧ (sinkRun true t0 1 e0 G (stream 1000 T e lat ep)).countP (fun ev => decide (t0 + 1 ≤ ev.1)) = 0
~~~

## ControlStack/Families/F4/GateClients.lean

### 203. dispatch_effects_prefix

Source: ControlStack/Families/F4/GateClients.lean:44 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dispatch_effects_prefix (s : AuditDispatch.St) (o : AuditDispatch.Op) : s.effects <+: (AuditDispatch.step s o).effects
~~~

### 204. dispatch_no_agent_effects

Source: ControlStack/Families/F4/GateClients.lean:55 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dispatch_no_agent_effects : NoAgentEffects dispatchSys (fun o => ∀ id, o ≠ .dispatch id)
~~~

### 205. auditGate_prefix

Source: ControlStack/Families/F4/GateClients.lean:65 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem auditGate_prefix (s : AuditGate.St) (o : AuditGate.Op) : s.executions <+: (AuditGate.step s o).executions
~~~

### 206. egress_prefix

Source: ControlStack/Families/F4/GateClients.lean:82 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem egress_prefix (p : EgressGate.Policy) (s : EgressGate.State) (a : EgressGate.Action) : s.attempts <+: (EgressGate.step p s a).attempts
~~~

### 207. step_inv

Source: ControlStack/Families/F4/GateClients.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (hash : C → H) (s : St C H) (o : Op C H) (h : Inv hash s) : Inv hash (step hash s o)
~~~

### 208. prefix_step

Source: ControlStack/Families/F4/GateClients.lean:169 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prefix_step (hash : C → H) (s : St C H) (o : Op C H) : s.deployed <+: (step hash s o).deployed
~~~

### 209. deployed_reviewed

Source: ControlStack/Families/F4/GateClients.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployed_reviewed (hash : C → H) (ops : List (Op C H)) : ∀ c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).deployed, hash c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).reviewed
~~~

### 210. deployed_is_reviewed

Source: ControlStack/Families/F4/GateClients.lean:195 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem deployed_is_reviewed (hash : C → H) (ops : List (Op C H)) (hinj : Set.InjOn hash {c | c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).store ∨ c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).reviewedContent}) : ∀ c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).deployed, c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).reviewedContent
~~~

### 211. collision_breaks

Source: ControlStack/Families/F4/GateClients.lean:210 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem collision_breaks : let s
~~~

### 212. agent_cannot_review

Source: ControlStack/Families/F4/GateClients.lean:222 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_cannot_review (hash : C → H) (s : St C H) (o : Op C H) (ho : agentOp o) : (step hash s o).reviewed = s.reviewed ∧ (step hash s o).reviewedContent = s.reviewedContent
~~~

### 213. step_inv

Source: ControlStack/Families/F4/GateClients.lean:273 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (s : St P) (o : Op P) (h : Inv s) : Inv (step s o)
~~~

### 214. prefix_step

Source: ControlStack/Families/F4/GateClients.lean:292 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prefix_step (s : St P) (o : Op P) : s.executed <+: (step s o).executed
~~~

### 215. approval_safe

Source: ControlStack/Families/F4/GateClients.lean:307 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem approval_safe (ops : List (Op P)) : let s
~~~

### 216. replay_without_nonce

Source: ControlStack/Families/F4/GateClients.lean:322 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem replay_without_nonce : let t : Tx Unit
~~~

### 217. agent_cannot_approve

Source: ControlStack/Families/F4/GateClients.lean:334 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_cannot_approve (s : St P) (o : Op P) (ho : agentOp o) : (step s o).approvals = s.approvals
~~~

### 218. replay_if_nonces_lost

Source: ControlStack/Families/F4/GateClients.lean:341 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem replay_if_nonces_lost : let t : Tx Unit
~~~

## ControlStack/Families/F5/Lease.lean

### 219. spent_append

Source: ControlStack/Families/F5/Lease.lean:107 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem spent_append (work : List (ℕ × ℕ × ℕ)) (e : ℕ × ℕ × ℕ) (id : ℕ) : spent (work ++ [e]) id = spent work id + (if e.1 = id then e.2.1 else 0)
~~~

### 220. total_append

Source: ControlStack/Families/F5/Lease.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem total_append (work : List (ℕ × ℕ × ℕ)) (e : ℕ × ℕ × ℕ) : total (work ++ [e]) = total work + e.2.1
~~~

### 221. spent_eq_zero_of_absent

Source: ControlStack/Families/F5/Lease.lean:114 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem spent_eq_zero_of_absent (work : List (ℕ × ℕ × ℕ)) (id : ℕ) (h : ∀ e ∈ work, e.1 ≠ id) : spent work id = 0
~~~

### 222. step_inv

Source: ControlStack/Families/F5/Lease.lean:120 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (cap : ℕ) (s : St) (o : Op) (h : Inv cap s) : Inv cap (step cap s o)
~~~

### 223. prefix_step

Source: ControlStack/Families/F5/Lease.lean:180 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prefix_step (cap : ℕ) (s : St) (o : Op) : s.work <+: (step cap s o).work
~~~

### 224. lease_safe

Source: ControlStack/Families/F5/Lease.lean:204 | Family: F5 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem lease_safe (cap : ℕ) (ops : List Op) : let s
~~~

### 225. revoke_step

Source: ControlStack/Families/F5/Lease.lean:213 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem revoke_step (cap : ℕ) (s : St) (o : Op) (id : ℕ) (hr : id ∈ s.revoked) : id ∈ (step cap s o).revoked ∧ ∃ δ, (step cap s o).work = s.work ++ δ ∧ ∀ e ∈ δ, e.1 ≠ id
~~~

### 226. revoke_absorbing

Source: ControlStack/Families/F5/Lease.lean:238 | Family: F5 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem revoke_absorbing (cap : ℕ) (s : St) (ops : List Op) (id : ℕ) (hr : id ∈ s.revoked) : ∃ δ, ((sys cap).run s ops).work = s.work ++ δ ∧ ∀ e ∈ δ, e.1 ≠ id
~~~

### 227. length_le_sum

Source: ControlStack/Families/F5/Lease.lean:252 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem length_le_sum (L : List (ℕ × ℕ × ℕ)) (h : ∀ e ∈ L, 1 ≤ e.2.1) : L.length ≤ (L.map (fun e => e.2.1)).sum
~~~

### 228. work_count_le

Source: ControlStack/Families/F5/Lease.lean:264 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem work_count_le (cap : ℕ) (ops : List Op) : let s
~~~

### 229. agent_cannot_issue

Source: ControlStack/Families/F5/Lease.lean:282 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_cannot_issue (cap : ℕ) (s : St) (o : Op) (ho : agentOp o) : (step cap s o).leases = s.leases ∧ (step cap s o).revoked = s.revoked
~~~

### 230. revoked_worker_stays_stopped

Source: ControlStack/Families/F5/Lease.lean:298 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem revoked_worker_stays_stopped : let ops
~~~

### 231. zero_cost_refused

Source: ControlStack/Families/F5/Lease.lean:304 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem zero_cost_refused : ([Op.issue ⟨0, 0, 100⟩ 1, .work 1 0, .work 1 0].foldl (step 100) init).work = []
~~~

### 232. fork_without_lease_accounting

Source: ControlStack/Families/F5/Lease.lean:328 | Family: F5 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem fork_without_lease_accounting : let ops
~~~

### 233. reissue_takes_effect

Source: ControlStack/Families/F5/Lease.lean:335 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reissue_takes_effect : let ops
~~~

## ControlStack/Families/F6/DamageBound.lean

### 234. val_le_const

Source: ControlStack/Families/F6/DamageBound.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_le_const (K : List (Y × O) → Y × O → ℝ) (pay : List O → ℝ) (M : ℝ) (hK0 : ∀ h z, 0 ≤ K h z) (hK1 : ∀ h, ∑ z, K h z ≤ 1) (hM : 0 ≤ M) (hpay : ∀ t, pay t ≤ M) : ∀ n h, val K pay n h ≤ M
~~~

### 235. val_mono_on

Source: ControlStack/Families/F6/DamageBound.lean:84 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_mono_on (K : List (Y × O) → Y × O → ℝ) (P : List O → Prop) (pay pay' : List O → ℝ) (hK0 : ∀ h z, 0 ≤ K h z) (hP : ∀ h y o, K h (y, o) ≠ 0 → P (h.map Prod.snd) → P (h.map Prod.snd ++ [o])) (hle : ∀ t, P t → pay t ≤ pay' t) : ∀ n h, P (h.map Prod.snd) → val K pay n h ≤ val K pay' n h
~~~

### 236. val_smul

Source: ControlStack/Families/F6/DamageBound.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_smul (K : List (Y × O) → Y × O → ℝ) (c : ℝ) (pay : List O → ℝ) : ∀ n h, val K (fun t => c * pay t) n h = c * val K pay n h
~~~

### 237. val_add

Source: ControlStack/Families/F6/DamageBound.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_add (K : List (Y × O) → Y × O → ℝ) (p q : List O → ℝ) : ∀ n h, val K (fun t => p t + q t) n h = val K p n h + val K q n h
~~~

### 238. val_finsum

Source: ControlStack/Families/F6/DamageBound.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_finsum {ι : Type} (s : Finset ι) (K : List (Y × O) → Y × O → ℝ) (f : ι → List O → ℝ) : ∀ n h, val K (fun t => ∑ j ∈ s, f j t) n h = ∑ j ∈ s, val K (f j) n h
~~~

### 239. val_det

Source: ControlStack/Families/F6/DamageBound.lean:131 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_det [DecidableEq Y] [DecidableEq O] (z0 : Y × O) (pay : List O → ℝ) : ∀ n h, val (fun _ z => if z = z0 then (1 : ℝ) else 0) pay n h = pay (h.map Prod.snd ++ List.replicate n z0.2)
~~~

### 240. pre_all

Source: ControlStack/Families/F6/DamageBound.lean:161 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pre_all (g : List (AOut Unit)) (hg : (g.all fun o => !caughtFlag o) = true) : pre g = g
~~~

### 241. pre_snoc

Source: ControlStack/Families/F6/DamageBound.lean:170 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pre_snoc (g : List (AOut Unit)) (o : AOut Unit) : pre (g ++ [o]) = if (g.all fun o => !caughtFlag o) = true then (if caughtFlag o = true then g else g ++ [o]) else pre g
~~~

### 242. attacked_snoc

Source: ControlStack/Families/F6/DamageBound.lean:186 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attacked_snoc (g : List (AOut Unit)) (o : AOut Unit) (i : ℕ) (h : attacked g i = true) : attacked (g ++ [o]) i = true
~~~

### 243. attackSet_snoc

Source: ControlStack/Families/F6/DamageBound.lean:196 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attackSet_snoc {N : ℕ} (g : List (AOut Unit)) (o : AOut Unit) : attackSet (N
~~~

### 244. ucX_mono

Source: ControlStack/Families/F6/DamageBound.lean:202 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ucX_mono (N : ℕ) (g : List (AOut Unit)) (o : AOut Unit) : ucX N g ≤ ucX N (g ++ [o])
~~~

### 245. ucX_stuck

Source: ControlStack/Families/F6/DamageBound.lean:210 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ucX_stuck (N : ℕ) (g : List (AOut Unit)) (o : AOut Unit) (h : (g.all fun o => !caughtFlag o) = false ∨ caughtFlag o = true) : ucX N (g ++ [o]) = ucX N g
~~~

### 246. ucX_le

Source: ControlStack/Families/F6/DamageBound.lean:220 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ucX_le (N : ℕ) (t : List (AOut Unit)) : ucX N t ≤ N
~~~

### 247. ucX_tail

Source: ControlStack/Families/F6/DamageBound.lean:225 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ucX_tail (N : ℕ) (t : List (AOut Unit)) : (ucX N t : ℝ) = ∑ j ∈ range N, (if j + 1 ≤ ucX N t then (1 : ℝ) else 0)
~~~

### 248. sum_point

Source: ControlStack/Families/F6/DamageBound.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_point (z0 : Y × AOut Unit) (F : Y × AOut Unit → ℝ) : ∑ y, ∑ o, (if (y, o) = z0 then (1 : ℝ) else 0) * F (y, o) = F z0
~~~

### 249. val_frozen

Source: ControlStack/Families/F6/DamageBound.lean:257 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem val_frozen (j : ℕ) (y0 : Y) (Kx : List (Y × AOut Unit) → Y × AOut Unit → ℝ) : ∀ n h, j ≤ ucX N (h.map Prod.snd) → val (freezeK N j y0 Kx) (pX N j) n h = 1
~~~

### 250. freeze_le

Source: ControlStack/Families/F6/DamageBound.lean:273 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem freeze_le (j : ℕ) (y0 : Y) (Kx : List (Y × AOut Unit) → Y × AOut Unit → ℝ) (hK0 : ∀ h z, 0 ≤ Kx h z) (hK1 : ∀ h, ∑ z, Kx h z ≤ 1) : ∀ n h, val Kx (pX N j) n h ≤ val (freezeK N j y0 Kx) (pX N j) n h
~~~

### 251. pX_le_succ

Source: ControlStack/Families/F6/DamageBound.lean:291 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pX_le_succ (j : ℕ) (y0 : Y) (Kx : List (Y × AOut Unit) → Y × AOut Unit → ℝ) (hK0 : ∀ h z, 0 ≤ Kx h z) (n : ℕ) : val (freezeK N j y0 Kx) (pX N j) n [] ≤ val (freezeK N j y0 Kx) (recallSucc (N
~~~

### 252. tail_bound

Source: ControlStack/Families/F6/DamageBound.lean:328 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tail_bound (y0 : Y) (j Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) (pX N j) N [] ≤ hypMiss N Bh j r
~~~

### 253. expected_uc

Source: ControlStack/Families/F6/DamageBound.lean:373 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem expected_uc (y0 : Y) (Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) (fun t => (ucX N t : ℝ)) N [] ≤ ∑ j ∈ range N, hypMiss N Bh (j + 1) r
~~~

### 254. damage_bound

Source: ControlStack/Families/F6/DamageBound.lean:394 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem damage_bound (y0 : Y) (Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) (D : ℝ) (hD : 0 ≤ D) (dmg : List (AOut Unit) → ℝ) (hdD : ∀ t, dmg t ≤ D * ucX N t) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) dmg N [] ≤ D * ∑ j ∈ range N, hypMiss N Bh (j + 1) r
~~~

### 255. damage_cap_inflight

Source: ControlStack/Families/F6/DamageBound.lean:423 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem damage_cap_inflight (y0 : Y) (Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) (D F G : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (hG : 0 ≤ G) (dmg : List (AOut Unit) → ℝ) (hdD : ∀ t, dmg t ≤ D * ucX N t + F) (hdG : ∀ t, dmg t ≤ G) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) dmg N [] ≤ min G (D * ∑ j ∈ range N, hypMiss N Bh (j + 1) r + F)
~~~

### 256. hypMiss_one

Source: ControlStack/Families/F6/DamageBound.lean:473 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hypMiss_one (B k : ℕ) : hypMiss N B k 1 = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

### 257. sum_range_choose_succ

Source: ControlStack/Families/F6/DamageBound.lean:481 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_range_choose_succ (B : ℕ) : ∀ n, ∑ m ∈ range n, Nat.choose m B = Nat.choose n (B + 1)
~~~

### 258. expected_r1

Source: ControlStack/Families/F6/DamageBound.lean:487 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem expected_r1 (B : ℕ) (hB : B ≤ N) : ∑ j ∈ range N, hypMiss N B (j + 1) 1 = ((N : ℝ) - B) / (B + 1)
~~~

### 259. sum_pU_eq

Source: ControlStack/Families/F6/DamageBound.lean:507 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_pU_eq (B : ℕ) (X : Finset (Fin N) → ℝ) : ∑ S : Finset (Fin N), pU N B S * X S = (Nat.choose N B : ℝ)⁻¹ * ∑ S ∈ AuditBudget.randomSchedules N B, X S
~~~

### 260. count_mem

Source: ControlStack/Families/F6/DamageBound.lean:515 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem count_mem (B : ℕ) (hB1 : 1 ≤ B) (a : Fin N) : ((AuditBudget.randomSchedules N B).filter (fun S => a ∈ S)).card = Nat.choose (N - 1) (B - 1)
~~~

### 261. hyp_step

Source: ControlStack/Families/F6/DamageBound.lean:529 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hyp_step (B k : ℕ) (hB : B ≤ N) (hk : k < N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : hypMiss N B (k + 1) r ≤ (1 - r * B / N) * hypMiss N B k r
~~~

### 262. hypMiss_zero

Source: ControlStack/Families/F6/DamageBound.lean:645 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hypMiss_zero (B : ℕ) (hB : B ≤ N) (r : ℝ) : hypMiss N B 0 r = 1
~~~

### 263. hyp_geom

Source: ControlStack/Families/F6/DamageBound.lean:651 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hyp_geom (B : ℕ) (hB : B ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : ∀ k, k ≤ N → hypMiss N B k r ≤ (1 - r * B / N) ^ k
~~~

### 264. expected_geom

Source: ControlStack/Families/F6/DamageBound.lean:672 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem expected_geom (B : ℕ) (hB : B ≤ N) (hB0 : 0 < B) (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) : ∑ j ∈ range N, hypMiss N B (j + 1) r ≤ ((N : ℝ) - r * B) / (r * B)
~~~

### 265. no_halt_damage

Source: ControlStack/Families/F6/DamageBound.lean:708 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_damage (N : ℕ) (D : ℝ) : val (fun (_ : List (Unit × AOut Unit)) z => if z = ((), ((true, (), true) : AOut Unit)) then (1 : ℝ) else 0) (fun t => D * (attackSet (N
~~~

### 266. no_cap_damage

Source: ControlStack/Families/F6/DamageBound.lean:732 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_cap_damage (M : ℝ) : val (fun (_ : List (Unit × AOut Unit)) z => if z = ((), ((true, (), false) : AOut Unit)) then (1 : ℝ) else 0) (fun t => M * ucX 1 t) 1 [] = M
~~~

### 267. example_r1

Source: ControlStack/Families/F6/DamageBound.lean:745 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem example_r1 : ∑ j ∈ range 100, hypMiss 100 10 (j + 1) 1 = 90 / 11
~~~

### 268. example_r_half

Source: ControlStack/Families/F6/DamageBound.lean:749 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem example_r_half : ∑ j ∈ range 100, hypMiss 100 10 (j + 1) (1 / 2) ≤ 19
~~~

## ControlStack/Families/F6/MonitorCollusion.lean

### 269. pass_transfer

Source: ControlStack/Families/F6/MonitorCollusion.lean:65 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem pass_transfer (Ph Pr β : V → ℝ) (hh : IsDist Ph) (hr : IsDist Pr) (hβ : ∀ v, 0 ≤ β v ∧ β v ≤ 1) : |passRate Pr β - passRate Ph β| ≤ tv Ph Pr
~~~

### 270. pass_equal

Source: ControlStack/Families/F6/MonitorCollusion.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pass_equal (Ph Pr β : V → ℝ) (heq : Ph = Pr) : passRate Pr β = passRate Ph β
~~~

### 271. sum_max_eq

Source: ControlStack/Families/F6/MonitorCollusion.lean:90 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_max_eq (P Q : V → ℝ) (hP : IsDist P) (hQ : IsDist Q) : ∑ v, max (P v) (Q v) = 1 + tv P Q
~~~

### 272. collusion_ml

Source: ControlStack/Families/F6/MonitorCollusion.lean:105 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem collusion_ml (p : Bool → ℝ) (lik : Bool → V → ℝ) (δ : V → Bool → ℝ) (hp : ∀ φ, 0 ≤ p φ) (hlik : ∀ φ v, 0 ≤ lik φ v) (hδ : ∀ v, IsDist (δ v)) : ∑ φ, p φ * ∑ v, lik φ v * ∑ a, δ v a * (if a = φ then 1 else 0) ≤ (∑ v, max (lik true v) (lik false v)) * max (p true) (p false)
~~~

### 273. collusion_uniform

Source: ControlStack/Families/F6/MonitorCollusion.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem collusion_uniform (Ph Pr : V → ℝ) (hh : IsDist Ph) (hr : IsDist Pr) (δ : V → Bool → ℝ) (hδ : ∀ v, IsDist (δ v)) : ∑ φ, (1 / 2 : ℝ) * ∑ v, (if φ then Pr v else Ph v) * ∑ a, δ v a * (if a = φ then 1 else 0) ≤ (1 + tv Pr Ph) / 2
~~~

### 274. canon_channel

Source: ControlStack/Families/F6/MonitorCollusion.lean:140 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem canon_channel {M : Type} [Fintype M] [DecidableEq M] [Nonempty M] (K : ℕ) (κ : V → Fin K) (enc : M → V → ℝ) (henc : ∀ m, IsDist (enc m)) (dec : Fin K → M → ℝ) (hdec : ∀ k, IsDist (dec k)) : ∑ m, (Fintype.card M : ℝ)⁻¹ * ∑ v, enc m v * ∑ a, dec (κ v) a * (if a = m then 1 else 0) ≤ (K : ℝ) * (Fintype.card M : ℝ)⁻¹
~~~

### 275. stego_fools_honeypots

Source: ControlStack/Families/F6/MonitorCollusion.lean:179 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stego_fools_honeypots : passRate stegoReal stegoMonitor = 1 ∧ passRate stegoHoney stegoMonitor = 0 ∧ tv stegoHoney stegoReal = 1
~~~

### 276. canon_restores

Source: ControlStack/Families/F6/MonitorCollusion.lean:185 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem canon_restores (β : Fin 1 → ℝ) : passRate stegoReal (fun v => β ((fun _ => 0 : Bool → Fin 1) v)) = passRate stegoHoney (fun v => β ((fun _ => 0 : Bool → Fin 1) v))
~~~

### 277. phase_learning

Source: ControlStack/Families/F6/MonitorCollusion.lean:203 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem phase_learning (K : Bool → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (L : ℝ) (hK0 : ∀ φ h z, 0 ≤ K φ h z) (hdom : ∀ φ, Dominated (K φ) c) (hc0 : ∀ g o, 0 ≤ c g o) (hL0 : 0 ≤ L) (hL : ∀ g, ∑ o, c g o ≤ L) (guess : List O → Bool → ℝ) (hg : ∀ t, IsDist (guess t)) (m : ℕ) : ∑ φ, (1 / 2 : ℝ) * val (K φ) (fun t => guess t φ) m [] ≤ (1 / 2) * L ^ m
~~~

### 278. bscK_dist

Source: ControlStack/Families/F6/MonitorCollusion.lean:216 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bscK_dist (φ : Bool) (h : List (Unit × Bool)) : IsDist (bscK φ h)
~~~

### 279. phase_example

Source: ControlStack/Families/F6/MonitorCollusion.lean:223 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem phase_example (guess : List Bool → Bool → ℝ) (hg : ∀ t, IsDist (guess t)) : ∑ φ, (1 / 2 : ℝ) * val (bscK φ) (fun t => guess t φ) 10 [] < 0.553
~~~

## ControlStack/Families/F6/ReservedAudit.lean

### 280. pU_nonneg

Source: ControlStack/Families/F6/ReservedAudit.lean:70 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pU_nonneg (N B : ℕ) (S : Finset (Fin N)) : 0 ≤ pU N B S
~~~

### 281. reserved_leak_bound_all

Source: ControlStack/Families/F6/ReservedAudit.lean:76 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reserved_leak_bound_all (k B : ℕ) (hB : B ≤ N) (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (hK0 : ∀ S h z, 0 ≤ K S h z) (hdom : ∀ S h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o) (hK1 : ∀ S h, ∑ z, K S h z ≤ 1) (hcl0 : ∀ g o, 0 ≤ cl g o) : ∑ S : Finset (Fin N), pU N B S * val (K S) (successInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * mass (dropStop caughtFlag cl) N []
~~~

### 282. reserved_leak_bound

Source: ControlStack/Families/F6/ReservedAudit.lean:114 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reserved_leak_bound (k B : ℕ) (hB : B ≤ N) (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1) (hdom : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o) (hcl0 : ∀ g o, 0 ≤ cl g o) : ∑ S : Finset (Fin N), pU N B S * val (K S) (successInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * mass (dropStop caughtFlag cl) N []
~~~

### 283. reserved_adaptive

Source: ControlStack/Families/F6/ReservedAudit.lean:157 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reserved_adaptive (k Bh : ℕ) (hB : Bh ≤ N) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hmarg : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, ∑ c : Bool, K S h (y, (a, (), c)) ≤ σ (h.map Prod.snd) a) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) (successInd k S) N [] ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ)
~~~

### 284. flagRun_inv

Source: ControlStack/Families/F6/ReservedAudit.lean:202 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem flagRun_inv (Bf : ℕ) (fs : List Bool) (st : ℕ × ℕ) (h : st.2 = min st.1 Bf) : (fs.foldl (flagStep Bf) st).2 = min (fs.foldl (flagStep Bf) st).1 Bf
~~~

### 285. flagRun_audits_le

Source: ControlStack/Families/F6/ReservedAudit.lean:215 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem flagRun_audits_le (Bf : ℕ) (fs : List Bool) : (flagRun Bf fs).2 ≤ Bf
~~~

### 286. reservedK_nonneg

Source: ControlStack/Families/F6/ReservedAudit.lean:229 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reservedK_nonneg (Bf : ℕ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (φ : Finset (Fin N) → List (Bool × AOut Unit) → Bool → Bool → ℝ) (hφ : ∀ S h a, IsDist (φ S h a)) (S : Finset (Fin N)) (h : List (Bool × AOut Unit)) (z : Bool × AOut Unit) : 0 ≤ reservedK Bf σ φ S h z
~~~

### 287. sum_ite_bool

Source: ControlStack/Families/F6/ReservedAudit.lean:235 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_ite_bool (e : Bool) : ∑ c : Bool, (if c = e then (1 : ℝ) else 0) = 1
~~~

### 288. reservedK_sum_c

Source: ControlStack/Families/F6/ReservedAudit.lean:239 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reservedK_sum_c (Bf : ℕ) (σ : List (AOut Unit) → Bool → ℝ) (φ : Finset (Fin N) → List (Bool × AOut Unit) → Bool → Bool → ℝ) (S : Finset (Fin N)) (h : List (Bool × AOut Unit)) (y a : Bool) : ∑ c : Bool, reservedK Bf σ φ S h (y, (a, (), c)) = σ (h.map Prod.snd) a * φ S h a y
~~~

### 289. reservedK_sum

Source: ControlStack/Families/F6/ReservedAudit.lean:247 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reservedK_sum (Bf : ℕ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (φ : Finset (Fin N) → List (Bool × AOut Unit) → Bool → Bool → ℝ) (hφ : ∀ S h a, IsDist (φ S h a)) (S : Finset (Fin N)) (h : List (Bool × AOut Unit)) : ∑ z, reservedK Bf σ φ S h z ≤ 1
~~~

### 290. reserved_policy_bound

Source: ControlStack/Families/F6/ReservedAudit.lean:261 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reserved_policy_bound (k Bh Bf : ℕ) (hB : Bh ≤ N) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (φ : Finset (Fin N) → List (Bool × AOut Unit) → Bool → Bool → ℝ) (hφ : ∀ S h a, IsDist (φ S h a)) : ∑ S : Finset (Fin N), pU N Bh S * val (reservedK Bf σ φ S) (successInd k S) N [] ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ)
~~~

### 291. flag_audits_le

Source: ControlStack/Families/F6/ReservedAudit.lean:281 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem flag_audits_le (Bf : ℕ) (flags : Fin N → Bool) : (univ.filter (fun i => Necessity.audited Bf flags i = true)).card ≤ Bf
~~~

### 292. reserved_total_le

Source: ControlStack/Families/F6/ReservedAudit.lean:308 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reserved_total_le (Bh Bf : ℕ) (S : Finset (Fin N)) (hS : S.card = Bh) (flags : Fin N → Bool) : (S ∪ univ.filter (fun i => Necessity.audited Bf flags i = true)).card ≤ Bh + Bf
~~~

### 293. sum_pU

Source: ControlStack/Families/F6/ReservedAudit.lean:326 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_pU (B : ℕ) (hB : B ≤ N) : ∑ S : Finset (Fin N), pU N B S = 1
~~~

### 294. sum_pU_disjoint

Source: ControlStack/Families/F6/ReservedAudit.lean:332 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_pU_disjoint (B k : ℕ) (A : Finset (Fin N)) (hA : A.card = k) : ∑ S : Finset (Fin N), pU N B S * (if Disjoint S A then 1 else 0) = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
~~~

### 295. missRecall_const

Source: ControlStack/Families/F6/ReservedAudit.lean:346 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem missRecall_const (B : ℕ) (A : Finset (Fin N)) (r : ℝ) : missRecall B A (fun _ => r) = ∑ S : Finset (Fin N), pU N B S * (1 - r) ^ (S ∩ A).card
~~~

### 296. recall_miss_le

Source: ControlStack/Families/F6/ReservedAudit.lean:354 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recall_miss_le (B k : ℕ) (hB : B ≤ N) (A : Finset (Fin N)) (hA : A.card = k) (r : ℝ) (rec : Fin N → ℝ) (hr0 : 0 ≤ r) (hrec : ∀ i, r ≤ rec i ∧ rec i ≤ 1) : missRecall B A rec ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) + (1 - (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)) * (1 - r)
~~~

### 297. observable_reserved_nogo

Source: ControlStack/Families/F6/ReservedAudit.lean:392 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem observable_reserved_nogo {N Bh k : ℕ} (S : Finset (Fin N)) (hS : S.card = Bh) (hk : k ≤ N - Bh) : ∃ A : Finset (Fin N), A.card = k ∧ Disjoint S A
~~~

### 298. observable_and_exhausted

Source: ControlStack/Families/F6/ReservedAudit.lean:400 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem observable_and_exhausted : Disjoint ({0} : Finset (Fin 4)) {2, 3} ∧ ∀ i ∈ ({2, 3} : Finset (Fin 4)), Necessity.audited 1 (fun _ => true) i = false
~~~

### 299. recall_zero_vacuous

Source: ControlStack/Families/F6/ReservedAudit.lean:407 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recall_zero_vacuous {N : ℕ} (B k : ℕ) (hB : B ≤ N) (A : Finset (Fin N)) : missRecall B A (fun _ => 0) = 1 ∧ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) + (1 - (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)) * (1 - 0) = 1
~~~

### 300. reserved_example

Source: ControlStack/Families/F6/ReservedAudit.lean:419 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reserved_example (Bf : ℕ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (φ : Finset (Fin 100) → List (Bool × AOut Unit) → Bool → Bool → ℝ) (hφ : ∀ S h a, IsDist (φ S h a)) : ∑ S : Finset (Fin 100), pU 100 10 S * val (reservedK Bf σ φ S) (successInd 5 S) 100 [] ≤ (10104934117421 : ℝ) / 17310309456440
~~~

### 301. recall_example

Source: ControlStack/Families/F6/ReservedAudit.lean:429 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recall_example (A : Finset (Fin 100)) (hA : A.card = 5) (rec : Fin 100 → ℝ) (hrec : ∀ i, 1 / 2 ≤ rec i ∧ rec i ≤ 1) : missRecall 10 A rec ≤ ((10104934117421 : ℝ) / 17310309456440 + 1) / 2
~~~

## ControlStack/Families/F6/ReservedRecall.lean

### 302. count_inter

Source: ControlStack/Families/F6/ReservedRecall.lean:53 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem count_inter (B k j : ℕ) (A : Finset (Fin N)) (hA : A.card = k) (hj : j ≤ B) : ((AuditBudget.randomSchedules N B).filter (fun S => (S ∩ A).card = j)).card = Nat.choose k j * Nat.choose (N - k) (B - j)
~~~

### 303. hypMiss_nonneg

Source: ControlStack/Families/F6/ReservedRecall.lean:108 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hypMiss_nonneg (N B k : ℕ) (r : ℝ) (hr1 : r ≤ 1) : 0 ≤ hypMiss N B k r
~~~

### 304. missRecall_closed

Source: ControlStack/Families/F6/ReservedRecall.lean:116 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem missRecall_closed (B k : ℕ) (A : Finset (Fin N)) (hA : A.card = k) (r : ℝ) : missRecall B A (fun _ => r) = hypMiss N B k r
~~~

### 305. missRecall_anti

Source: ControlStack/Families/F6/ReservedRecall.lean:141 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem missRecall_anti (B : ℕ) (A A' : Finset (Fin N)) (hAA : A ⊆ A') (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : missRecall B A' (fun _ => r) ≤ missRecall B A (fun _ => r)
~~~

### 306. miss_ge_k

Source: ControlStack/Families/F6/ReservedRecall.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem miss_ge_k (B k : ℕ) (A : Finset (Fin N)) (hA : k ≤ A.card) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : missRecall B A (fun _ => r) ≤ hypMiss N B k r
~~~

### 307. hypMiss_le_two_term

Source: ControlStack/Families/F6/ReservedRecall.lean:157 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hypMiss_le_two_term (B k : ℕ) (hB : B ≤ N) (hk : k ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : hypMiss N B k r ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) + (1 - (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)) * (1 - r)
~~~

### 308. cval_factor

Source: ControlStack/Families/F6/ReservedRecall.lean:175 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cval_factor (c f : List O → O → ℝ) (Φ : List O → ℝ) (B : List O → ℝ) (hΦ : ∀ g o, Φ (g ++ [o]) = Φ g * f g o) : ∀ n g, Φ g * cval (fun g o => c g o * f g o) B n g = cval c (fun t => B t * Φ t) n g
~~~

### 309. term_snoc

Source: ControlStack/Families/F6/ReservedRecall.lean:207 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem term_snoc (r : ℝ) (S : Finset (Fin N)) (g : List (AOut Unit)) (o : AOut Unit) (j : Fin N) : (if j ∈ S ∧ attNC (g ++ [o]) j = true then 1 - r else 1) = (if j ∈ S ∧ attNC g j = true then 1 - r else 1) * (if (j : ℕ) = g.length ∧ j ∈ S ∧ (o.1 = true ∧ o.2.2 = false) then 1 - r else 1)
~~~

### 310. prod_single_fac

Source: ControlStack/Families/F6/ReservedRecall.lean:230 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prod_single_fac (r : ℝ) (S : Finset (Fin N)) (g : List (AOut Unit)) (o : AOut Unit) : ∏ j : Fin N, (if (j : ℕ) = g.length ∧ j ∈ S ∧ (o.1 = true ∧ o.2.2 = false) then 1 - r else 1) = fac r S g o
~~~

### 311. phi_snoc

Source: ControlStack/Families/F6/ReservedRecall.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem phi_snoc (r : ℝ) (S : Finset (Fin N)) (g : List (AOut Unit)) (o : AOut Unit) : phi r S (g ++ [o]) = phi r S g * fac r S g o
~~~

### 312. phi_nil

Source: ControlStack/Families/F6/ReservedRecall.lean:257 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem phi_nil (r : ℝ) (S : Finset (Fin N)) : phi r S [] = 1
~~~

### 313. phi_live

Source: ControlStack/Families/F6/ReservedRecall.lean:261 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem phi_live (r : ℝ) (S : Finset (Fin N)) (t : List (AOut Unit)) (hl : (t.all fun o => !caughtFlag o) = true) : phi r S t = (1 - r) ^ (S ∩ attackSet (N
~~~

### 314. adaptive_recall_bound

Source: ControlStack/Families/F6/ReservedRecall.lean:292 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adaptive_recall_bound {Y : Type} [Fintype Y] (k Bh : ℕ) (_hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) (recallSucc (N
~~~

### 315. adaptive_recall_two_term

Source: ControlStack/Families/F6/ReservedRecall.lean:377 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adaptive_recall_two_term {Y : Type} [Fintype Y] (k Bh : ℕ) (hB : Bh ≤ N) (hk : k ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool), ∑ y, K S h (y, (a, (), false)) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) : ∑ S : Finset (Fin N), pU N Bh S * val (K S) (recallSucc (N
~~~

### 316. recall_instance_bound

Source: ControlStack/Families/F6/ReservedRecall.lean:402 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recall_instance_bound (k Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) : ∑ S : Finset (Fin N), pU N Bh S * val (recallK r σ S) (recallSucc (N
~~~

### 317. recall_example

Source: ControlStack/Families/F6/ReservedRecall.lean:424 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem recall_example (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) : ∑ S : Finset (Fin 100), pU 100 10 S * val (recallK (1 / 2) σ S) (recallSucc (N
~~~

## ControlStack/GateComposition.lean

### 318. shared_invariants

Source: ControlStack/GateComposition.lean:18 | Family: F8 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem shared_invariants {S A : Type} (P Q : S → Prop) (step : S → A → S) (s : S) (actions : List A) (hJoint : ∀ (x : S) (a : A), P x → Q x → P (step x a) ∧ Q (step x a)) (h : P s ∧ Q s) : P (run step s actions) ∧ Q (run step s actions)
~~~

### 319. confused_deputy_counterexample

Source: ControlStack/GateComposition.lean:45 | Family: F8 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem confused_deputy_counterexample : (unsafeDeputyStep { gateAApproved
~~~

## ControlStack/GatewayCore.lean

### 320. frozen

Source: ControlStack/GatewayCore.lean:72 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma frozen (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (v : View S slots) (h : st.snap = some v) (tr : List (Ev C R)) : runG valid st tr = st
~~~

### 321. close_freezes

Source: ControlStack/GatewayCore.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem close_freezes (valid : (c : Fin C) → R → Option (S c)) (pre post : List (Ev C R)) : finalView (runG valid (init (S
~~~

### 322. blanked_stays

Source: ControlStack/GatewayCore.lean:101 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma blanked_stays (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (hb : st.blanked = true) (hs : st.snap = none ∨ st.snap = some nullView) (tr : List (Ev C R)) : (runG valid st tr).blanked = true ∧ ((runG valid st tr).snap = none ∨ (runG valid st tr).snap = some nullView)
~~~

### 323. finalView_blanked

Source: ControlStack/GatewayCore.lean:144 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma finalView_blanked (st : GSt S slots) (hb : st.blanked = true) (hs : st.snap = none ∨ st.snap = some nullView) : finalView st = nullView
~~~

### 324. refusal_blanks

Source: ControlStack/GatewayCore.lean:152 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refusal_blanks (valid : (c : Fin C) → R → Option (S c)) (pre post : List (Ev C R)) (e : Ev C R) (hpre : (runG valid (init (S
~~~

### 325. other_blanks

Source: ControlStack/GatewayCore.lean:184 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem other_blanks (valid : (c : Fin C) → R → Option (S c)) (pre post : List (Ev C R)) (hpre : (runG valid (init (S
~~~

### 326. card_prefixes

Source: ControlStack/GatewayCore.lean:200 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem card_prefixes [∀ c, Fintype (S c)] [∀ c, DecidableEq (S c)] : Fintype.card (Prefixes S slots) = viewSpace slots (fun c => Fintype.card (S c))
~~~

### 327. viewOf_reachable

Source: ControlStack/GatewayCore.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma viewOf_reachable (st : GSt S slots) (h : ∀ c, (st.buf c).length ≤ slots c) : viewOf st ∈ Set.range (embedAll (S
~~~

### 328. gstep_inv

Source: ControlStack/GatewayCore.lean:217 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma gstep_inv (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (e : Ev C R) (h : Inv st) : Inv (gstep valid st e)
~~~

### 329. runG_inv

Source: ControlStack/GatewayCore.lean:247 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma runG_inv (valid : (c : Fin C) → R → Option (S c)) (tr : List (Ev C R)) (st : GSt S slots) (h : Inv st) : Inv (runG valid st tr)
~~~

### 330. view_reachable

Source: ControlStack/GatewayCore.lean:254 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem view_reachable (valid : (c : Fin C) → R → Option (S c)) (tr : List (Ev C R)) : finalView (runG valid (init (S
~~~

### 331. core_bound

Source: ControlStack/GatewayCore.lean:265 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem core_bound {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R] [∀ c, Fintype (S c)] [∀ c, DecidableEq (S c)] [Fintype (Ev C R)] (valid : (c : Fin C) → R → Option (S c)) (L : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ) (dec : Ω → View S slots → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : (∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ tr, enc ω m tr * dec ω (finalView (runG valid (init (S
~~~

### 332. sc01_episode_views

Source: ControlStack/GatewayCore.lean:297 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sc01_episode_views : viewSpace (C
~~~

## ControlStack/GatewayModel.lean

### 333. blank_absorbing

Source: ControlStack/GatewayModel.lean:47 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem blank_absorbing {R S : Type} (valid : R → Option S) (slots : ℕ) (tr : List (Act R)) (st : St S) (h : st.blanked = true) : (tr.foldl (step valid slots) st).blanked = true
~~~

### 334. other_blanks

Source: ControlStack/GatewayModel.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem other_blanks {R S : Type} (valid : R → Option S) (slots : ℕ) (pre post : List (Act R)) : deliver slots (run valid slots (pre ++ Act.other :: post)) = fun _ => none
~~~

### 335. push_dist

Source: ControlStack/GatewayModel.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_dist {T V : Type} [Fintype T] [Fintype V] [DecidableEq V] (f : T → V) (p : T → ℝ) (hp : IsDist p) : IsDist (push f p)
~~~

### 336. gateway_bound

Source: ControlStack/GatewayModel.lean:84 | Family: F2 | Adversary: SHARED_SEED | Status: PROVED_RECORDED

~~~lean
theorem gateway_bound {Ω M R S : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R] [Fintype S] [DecidableEq S] (valid : R → Option S) (slots L : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → (Fin L → Act R) → ℝ) (dec : Ω → (Fin slots → Option S) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : (∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ tr, enc ω m tr * dec ω (deliver slots (run valid slots (List.ofFn tr))) m)) ≤ ((Fintype.card S : ℝ) + 1) ^ slots / (Fintype.card M : ℝ)
~~~

### 337. buf_le

Source: ControlStack/GatewayModel.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem buf_le {R S : Type} (valid : R → Option S) (slots : ℕ) (tr : List (Act R)) (st : St S) (h : st.buf.length ≤ slots) : (tr.foldl (step valid slots) st).buf.length ≤ slots
~~~

### 338. deliver_eq_embed

Source: ControlStack/GatewayModel.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deliver_eq_embed {S : Type} (slots : ℕ) (st : St S) (h : st.buf.length ≤ slots) : deliver slots st = embedPrefix slots (toPrefix slots st h)
~~~

### 339. gateway_bound_reachable

Source: ControlStack/GatewayModel.lean:153 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gateway_bound_reachable {Ω M R S : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R] [Fintype S] [DecidableEq S] (valid : R → Option S) (slots L : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → (Fin L → Act R) → ℝ) (dec : Ω → (Fin slots → Option S) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : (∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ tr, enc ω m tr * dec ω (deliver slots (run valid slots (List.ofFn tr))) m)) ≤ (∑ j : Fin (slots + 1), (Fintype.card S : ℝ) ^ (j : ℕ)) / (Fintype.card M : ℝ)
~~~

## ControlStack/HaltLiveness.lean

### 340. run_append

Source: ControlStack/HaltLiveness.lean:18 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_append {St Op Eff : Type} (G : System St Op Eff) (s : St) (before after : List Op) : G.run s (before ++ after) = G.run (G.run s before) after
~~~

### 341. delivered_halt_absorbs

Source: ControlStack/HaltLiveness.lean:24 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem delivered_halt_absorbs {St Op Eff : Type} (G : System St Op Eff) (sh : St × Bool) (rest : List (HOp Op)) : (withHalt G).run sh (.halt :: rest) = (sh.1, true)
~~~

### 342. liveness_if_delivered

Source: ControlStack/HaltLiveness.lean:40 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem liveness_if_delivered {St Op Eff : Type} (G : System St Op Eff) (s : St) (n : Nat) (ops : List (HOp Op)) (h : DeliveredWithin n ops) : ((withHalt G).run (s, false) ops).2 = true
~~~

### 343. effects_frozen_after_delivered_halt

Source: ControlStack/HaltLiveness.lean:51 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem effects_frozen_after_delivered_halt {St Op Eff : Type} (G : System St Op Eff) (s : St) (before after : List (HOp Op)) : (withHalt G).effects ((withHalt G).run (s, false) (before ++ (.halt :: after))) = (withHalt G).effects ((withHalt G).run (s, false) before)
~~~

### 344. ordinary_operations_never_halt

Source: ControlStack/HaltLiveness.lean:62 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem ordinary_operations_never_halt {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List Op) : ((withHalt G).run (s, false) (ops.map HOp.op)).2 = false
~~~

## ControlStack/HoneypotBridgeProof.lean

### 345. honeypotPasses_step

Source: ControlStack/HoneypotBridgeProof.lean:34 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honeypotPasses_step {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (n k : ℕ) : Pr[= k | honeypotPasses H M D (n + 1)] = Pr[= true | H >>= M >>= D] * Pr[= k | (fun a => a + 1) <$> honeypotPasses H M D n] + Pr[= false | H >>= M >>= D] * Pr[= k | honeypotPasses H M D n]
~~~

### 346. honeypotPasses_probOutput

Source: ControlStack/HoneypotBridgeProof.lean:42 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honeypotPasses_probOutput {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (n k : ℕ) : Pr[= k | honeypotPasses H M D n] = (n.choose k : ENNReal) * Pr[= true | H >>= M >>= D] ^ k * Pr[= false | H >>= M >>= D] ^ (n - k)
~~~

### 347. bridge

Source: ControlStack/HoneypotBridgeProof.lean:76 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bridge : BridgeClaim
~~~

## ControlStack/LifetimeLedger.lean

### 348. pr_append_one

Source: ControlStack/LifetimeLedger.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma pr_append_one (ℓ ℓ' : L) (k : ℕ) (adm : List (L × ℕ)) : pr ℓ' (adm ++ [(ℓ, k)]) = pr ℓ' adm * (if ℓ = ℓ' then k else 1)
~~~

### 349. step_inv

Source: ControlStack/LifetimeLedger.lean:69 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma step_inv (cap : ℕ) (s : Option (L → ℕ)) (adm : List (L × ℕ)) (e : Ev L) (he : ¬ e.isRestore) (h : Inv cap (s, adm)) : Inv cap ((step cap s e).1, adm ++ (step cap s e).2.toList)
~~~

### 350. run_inv

Source: ControlStack/LifetimeLedger.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma run_inv (cap : ℕ) : ∀ (es : List (Ev L)) (st : Option (L → ℕ) × List (L × ℕ)), (∀ e ∈ es, ¬ e.isRestore) → Inv cap st → Inv cap (run cap st es) | [], st, _, h => h | e :: es, (s, adm), hes, h => by simp only [run] exact run_inv cap es _ (fun e' he' => hes e' (List.mem_cons_of_mem e he')) (step_inv cap s adm e (hes e List.mem_cons_self) h) theorem ledger_safe (cap : ℕ) (hcap : 1 ≤ cap) (es : List (Ev L)) (hes : ∀ e ∈ es, ¬ e.isRestore) (ℓ : L) : pr ℓ (run cap (some (fun _ => 1), []) es).2 ≤ cap
~~~

### 351. ledger_safe

Source: ControlStack/LifetimeLedger.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ledger_safe (cap : ℕ) (hcap : 1 ≤ cap) (es : List (Ev L)) (hes : ∀ e ∈ es, ¬ e.isRestore) (ℓ : L) : pr ℓ (run cap (some (fun _ => 1), []) es).2 ≤ cap
~~~

### 352. restore_breaks

Source: ControlStack/LifetimeLedger.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem restore_breaks (cap : ℕ) (hcap : 2 ≤ cap) (ℓ : L) : cap < pr ℓ (run cap (some (fun _ => 1), []) [.charge ℓ cap, .restore (fun _ => 1), .charge ℓ cap]).2
~~~

### 353. lifetime_secret_bound

Source: ControlStack/LifetimeLedger.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lifetime_secret_bound {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] {E : ℕ} (V : Fin E → Type) [∀ e, Fintype (V e)] [∀ e, DecidableEq (V e)] (cap : ℕ) (hV : ∏ e, Fintype.card (V e) ≤ cap) (ρ : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ) (dec : Ω → ((e : Fin E) → V e) → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (cap : ℝ) / (Fintype.card M : ℝ)
~~~

## ControlStack/MultiStep.lean

### 354. V_zero

Source: ControlStack/MultiStep.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
@[simp] theorem V_zero {A : Type} [Fintype A] (π κ : List A → A → ℝ) (h : List A) : V π κ 0 h = 1
~~~

### 355. V_succ

Source: ControlStack/MultiStep.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem V_succ {A : Type} [Fintype A] (π κ : List A → A → ℝ) (k : ℕ) (h : List A) : V π κ (k + 1) h = ∑ a, π h a * (1 - κ h a) * V π κ k (h ++ [a])
~~~

### 356. survival_bounds

Source: ControlStack/MultiStep.lean:54 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_bounds {A : Type} [Fintype A] (π κ : List A → A → ℝ) (hπ : IsPolicy π) (hκ : IsMonitor κ) (k : ℕ) (h : List A) : 0 ≤ V π κ k h ∧ V π κ k h ≤ 1
~~~

### 357. survival_le

Source: ControlStack/MultiStep.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_le {A : Type} [Fintype A] (π κ : List A → A → ℝ) (hπ : IsPolicy π) (hκ : IsMonitor κ) (c : ℝ) (hc1 : c ≤ 1) (hcκ : ∀ h a, c ≤ κ h a) (k : ℕ) (h : List A) : V π κ k h ≤ (1 - c) ^ k
~~~

### 358. survival_const

Source: ControlStack/MultiStep.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_const {A : Type} [Fintype A] (π : List A → A → ℝ) (hπ : IsPolicy π) (c : ℝ) (k : ℕ) (h : List A) : V π (fun _ _ => c) k h = (1 - c) ^ k
~~~

### 359. V_never

Source: ControlStack/MultiStep.lean:104 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem V_never {A : Type} [Fintype A] (π : List A → A → ℝ) (hπ : IsPolicy π) (k : ℕ) (h : List A) : V π (fun _ _ => 0) k h = 1
~~~

### 360. V_always

Source: ControlStack/MultiStep.lean:109 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem V_always {A : Type} [Fintype A] (π : List A → A → ℝ) (k : ℕ) (h : List A) : V π (fun _ _ => 1) (k + 1) h = 0
~~~

### 361. seeded_marginal

Source: ControlStack/MultiStep.lean:125 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seeded_marginal {A : Type} (c : ℝ) (h : List A) (a : A) : seededMarginal c h a = c
~~~

### 362. seeded_survival

Source: ControlStack/MultiStep.lean:129 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seeded_survival {A : Type} [Fintype A] (c : ℝ) (π : List A → A → ℝ) (hπ : IsPolicy π) (k : ℕ) (hk : 1 ≤ k) (h : List A) : V π (seededκ true) k h = 0 ∧ V π (seededκ false) k h = 1 ∧ seededSurvival c π k h = 1 - c
~~~

### 363. pow_lt_self_of_two_le

Source: ControlStack/MultiStep.lean:139 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pow_lt_self_of_two_le (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (k : ℕ) (hk : 2 ≤ k) : (1 - c) ^ k < 1 - c
~~~

### 364. correlated_nogo

Source: ControlStack/MultiStep.lean:149 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem correlated_nogo {A : Type} [Fintype A] (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (π : List A → A → ℝ) (hπ : IsPolicy π) (k : ℕ) (hk : 2 ≤ k) (h : List A) : (∀ (h' : List A) (a : A), seededMarginal c h' a = c) ∧ seededSurvival c π k h = 1 - c ∧ V π (fun _ _ => c) k h = (1 - c) ^ k ∧ (1 - c) ^ k < seededSurvival c π k h
~~~

### 365. Vs_eq

Source: ControlStack/MultiStep.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Vs_eq {A Θ : Type} [Fintype A] [Fintype Θ] (π : List A → A → ℝ) (κ : Θ → List A → A → ℝ) (k : ℕ) (h : List A) (w : Θ → ℝ) : Vs π κ k h w = ∑ θ, w θ * V π (κ θ) k h
~~~

### 366. reachable_nonneg

Source: ControlStack/MultiStep.lean:184 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reachable_nonneg {A Θ : Type} (ρ : Θ → ℝ) (κ : Θ → List A → A → ℝ) (hρ : ∀ θ, 0 ≤ ρ θ) (hκ : ∀ θ, IsMonitor (κ θ)) {h : List A} {w : Θ → ℝ} (hr : Reachable ρ κ h w) : ∀ θ, 0 ≤ w θ
~~~

### 367. survival_avg

Source: ControlStack/MultiStep.lean:195 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_avg {A Θ : Type} [Fintype A] [Fintype Θ] (π : List A → A → ℝ) (hπ : IsPolicy π) (κ : Θ → List A → A → ℝ) (ρ : Θ → ℝ) (c : ℝ) (hc1 : c ≤ 1) (hpost : ∀ h w, Reachable ρ κ h w → ∀ a, c * ∑ θ, w θ ≤ ∑ θ, w θ * κ θ h a) (k : ℕ) : ∑ θ, ρ θ * V π (κ θ) k [] ≤ (1 - c) ^ k * ∑ θ, ρ θ
~~~

### 368. seeded_violates_posterior

Source: ControlStack/MultiStep.lean:225 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seeded_violates_posterior {A : Type} (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (a b : A) : let ρ : Bool → ℝ
~~~

### 369. survival_example

Source: ControlStack/MultiStep.lean:235 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survival_example {A : Type} [Fintype A] (π κ : List A → A → ℝ) (hπ : IsPolicy π) (hκ : IsMonitor κ) (hcκ : ∀ h a, (1 / 10 : ℝ) ≤ κ h a) (h : List A) : V π κ 5 h ≤ 0.59049
~~~

## ControlStack/OutcomeProof.lean

### 370. probOutput_isCat

Source: ControlStack/OutcomeProof.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_isCat (c : ProbComp Outcome) : Pr[= true | isCat <$> c] = Pr[= Outcome.catastrophe | c]
~~~

### 371. map_deployO

Source: ControlStack/OutcomeProof.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem map_deployO {X Z : Type} (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n : ℕ) : ∀ u h, isCat <$> deployO Bad π M D A b n u h = deploy Bad π M D A b n u h
~~~

### 372. marginal

Source: ControlStack/OutcomeProof.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem marginal : MarginalClaim
~~~

### 373. probOutput_auditO

Source: ControlStack/OutcomeProof.lean:44 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_auditO (c : ProbComp Bool) (o : Outcome) : Pr[= o | (fun caught => if caught then Outcome.caught else Outcome.catastrophe) <$> c] = Pr[= true | c] * (if o = Outcome.caught then 1 else 0) + Pr[= false | c] * (if o = Outcome.catastrophe then 1 else 0)
~~~

### 374. deployO_step

Source: ControlStack/OutcomeProof.lean:51 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployO_step {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) (o : Outcome) : Pr[= o | deployO Bad π M D A b (n+1) u h] = ∑ x, Pr[= x | π h] * ∑ z, Pr[= z | M x] * (Pr[= true | D z] * Pr[= o | (if Bad x then pure .catastrophe else deployO Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Outcome)] + Pr[= false | D z] * Pr[= o | (if u < b then (if Bad x then (fun caught => if caught then Outcome.caught else Outcome.catastrophe) <$> A h x z else deployO Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure .halted : ProbComp Outcome)])
~~~

### 375. deployO_step_real

Source: ControlStack/OutcomeProof.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployO_step_real {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) (o : Outcome) : (Pr[= o | deployO Bad π M D A b (n+1) u h]).toReal = ∑ x, (Pr[= x | π h]).toReal * ∑ z, (Pr[= z | M x]).toReal * ((Pr[= true | D z]).toReal * (Pr[= o | (if Bad x then pure .catastrophe else deployO Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Outcome)]).toReal + (1 - (Pr[= true | D z]).toReal) * (Pr[= o | (if u < b then (if Bad x then (fun caught => if caught then Outcome.caught else Outcome.catastrophe) <$> A h x z else deployO Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure .halted : ProbComp Outcome)]).toReal)
~~~

### 376. deployO_rejected

Source: ControlStack/OutcomeProof.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployO_rejected {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n : ℕ) : ∀ u h, Pr[= Outcome.rejected | deployO Bad π M D A b n u h] = 0
~~~

### 377. deployLaw

Source: ControlStack/OutcomeProof.lean:99 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployLaw : DeployLawClaim
~~~

### 378. conservation

Source: ControlStack/OutcomeProof.lean:129 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conservation : ConservationClaim
~~~

### 379. nonneg

Source: ControlStack/OutcomeProof.lean:154 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nonneg : NonnegClaim
~~~

### 380. deployO_rejected

Source: ControlStack/OutcomeProof.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployO_rejected' {X Z : Type} (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n : ℕ) : ∀ u h, Pr[= Outcome.rejected | deployO Bad π M D A b n u h] = 0
~~~

### 381. probEvent_not_toReal

Source: ControlStack/OutcomeProof.lean:190 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probEvent_not_toReal {α : Type} (c : ProbComp α) (p : α → Prop) : (Pr[fun x => ¬ p x | c]).toReal = 1 - (Pr[p | c]).toReal
~~~

### 382. gameLaw

Source: ControlStack/OutcomeProof.lean:199 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gameLaw : GameLawClaim
~~~

### 383. rateLink

Source: ControlStack/OutcomeProof.lean:231 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rateLink : RateLinkClaim
~~~

### 384. binCDF_succ_zero

Source: ControlStack/OutcomeProof.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem binCDF_succ_zero (n : ℕ) (f : ℝ) : binCDF (n + 1) 0 f = (1 - f) * binCDF n 0 f
~~~

### 385. binCDF_succ_succ

Source: ControlStack/OutcomeProof.lean:255 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem binCDF_succ_succ (n s : ℕ) (f : ℝ) : binCDF (n + 1) (s + 1) f = (1 - f) * binCDF n (s + 1) f + f * binCDF n s f
~~~

### 386. wsum_const

Source: ControlStack/OutcomeProof.lean:275 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum_const {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (φ : Z → ℝ) (μ : X → ℝ) (hM1 : ∀ x, ∑ z, M x z = 1) (hμ1 : ∑ x, μ x = 1) (a c : ℝ) : ∑ x, μ x * ∑ z, M x z * (φ z * a + (1 - φ z) * c) = (1 - flagRate M μ φ) * a + flagRate M μ φ * c
~~~

### 387. catG_benign

Source: ControlStack/OutcomeProof.lean:297 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catG_benign {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R : Hist X Z → X → Z → ℝ) (b : ℕ) (hben : ∀ h x, π h x ≠ 0 → ¬ Bad x) : ∀ n u h, catG Bad M φ π R b n u h = 0 ∧ caughtG Bad M φ π R b n u h = 0
~~~

### 388. complG_benign

Source: ControlStack/OutcomeProof.lean:312 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem complG_benign {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (μ : X → ℝ) (b : ℕ) (hM1 : ∀ x, ∑ z, M x z = 1) (hμ1 : ∑ x, μ x = 1) (hben : ∀ x, μ x ≠ 0 → ¬ Bad x) : ∀ n u h, u ≤ b → complG Bad M φ (fun _ => μ) b n u h = binCDF n (b - u) (flagRate M μ φ)
~~~

### 389. benignRecursion

Source: ControlStack/OutcomeProof.lean:341 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem benignRecursion : BenignRecursionClaim
~~~

### 390. honest

Source: ControlStack/OutcomeProof.lean:351 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest : HonestClaim
~~~

### 391. binCDF_nonneg

Source: ControlStack/OutcomeProof.lean:387 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem binCDF_nonneg (n s : ℕ) (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1) : 0 ≤ binCDF n s f
~~~

### 392. pareto

Source: ControlStack/OutcomeProof.lean:392 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pareto : ParetoClaim
~~~

### 393. witness

Source: ControlStack/OutcomeProof.lean:431 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## ControlStack/PolicyTamper.lean

### 394. policy_preserved_if_protected

Source: ControlStack/PolicyTamper.lean:31 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem policy_preserved_if_protected (p : Policy) (s : St) (ops : List Op) (h : s.activePolicy = p) : (run false s ops).activePolicy = p
~~~

### 395. tamper_possible_if_writable

Source: ControlStack/PolicyTamper.lean:42 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: SOURCE_ONLY

~~~lean
theorem tamper_possible_if_writable (s : St) (replacement : Policy) : (step true s (.attemptPolicyWrite replacement)).activePolicy = replacement
~~~

## ControlStack/RefinementProof.lean

### 396. probOutput_true_add_false_one

Source: ControlStack/RefinementProof.lean:6 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_true_add_false_one (c : ProbComp Bool) : Pr[= true | c] + Pr[= false | c] = 1
~~~

### 397. probOutput_false_toReal

Source: ControlStack/RefinementProof.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_false_toReal (c : ProbComp Bool) : (Pr[= false | c]).toReal = 1 - (Pr[= true | c]).toReal
~~~

### 398. probOutput_not_true

Source: ControlStack/RefinementProof.lean:20 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem probOutput_not_true (c : ProbComp Bool) : Pr[= true | (fun caught => !caught) <$> c] = Pr[= false | c]
~~~

### 399. deploy_step

Source: ControlStack/RefinementProof.lean:24 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deploy_step {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) : Pr[= true | deploy Bad π M D A b (n+1) u h] = ∑ x, Pr[= x | π h] * ∑ z, Pr[= z | M x] * (Pr[= true | D z] * Pr[= true | (if Bad x then pure true else deploy Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Bool)] + Pr[= false | D z] * Pr[= true | (if u < b then (if Bad x then (fun caught => !caught) <$> A h x z else deploy Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure false : ProbComp Bool)])
~~~

### 400. deploy_step_real

Source: ControlStack/RefinementProof.lean:36 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deploy_step_real {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) : (Pr[= true | deploy Bad π M D A b (n+1) u h]).toReal = ∑ x, (Pr[= x | π h]).toReal * ∑ z, (Pr[= z | M x]).toReal * ((Pr[= true | D z]).toReal * (Pr[= true | (if Bad x then pure true else deploy Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Bool)]).toReal + (1 - (Pr[= true | D z]).toReal) * (Pr[= true | (if u < b then (if Bad x then (fun caught => !caught) <$> A h x z else deploy Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure false : ProbComp Bool)]).toReal)
~~~

### 401. toReal_probOutput_le_one

Source: ControlStack/RefinementProof.lean:58 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem toReal_probOutput_le_one {α : Type} (c : ProbComp α) (x : α) : (Pr[= x | c]).toReal ≤ 1
~~~

### 402. toReal_probEvent_le_one

Source: ControlStack/RefinementProof.lean:62 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem toReal_probEvent_le_one {α : Type} (c : ProbComp α) (p : α → Prop) : (Pr[p | c]).toReal ≤ 1
~~~

### 403. sum_toReal_probOutput

Source: ControlStack/RefinementProof.lean:66 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_toReal_probOutput {α : Type} [Fintype α] (c : ProbComp α) : ∑ x, (Pr[= x | c]).toReal = 1
~~~

### 404. catG_const

Source: ControlStack/RefinementProof.lean:72 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catG_const {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (b : ℕ) : ∀ n u h, catG Bad M φ π (fun _ _ _ => r) b n u h = cat Bad M φ π r b n u h
~~~

### 405. catG_congr

Source: ControlStack/RefinementProof.lean:80 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catG_congr {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R R' : Hist X Z → X → Z → ℝ) (b : ℕ) (hR : ∀ h x z, Bad x → R h x z = R' h x z) : ∀ n u h, catG Bad M φ π R b n u h = catG Bad M φ π R' b n u h
~~~

### 406. catG_le_cat

Source: ControlStack/RefinementProof.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catG_le_cat {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R : Hist X Z → X → Z → ℝ) (r : ℝ) (b : ℕ) (hπ : ∀ h x, 0 ≤ π h x) (hM : ∀ x z, 0 ≤ M x z) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) (hR : ∀ h x z, Bad x → r ≤ R h x z) : ∀ n u h, catG Bad M φ π R b n u h ≤ cat Bad M φ π r b n u h
~~~

### 407. wsum_le

Source: ControlStack/RefinementProof.lean:122 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum_le {Y : Type} [Fintype Y] (w f : Y → ℝ) (c : ℝ) (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∑ y, w y = 1) (hf : ∀ y, f y ≤ c) : ∑ y, w y * f y ≤ c
~~~

### 408. t3a

Source: ControlStack/RefinementProof.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t3a {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r A : ℝ) (b : ℕ) (hM0 : ∀ x z, 0 ≤ M x z) (hM1 : ∀ x, ∑ z, M x z = 1) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) (hπ0 : ∀ h x, 0 ≤ π h x) (hπ1 : ∀ h, ∑ x, π h x = 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hbad : ∀ x, Bad x → ∑ z, M x z * φ z ≤ A) : ∀ n u h, cat Bad M φ π r b n u h ≤ (if u < b then 1 - r + r * A else A)
~~~

### 409. final_dom

Source: ControlStack/RefinementProof.lean:185 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem final_dom (S h L r A B : ℝ) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hA : A ≤ L * h) (hB : h * S ≤ B) : S * (1 - r + r * A) ≤ (1 - r) + r * (L * B)
~~~

### 410. first_moment

Source: ControlStack/RefinementProof.lean:198 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem first_moment (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hB : binCDF (n + 1) (s + 1) h ≤ 1) : ((n : ℝ) + 1) * (h * binCDF n s h) ≤ (s : ℝ) + 1
~~~

### 411. first_moment

Source: ControlStack/RefinementProof.lean:238 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem first_moment' (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hB : binCDF (n + 1) (s + 1) h ≤ 1) : h * binCDF n s h ≤ ((s : ℝ) + 1) / ((n : ℝ) + 1)
~~~

### 412. deployG

Source: ControlStack/RefinementProof.lean:245 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployG : DeployGClaim
~~~

### 413. deploy_le

Source: ControlStack/RefinementProof.lean:258 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deploy_le : DeployClaim
~~~

### 414. deploy_exact

Source: ControlStack/RefinementProof.lean:264 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deploy_exact : DeployExactClaim
~~~

### 415. protocol

Source: ControlStack/RefinementProof.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem protocol : ProtocolClaim
~~~

### 416. endToEnd

Source: ControlStack/RefinementProof.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem endToEnd : EndToEndClaim
~~~

### 417. attain

Source: ControlStack/RefinementProof.lean:343 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attain : AttainClaim
~~~

### 418. witness

Source: ControlStack/RefinementProof.lean:375 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## ControlStack/SafetyCaseSC01.lean

### 419. step_adm

Source: ControlStack/SafetyCaseSC01.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma step_adm {L : Type} [DecidableEq L] (cap : ℕ) (s : Option (L → ℕ)) (e : Ev L) (a : L × ℕ) (h : (step cap s e).2 = some a) : ∃ ℓ k, e = .charge ℓ k ∧ a = (ℓ, k)
~~~

### 420. run_sizes

Source: ControlStack/SafetyCaseSC01.lean:32 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma run_sizes {L : Type} [DecidableEq L] (cap : ℕ) (K : ℕ) : ∀ (es : List (Ev L)) (st : Option (L → ℕ) × List (L × ℕ)), (∀ e ∈ es, ∀ ℓ k, e = .charge ℓ k → k = K) → (∀ a ∈ st.2, a.2 = K) → ∀ a ∈ (run cap st es).2, a.2 = K | [], st, _, h => h | e :: es, (s, adm), hes, h => by simp only [run] apply run_sizes cap K es _ (fun e' he' => hes e' (List.mem_cons_of_mem e he')) intro a ha rcases List.mem_append.1 ha with ha | ha · exact h a ha · cases hst : (step cap s e).2 with | none => simp [hst] at ha | some b => simp [hst] at ha; rw [ha] obtain ⟨ℓ, k, rfl, rfl⟩
~~~

### 421. pr_const

Source: ControlStack/SafetyCaseSC01.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma pr_const {L : Type} [DecidableEq L] (ℓ : L) (K : ℕ) (adm : List (L × ℕ)) (h : ∀ a ∈ adm, a.2 = K) : pr ℓ adm = K ^ (adm.filter (fun a => a.1 = ℓ)).length
~~~

### 422. ledger_five

Source: ControlStack/SafetyCaseSC01.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ledger_five {L : Type} [DecidableEq L] (es : List (Ev L)) (hes : ∀ e ∈ es, ¬ e.isRestore) (h9 : ∀ e ∈ es, ∀ ℓ k, e = .charge ℓ k → k = 9) (ℓ : L) : ((run (2 ^ 16) (some (fun _ => 1), []) es).2.filter (fun a => a.1 = ℓ)).length ≤ 5
~~~

### 423. bit_refutes

Source: ControlStack/SafetyCaseSC01.lean:78 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bit_refutes {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (enc : Ω → Bool → Unit × S → ℝ) (dec : Ω → Unit × O → Bool → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : 2 * sideSuccess ρ W enc dec ≤ ∑ o, c o
~~~

### 424. refute_threshold

Source: ControlStack/SafetyCaseSC01.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refute_threshold : (2 : ℝ) * (5551 / 10000) > 65536 / 59049
~~~

### 425. sc01_case

Source: ControlStack/SafetyCaseSC01.lean:95 | Family: F2 | Adversary: SIDE_OBSERVING | Status: PROVED_RECORDED

~~~lean
theorem sc01_case : (∀ {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ), (∀ s o, W s o ≤ c o) → (∀ o, 0 ≤ c o) → ∑ o, c o ≤ 65536 / 59049 → ∀ (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ) (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ), IsDist ρ → (∀ ω m, IsDist (enc ω m)) → (∀ ω y, IsDist (dec ω y)) → sideSuccess ρ W enc dec ≤ 1 / 2 ^ 16) ∧ (∀ p : ℝ, 0 ≤ p → p ≤ 9 / 10 → passProb p ≤ 1 / 80) ∧ (tail 64 (93382 / 100000) ≤ 1 / 80 ∧ (9 : ℝ) / 10 ≤ 93382 / 100000) ∧ (viewSpace (C
~~~

## ControlStack/ScenarioACore.lean

### 426. card_epPrefix

Source: ControlStack/ScenarioACore.lean:55 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem card_epPrefix : Fintype.card EpPrefix = 9
~~~

### 427. epView_card

Source: ControlStack/ScenarioACore.lean:60 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem epView_card : Fintype.card EpView = 9
~~~

### 428. prefixToView_viewToPrefix

Source: ControlStack/ScenarioACore.lean:71 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma prefixToView_viewToPrefix (o : ScenarioARepair.View) : prefixToView (viewToPrefix o) = o
~~~

### 429. viewToPrefix_prefixToView

Source: ControlStack/ScenarioACore.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma viewToPrefix_prefixToView (p : EpPrefix) : viewToPrefix (prefixToView p) = p
~~~

### 430. prefixEquiv_apply

Source: ControlStack/ScenarioACore.lean:99 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prefixEquiv_apply (p : EpPrefix) : prefixEquiv p = embedAll p 0 0
~~~

### 431. epView_ext

Source: ControlStack/ScenarioACore.lean:102 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma epView_ext (v w : EpView) (h : v 0 0 = w 0 0) : v = w
~~~

### 432. embedAll_viewToPrefix

Source: ControlStack/ScenarioACore.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem embedAll_viewToPrefix (v : EpView) : embedAll (prefixEquiv.symm (v 0 0)) = v
~~~

### 433. embedAll_surjective

Source: ControlStack/ScenarioACore.lean:114 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem embedAll_surjective : Function.Surjective (embedAll (C
~~~

### 434. embedAll_injective

Source: ControlStack/ScenarioACore.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem embedAll_injective : Function.Injective (embedAll (C
~~~

### 435. reachable_eq_univ

Source: ControlStack/ScenarioACore.lean:124 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reachable_eq_univ : Set.range (embedAll (C
~~~

### 436. delivered_view_coord

Source: ControlStack/ScenarioACore.lean:130 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem delivered_view_coord {R : Type} (valid : (c : Fin 1) → R → Option (Fin 8)) (tr : List (Ev 1 R)) : finalView (runG valid (init (S
~~~

### 437. card_five_prefixes

Source: ControlStack/ScenarioACore.lean:140 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem card_five_prefixes : Fintype.card (Fin 5 → EpPrefix) = 59049
~~~

### 438. lifetime_bound_prefixes

Source: ControlStack/ScenarioACore.lean:145 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lifetime_bound_prefixes {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → (Fin 5 → EpPrefix) → ℝ) (dec : Ω → (Fin 5 → EpPrefix) → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (59049 : ℝ) / 2 ^ 32 ∧ (59049 : ℝ) / 2 ^ 32 ≤ 1 / 2 ^ 16
~~~

### 439. five_episode_core_bound

Source: ControlStack/ScenarioACore.lean:163 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem five_episode_core_bound {Ω R : Type} [Fintype Ω] [Fintype R] [Fintype (Ev 1 R)] (valid : (c : Fin 1) → R → Option (Fin 8)) (L : ℕ) (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → (Fin 5 → Fin L → Ev 1 R) → ℝ) (dec : Ω → (Fin 5 → EpView) → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc (fun ω tr m => dec ω (lifetimeView valid tr) m) ≤ (59049 : ℝ) / 2 ^ 32 ∧ (59049 : ℝ) / 2 ^ 32 ≤ 1 / 2 ^ 16
~~~

### 440. card_varObs

Source: ControlStack/ScenarioACore.lean:202 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem card_varObs : Fintype.card VarObs = 66430
~~~

### 441. varObs_gt

Source: ControlStack/ScenarioACore.lean:208 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem varObs_gt : (2 : ℕ) ^ 16 < 66430
~~~

### 442. varObsEmbed_injective

Source: ControlStack/ScenarioACore.lean:216 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem varObsEmbed_injective : Function.Injective varObsEmbed
~~~

### 443. attainEnc_dist

Source: ControlStack/ScenarioACore.lean:230 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma attainEnc_dist {M V : Type} [Fintype V] [DecidableEq M] [DecidableEq V] [Nonempty V] (e : V → M) (he : Function.Injective e) (m : M) : IsDist (attainEnc e () m)
~~~

### 444. attainDec_dist

Source: ControlStack/ScenarioACore.lean:244 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma attainDec_dist {M V : Type} [Fintype M] [DecidableEq M] (e : V → M) (v : V) : IsDist (attainDec e () v)
~~~

### 445. varObs_attain

Source: ControlStack/ScenarioACore.lean:252 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem varObs_attain : (∀ m, IsDist (attainEnc varObsEmbed () m)) ∧ (∀ v, IsDist (attainDec varObsEmbed () v)) ∧ successProb (Ω
~~~

### 446. varObs_breaks_target

Source: ControlStack/ScenarioACore.lean:265 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem varObs_breaks_target : ∃ (enc : Unit → Fin (2 ^ 32) → VarObs → ℝ) (dec : Unit → VarObs → Fin (2 ^ 32) → ℝ), IsDist (fun _ : Unit => (1 : ℝ)) ∧ (∀ ω m, IsDist (enc ω m)) ∧ (∀ ω v, IsDist (dec ω v)) ∧ (1 : ℝ) / 2 ^ 16 < successProb (fun _ => 1) enc dec
~~~

## ControlStack/ScenarioARepair.lean

### 447. transcript_card

Source: ControlStack/ScenarioARepair.lean:11 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem transcript_card : Fintype.card Transcript = 59049
~~~

### 448. repair_recovery

Source: ControlStack/ScenarioARepair.lean:14 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_recovery {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → Transcript → ℝ) (dec : Ω → Transcript → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ (59049 : ℝ) / 2 ^ 32
~~~

### 449. repair_target

Source: ControlStack/ScenarioARepair.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_target {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → Transcript → ℝ) (dec : Ω → Transcript → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) : successProb ρ enc dec ≤ 1 / 2 ^ 16
~~~

## ControlStack/ScenarioASide.lean

### 450. repair_side

Source: ControlStack/ScenarioASide.lean:18 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_side {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ) (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ W enc dec ≤ 59049 * (∑ o, c o) / 2 ^ 32
~~~

### 451. repair_side_target

Source: ControlStack/ScenarioASide.lean:27 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_side_target {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (hL : ∑ o, c o ≤ 65536 / 59049) (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ) (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ W enc dec ≤ 1 / 2 ^ 16
~~~

### 452. card_obs

Source: ControlStack/ScenarioASide.lean:41 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma card_obs : Fintype.card (Transcript × Bool) ≤ 2 ^ 32
~~~

### 453. emb_inj

Source: ControlStack/ScenarioASide.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma emb_inj : Function.Injective emb
~~~

### 454. repair_one_bit_attained

Source: ControlStack/ScenarioASide.lean:56 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem repair_one_bit_attained : ∃ (enc : Unit → Fin (2 ^ 32) → Transcript × Bool → ℝ) (dec : Unit → Transcript × Bool → Fin (2 ^ 32) → ℝ), (∀ ω m, IsDist (enc ω m)) ∧ (∀ ω y, IsDist (dec ω y)) ∧ sideSuccess (fun _ => (1 : ℝ)) idKernel enc dec = 2 * 59049 / 2 ^ 32 ∧ (1 : ℝ) / 2 ^ 16 < 2 * 59049 / 2 ^ 32
~~~

### 455. bsc_lifetime_ok

Source: ControlStack/ScenarioASide.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bsc_lifetime_ok : (2 * (1 - (49 : ℝ) / 100)) ^ 5 ≤ 65536 / 59049
~~~

### 456. bsc_lifetime_fails

Source: ControlStack/ScenarioASide.lean:94 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bsc_lifetime_fails : (65536 : ℝ) / 59049 < (2 * (1 - (48 : ℝ) / 100)) ^ 5
~~~

## ControlStack/ScenarioAUsefulness.lean

### 457. passProb_eq

Source: ControlStack/ScenarioAUsefulness.lean:28 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma passProb_eq (p : ℝ) : passProb p = 64 * p ^ 63 - 63 * p ^ 64
~~~

### 458. passProb_mono

Source: ControlStack/ScenarioAUsefulness.lean:34 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma passProb_mono : MonotoneOn passProb (Set.Icc 0 1)
~~~

### 459. false_pass_le

Source: ControlStack/ScenarioAUsefulness.lean:55 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem false_pass_le (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 9 / 10) : passProb p ≤ 1 / 80
~~~

### 460. endpoint64

Source: ControlStack/ScenarioAUsefulness.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem endpoint64 : tail 64 (93382 / 100000) ≤ 1 / 80 ∧ 1 / 80 < tail 64 (93383 / 100000)
~~~

### 461. endpoint63

Source: ControlStack/ScenarioAUsefulness.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem endpoint63 : tail 63 (90438 / 100000) ≤ 1 / 80 ∧ 1 / 80 < tail 63 (90439 / 100000)
~~~

### 462. reject62

Source: ControlStack/ScenarioAUsefulness.lean:69 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reject62 : 1 / 80 < tail 62 (9 / 10)
~~~

### 463. endpoints_clear_floor

Source: ControlStack/ScenarioAUsefulness.lean:75 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem endpoints_clear_floor : (9 : ℝ) / 10 ≤ 90438 / 100000 ∧ (90438 : ℝ) / 100000 ≤ 93382 / 100000
~~~

## ControlStack/Scenarios/SC08Exec.lean

### 464. run_cons

Source: ControlStack/Scenarios/SC08Exec.lean:103 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 465. sound_full

Source: ControlStack/Scenarios/SC08Exec.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sound_full : Sound full
~~~

### 466. execResult_ok

Source: ControlStack/Scenarios/SC08Exec.lean:121 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem execResult_ok (E : Env) {C : Checks} (hC : Sound C) (s : St) (p : ℕ) (sc : Option ℕ) (r : ℕ × Option ℕ) (h : execResult E C s p sc = some r) : RunOk E r
~~~

### 467. step_good

Source: ControlStack/Scenarios/SC08Exec.lean:139 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_good (E : Env) {C : Checks} (hC : Sound C) (s : St) (o : Op) (h : Good E s) : Good E (step E C s o)
~~~

### 468. run_good

Source: ControlStack/Scenarios/SC08Exec.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_good (E : Env) {C : Checks} (hC : Sound C) (s : St) (ops : List Op) (h : Good E s) : Good E (run E C s ops)
~~~

### 469. safe_of_sound

Source: ControlStack/Scenarios/SC08Exec.lean:164 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem safe_of_sound (E : Env) {C : Checks} (hC : Sound C) (files : List (ℕ × ℕ)) (ops : List Op) : Good E (run E C ⟨files, [], false⟩ ops)
~~~

### 470. sc08_safe

Source: ControlStack/Scenarios/SC08Exec.lean:168 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc08_safe (E : Env) (files : List (ℕ × ℕ)) (ops : List Op) : Good E (run E full ⟨files, [], false⟩ ops)
~~~

### 471. digest_design_needs_no_noexec

Source: ControlStack/Scenarios/SC08Exec.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem digest_design_needs_no_noexec (E : Env) (files : List (ℕ × ℕ)) (ops : List Op) : Good E (run E { full with noexec
~~~

### 472. step_halted

Source: ControlStack/Scenarios/SC08Exec.lean:178 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s
~~~

### 473. halt_freezes

Source: ControlStack/Scenarios/SC08Exec.lean:188 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
~~~

### 474. ran_prefix

Source: ControlStack/Scenarios/SC08Exec.lean:195 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ran_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.ran <+: (step E C s o).ran
~~~

### 475. honest_execs

Source: ControlStack/Scenarios/SC08Exec.lean:236 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_execs : (run E0 full s0 [.exec 1 none, .exec 4 (some 5)]).ran = [(10, none), (20, some 30)]
~~~

### 476. path_allowlist_toctou_breaks

Source: ControlStack/Scenarios/SC08Exec.lean:241 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem path_allowlist_toctou_breaks : (run E0 { full with byDigest
~~~

### 477. writable_exec_mount_breaks

Source: ControlStack/Scenarios/SC08Exec.lean:247 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem writable_exec_mount_breaks : (run E0 { full with byDigest
~~~

### 478. interpreter_loophole_breaks

Source: ControlStack/Scenarios/SC08Exec.lean:254 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem interpreter_loophole_breaks : (run E0 { full with scriptCheck
~~~

### 479. interpreter_repl_breaks

Source: ControlStack/Scenarios/SC08Exec.lean:260 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem interpreter_repl_breaks : (run E0 { full with scriptCheck
~~~

### 480. no_halt_check_breaks

Source: ControlStack/Scenarios/SC08Exec.lean:266 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run E0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC09Priv.lean

### 481. run_cons

Source: ControlStack/Scenarios/SC09Priv.lean:145 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (P : Policy) (C : Checks) (s : St) (o : Op) (ops : List Op) : run P C s (o :: ops) = run P C (step P C s o) ops
~~~

### 482. good_init

Source: ControlStack/Scenarios/SC09Priv.lean:158 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem good_init (P : Policy) : Good P init
~~~

### 483. procOf_mem

Source: ControlStack/Scenarios/SC09Priv.lean:160 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem procOf_mem {s : St} {pid : ℕ} {q : Proc} (h : procOf s pid = some q) : q ∈ s.procs
~~~

### 484. UseOk.mono

Source: ControlStack/Scenarios/SC09Priv.lean:163 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem UseOk.mono {P : Policy} {s t : St} (hg : s.granted ⊆ t.granted) {u : Use} (h : UseOk P s u) : UseOk P t u
~~~

### 485. use_append

Source: ControlStack/Scenarios/SC09Priv.lean:166 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem use_append {P : Policy} {s : St} (h : Good P s) (u : Use) (hu : UseOk P s u) : Good P { s with used
~~~

### 486. step_good

Source: ControlStack/Scenarios/SC09Priv.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_good (P : Policy) (s : St) (o : Op) (h : Good P s) : Good P (step P full s o)
~~~

### 487. run_good

Source: ControlStack/Scenarios/SC09Priv.lean:253 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_good (P : Policy) (s : St) (ops : List Op) (h : Good P s) : Good P (run P full s ops)
~~~

### 488. sc09_safe

Source: ControlStack/Scenarios/SC09Priv.lean:261 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc09_safe (P : Policy) (ops : List Op) : Good P (run P full init ops)
~~~

### 489. spawn_attenuates

Source: ControlStack/Scenarios/SC09Priv.lean:264 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem spawn_attenuates (P : Policy) (s : St) (p ch : ℕ) (keep : List ℕ) (q : Proc) (hh : s.halted = false) (hp : procOf s p = some q) (hc : procOf s ch = none) : ∀ r ∈ (step P full s (.spawn p ch keep)).procs, r ∉ s.procs → r.lin = q.lin ∧ r.caps ⊆ q.caps
~~~

### 490. step_halted

Source: ControlStack/Scenarios/SC09Priv.lean:276 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (P : Policy) (s : St) (o : Op) (hh : s.halted = true) : step P full s o = s
~~~

### 491. halt_freezes

Source: ControlStack/Scenarios/SC09Priv.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (P : Policy) (s : St) (ops : List Op) (hh : s.halted = true) : run P full s ops = s
~~~

### 492. used_prefix

Source: ControlStack/Scenarios/SC09Priv.lean:293 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem used_prefix (P : Policy) (C : Checks) (s : St) (o : Op) : s.used <+: (step P C s o).used
~~~

### 493. honest_privileged_work

Source: ControlStack/Scenarios/SC09Priv.lean:332 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_privileged_work : (run P0 full init [.start 9 1 1, .grant 9 1 1 7, .use 1 7, .elevate 1 50 3, .spawn 1 2 [7], .use 2 7]).used = [⟨1, 7, none⟩, ⟨1, 8, some (50, 3)⟩, ⟨1, 7, none⟩]
~~~

### 494. unrestricted_elevation_breaks

Source: ControlStack/Scenarios/SC09Priv.lean:338 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unrestricted_elevation_breaks : (run P0 { full with exactArgs
~~~

### 495. exec_without_attenuation_breaks

Source: ControlStack/Scenarios/SC09Priv.lean:344 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exec_without_attenuation_breaks : (run P0 { full with attenuate
~~~

### 496. confused_deputy_breaks

Source: ControlStack/Scenarios/SC09Priv.lean:350 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem confused_deputy_breaks : (run P0 { full with deputyCheck
~~~

### 497. no_halt_check_breaks

Source: ControlStack/Scenarios/SC09Priv.lean:356 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run P0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC10Policy.lean

### 498. run_cons

Source: ControlStack/Scenarios/SC10Policy.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 499. inv_init

Source: ControlStack/Scenarios/SC10Policy.lean:136 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) : Inv E init
~~~

### 500. DecOk.mono

Source: ControlStack/Scenarios/SC10Policy.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem DecOk.mono {E : Env} {s t : St} (hp : s.versions <+: t.versions) {d : Dec} (h : DecOk E s d) : DecOk E t d
~~~

### 501. inv_same

Source: ControlStack/Scenarios/SC10Policy.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_same {E : Env} {s t : St} (h : Inv E s) (hv : t.versions = s.versions) (hd : t.decisions = s.decisions) (hb : t.builds = s.builds) : Inv E t
~~~

### 502. step_inv

Source: ControlStack/Scenarios/SC10Policy.lean:154 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o)
~~~

### 503. run_inv

Source: ControlStack/Scenarios/SC10Policy.lean:203 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 504. sc10_safe

Source: ControlStack/Scenarios/SC10Policy.lean:212 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc10_safe (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (ops : List Op) : Good E (run E full init ops)
~~~

### 505. policy_admin_only

Source: ControlStack/Scenarios/SC10Policy.lean:217 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem policy_admin_only (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (ops : List Op) : ∀ pv ∈ (run E full init ops).versions, pv.2 ∈ E.admins
~~~

### 506. step_halted

Source: ControlStack/Scenarios/SC10Policy.lean:223 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s
~~~

### 507. halt_freezes

Source: ControlStack/Scenarios/SC10Policy.lean:233 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
~~~

### 508. decisions_prefix

Source: ControlStack/Scenarios/SC10Policy.lean:240 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem decisions_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.decisions <+: (step E C s o).decisions
~~~

### 509. honest_enforcement_and_build

Source: ControlStack/Scenarios/SC10Policy.lean:273 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_enforcement_and_build : let s
~~~

### 510. agent_writable_policy_breaks

Source: ControlStack/Scenarios/SC10Policy.lean:279 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_writable_policy_breaks : let s
~~~

### 511. stale_cache_breaks

Source: ControlStack/Scenarios/SC10Policy.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stale_cache_breaks : (run E0 { full with fresh
~~~

### 512. alternate_evaluator_breaks

Source: ControlStack/Scenarios/SC10Policy.lean:293 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem alternate_evaluator_breaks : (run E0 { full with singleEval
~~~

### 513. path_toolchain_breaks

Source: ControlStack/Scenarios/SC10Policy.lean:300 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem path_toolchain_breaks : (run E0 { full with pinnedPath
~~~

### 514. no_halt_check_breaks

Source: ControlStack/Scenarios/SC10Policy.lean:306 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run E0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC12Persistence.lean

### 515. run_cons

Source: ControlStack/Scenarios/SC12Persistence.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (admins : List ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) : run admins C s (o :: ops) = run admins C (step admins C s o) ops
~~~

### 516. inv_init

Source: ControlStack/Scenarios/SC12Persistence.lean:134 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init : Inv init
~~~

### 517. Inv.good

Source: ControlStack/Scenarios/SC12Persistence.lean:136 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {s : St} (h : Inv s) : Good s
~~~

### 518. fireOk_mono

Source: ControlStack/Scenarios/SC12Persistence.lean:140 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fireOk_mono {s t : St} (hp : s.ended <+: t.ended) (f : ℕ × ℕ × ℕ) (h : FireOk s f) : FireOk t f
~~~

### 519. entOf_mem

Source: ControlStack/Scenarios/SC12Persistence.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem entOf_mem {s : St} {id : ℕ} {e : Ent} (h : entOf s id = some e) : e ∈ s.live
~~~

### 520. step_inv

Source: ControlStack/Scenarios/SC12Persistence.lean:148 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (admins : List ℕ) (s : St) (o : Op) (h : Inv s) : Inv (step admins full s o)
~~~

### 521. run_inv

Source: ControlStack/Scenarios/SC12Persistence.lean:224 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (admins : List ℕ) (s : St) (ops : List Op) (h : Inv s) : Inv (run admins full s ops)
~~~

### 522. sc12_safe

Source: ControlStack/Scenarios/SC12Persistence.lean:231 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc12_safe (admins : List ℕ) (ops : List Op) : Good (run admins full init ops)
~~~

### 523. step_ended

Source: ControlStack/Scenarios/SC12Persistence.lean:234 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_ended (admins : List ℕ) (s : St) (o : Op) (h : Inv s) (sess : ℕ) (hs : sess ∈ s.ended) : sess ∈ (step admins full s o).ended ∧ (step admins full s o).fired.filter (fun f => f.2.1 = sess) = s.fired.filter (fun f => f.2.1 = sess)
~~~

### 524. no_fire_after_end

Source: ControlStack/Scenarios/SC12Persistence.lean:264 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_fire_after_end (admins : List ℕ) (s : St) (ops : List Op) (h : Inv s) (sess : ℕ) (hs : sess ∈ s.ended) : (run admins full s ops).fired.filter (fun f => f.2.1 = sess) = s.fired.filter (fun f => f.2.1 = sess)
~~~

### 525. step_halted

Source: ControlStack/Scenarios/SC12Persistence.lean:275 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (admins : List ℕ) (s : St) (o : Op) (hh : s.halted = true) : step admins full s o = s
~~~

### 526. halt_freezes

Source: ControlStack/Scenarios/SC12Persistence.lean:279 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (admins : List ℕ) (s : St) (ops : List Op) (hh : s.halted = true) : run admins full s ops = s
~~~

### 527. fired_prefix

Source: ControlStack/Scenarios/SC12Persistence.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fired_prefix (admins : List ℕ) (C : Checks) (s : St) (o : Op) : s.fired <+: (step admins C s o).fired
~~~

### 528. honest_session_lifecycle

Source: ControlStack/Scenarios/SC12Persistence.lean:315 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_session_lifecycle : let s
~~~

### 529. registry_bypass_survives

Source: ControlStack/Scenarios/SC12Persistence.lean:321 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem registry_bypass_survives : (run [9] { full with registryOnly
~~~

### 530. parent_only_revocation_survives

Source: ControlStack/Scenarios/SC12Persistence.lean:328 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem parent_only_revocation_survives : (run [9] { full with revokeLineage
~~~

### 531. foreign_registration_survives

Source: ControlStack/Scenarios/SC12Persistence.lean:335 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foreign_registration_survives : (run [9] { full with lineage
~~~

### 532. no_halt_check_breaks

Source: ControlStack/Scenarios/SC12Persistence.lean:342 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run [9] { full with haltCheck
~~~

## ControlStack/Scenarios/SC16Deploy.lean

### 533. run_cons

Source: ControlStack/Scenarios/SC16Deploy.lean:147 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (R : Roles) (h : ℕ → ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) : run R h C s (o :: ops) = run R h C (step R h C s o) ops
~~~

### 534. inv_init

Source: ControlStack/Scenarios/SC16Deploy.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (R : Roles) (h : ℕ → ℕ) : Inv R h init
~~~

### 535. Inv.good

Source: ControlStack/Scenarios/SC16Deploy.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {R : Roles} {h : ℕ → ℕ} {s : St} (hi : Inv R h s) : Good R h s
~~~

### 536. apprOf_mem

Source: ControlStack/Scenarios/SC16Deploy.lean:178 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem apprOf_mem {s : St} {n : ℕ} {ap : Appr} (h : apprOf s n = some ap) : ap ∈ s.approvals ∧ ap.n = n
~~~

### 537. inv_of_mono

Source: ControlStack/Scenarios/SC16Deploy.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_of_mono {R : Roles} {h : ℕ → ℕ} {s t : St} (hi : Inv R h s) (hrev : s.reviews ⊆ t.reviews) (happ : s.approvals ⊆ t.approvals) (hrevn : ∀ rv ∈ t.reviews, rv ∉ s.reviews → ReviewOk R h rv) (happn : ∀ ap ∈ t.approvals, ap ∉ s.approvals → ap.approver ∈ R.approvers) (hdep : t.deployed = s.deployed) (hused : t.used = s.used) : Inv R h t
~~~

### 538. doDeploy_inv

Source: ControlStack/Scenarios/SC16Deploy.lean:198 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem doDeploy_inv {R : Roles} {h : ℕ → ℕ} {s : St} (hi : Inv R h s) (n t x : ℕ) (ap : Appr) (hap : apprOf s n = some ap) (hrv : ∃ rv ∈ s.reviews, rv.d = ap.d) (hn : n ∉ s.used) (ht : t = ap.target) (hx : h x = ap.d) : Inv R h (doDeploy s n t x)
~~~

### 539. step_inv

Source: ControlStack/Scenarios/SC16Deploy.lean:218 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (R : Roles) (h : ℕ → ℕ) (s : St) (o : Op) (hi : Inv R h s) : Inv R h (step R h full s o)
~~~

### 540. run_inv

Source: ControlStack/Scenarios/SC16Deploy.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op) (hi : Inv R h s) : Inv R h (run R h full s ops)
~~~

### 541. sc16_safe

Source: ControlStack/Scenarios/SC16Deploy.lean:294 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc16_safe (R : Roles) (h : ℕ → ℕ) (ops : List Op) : Good R h (run R h full init ops)
~~~

### 542. sc16_reviewed_content

Source: ControlStack/Scenarios/SC16Deploy.lean:299 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc16_reviewed_content (R : Roles) (h : ℕ → ℕ) (ops : List Op) (hinj : Set.InjOn h {c | (∃ e ∈ (run R h full init ops).deployed, e.content = c) ∨ ∃ rv ∈ (run R h full init ops).reviews, rv.content = c}) : ∀ e ∈ (run R h full init ops).deployed, ∃ rv ∈ (run R h full init ops).reviews, rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager
~~~

### 543. step_halted

Source: ControlStack/Scenarios/SC16Deploy.lean:310 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (R : Roles) (h : ℕ → ℕ) (s : St) (o : Op) (hh : s.halted = true) : step R h full s o = s
~~~

### 544. halt_freezes

Source: ControlStack/Scenarios/SC16Deploy.lean:321 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op) (hh : s.halted = true) : run R h full s ops = s
~~~

### 545. deployed_prefix

Source: ControlStack/Scenarios/SC16Deploy.lean:329 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem deployed_prefix (R : Roles) (h : ℕ → ℕ) (C : Checks) (s : St) (o : Op) : s.deployed <+: (step R h C s o).deployed
~~~

### 546. honest_trace_deploys

Source: ControlStack/Scenarios/SC16Deploy.lean:363 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_trace_deploys : (run R0 id full init [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]).deployed = [⟨0, 5, 7⟩]
~~~

### 547. toctou_slot_breaks

Source: ControlStack/Scenarios/SC16Deploy.lean:369 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem toctou_slot_breaks : let s
~~~

### 548. verify_blocks_toctou

Source: ControlStack/Scenarios/SC16Deploy.lean:376 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem verify_blocks_toctou : (run R0 id full init [.stage 1 7, .writeSlot 1 0 7, .review 2 7, .approve 3 0 7 5 0, .writeSlot 1 0 666, .deploy 1 0 5 666]).deployed = []
~~~

### 549. collision_breaks

Source: ControlStack/Scenarios/SC16Deploy.lean:384 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem collision_breaks : let s
~~~

### 550. no_target_binding_breaks

Source: ControlStack/Scenarios/SC16Deploy.lean:390 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_target_binding_breaks : let s
~~~

### 551. self_review_without_distinct_check

Source: ControlStack/Scenarios/SC16Deploy.lean:399 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem self_review_without_distinct_check : let s
~~~

### 552. distinct_blocks_self_review

Source: ControlStack/Scenarios/SC16Deploy.lean:406 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem distinct_blocks_self_review : (run R1 id full init [.stage 1 7, .review 1 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]).deployed = []
~~~

### 553. no_nonce_redeploys

Source: ControlStack/Scenarios/SC16Deploy.lean:411 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_nonce_redeploys : (run R0 id { full with nonce
~~~

### 554. no_halt_check_breaks

Source: ControlStack/Scenarios/SC16Deploy.lean:418 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run R0 id { full with haltCheck
~~~

## ControlStack/Scenarios/SC17Infra.lean

### 555. run_cons

Source: ControlStack/Scenarios/SC17Infra.lean:154 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 556. inv_init

Source: ControlStack/Scenarios/SC17Infra.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) (g0 : List G) : Inv E (init g0)
~~~

### 557. Inv.good

Source: ControlStack/Scenarios/SC17Infra.lean:176 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {E : Env} {s : St} (h : Inv E s) : Good E s
~~~

### 558. propOf_spec

Source: ControlStack/Scenarios/SC17Infra.lean:182 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem propOf_spec {s : St} {id : ℕ} {p : Pr} (h : propOf s id = some p) : p ∈ s.props ∧ p.id = id
~~~

### 559. inv_same

Source: ControlStack/Scenarios/SC17Infra.lean:186 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_same {E : Env} {s t : St} (h : Inv E s) (ha : t.approvals = s.approvals) (hp : t.applied = s.applied) (hd : t.done = s.done) : Inv E t
~~~

### 560. step_inv

Source: ControlStack/Scenarios/SC17Infra.lean:190 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o)
~~~

### 561. run_inv

Source: ControlStack/Scenarios/SC17Infra.lean:238 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 562. sc17_safe

Source: ControlStack/Scenarios/SC17Infra.lean:246 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc17_safe (E : Env) (g0 : List G) (ops : List Op) : Good E (run E full (init g0) ops)
~~~

### 563. reconcile_restores

Source: ControlStack/Scenarios/SC17Infra.lean:250 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reconcile_restores (E : Env) (s : St) (hh : s.halted = false) : (step E full s .reconcile).live = (step E full s .reconcile).desired
~~~

### 564. step_halted

Source: ControlStack/Scenarios/SC17Infra.lean:259 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : (step E full s o).applied = s.applied ∧ (step E full s o).halted = true
~~~

### 565. halt_freezes

Source: ControlStack/Scenarios/SC17Infra.lean:267 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : (run E full s ops).applied = s.applied
~~~

### 566. applied_prefix

Source: ControlStack/Scenarios/SC17Infra.lean:278 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem applied_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.applied <+: (step E C s o).applied
~~~

### 567. honest_apply

Source: ControlStack/Scenarios/SC17Infra.lean:312 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_apply : (run E0 full (init []) [.propose 1 0 dA, .approve 2 0, .apply 0]).live = [(1, 1, 1)]
~~~

### 568. text_ceiling_composition_breaks

Source: ControlStack/Scenarios/SC17Infra.lean:318 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem text_ceiling_composition_breaks : (E0.allowed (run E0 { full with resultCheck
~~~

### 569. approve_then_amend_breaks

Source: ControlStack/Scenarios/SC17Infra.lean:326 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem approve_then_amend_breaks : let s
~~~

### 570. no_drift_detection_breaks

Source: ControlStack/Scenarios/SC17Infra.lean:333 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_drift_detection_breaks : let s
~~~

### 571. no_halt_check_breaks

Source: ControlStack/Scenarios/SC17Infra.lean:340 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run E0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC18Logging.lean

### 572. run_cons

Source: ControlStack/Scenarios/SC18Logging.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (admins : List ℕ) (trusted T : ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) : run admins trusted T C s (o :: ops) = run admins trusted T C (step admins trusted T C s o) ops
~~~

### 573. inv_init

Source: ControlStack/Scenarios/SC18Logging.lean:133 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (trusted T : ℕ) : Inv trusted T (init trusted)
~~~

### 574. RelOk.mono

Source: ControlStack/Scenarios/SC18Logging.lean:136 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem RelOk.mono {T : ℕ} {s t : St} (hp : s.logged <+: t.logged) {r : Rel} (h : RelOk T s r) : RelOk T t r
~~~

### 575. step_inv

Source: ControlStack/Scenarios/SC18Logging.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (admins : List ℕ) (trusted T : ℕ) (s : St) (o : Op) (ho : legal admins trusted o) (h : Inv trusted T s) : Inv trusted T (step admins trusted T full s o)
~~~

### 576. run_inv

Source: ControlStack/Scenarios/SC18Logging.lean:207 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (admins : List ℕ) (trusted T : ℕ) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal admins trusted o) (h : Inv trusted T s) : Inv trusted T (run admins trusted T full s ops)
~~~

### 577. sc18_safe

Source: ControlStack/Scenarios/SC18Logging.lean:219 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc18_safe (admins : List ℕ) (trusted T : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal admins trusted o) : Good T (run admins trusted T full (init trusted) ops)
~~~

### 578. config_untampered

Source: ControlStack/Scenarios/SC18Logging.lean:225 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem config_untampered (admins : List ℕ) (trusted T : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal admins trusted o) : (run admins trusted T full (init trusted) ops).cfg = trusted
~~~

### 579. step_halted

Source: ControlStack/Scenarios/SC18Logging.lean:231 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (admins : List ℕ) (trusted T : ℕ) (s : St) (o : Op) (hh : s.halted = true) : (step admins trusted T full s o).released = s.released ∧ (step admins trusted T full s o).halted = true
~~~

### 580. halt_freezes

Source: ControlStack/Scenarios/SC18Logging.lean:240 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (admins : List ℕ) (trusted T : ℕ) (s : St) (ops : List Op) (hh : s.halted = true) : (run admins trusted T full s ops).released = s.released
~~~

### 581. released_prefix

Source: ControlStack/Scenarios/SC18Logging.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem released_prefix (admins : List ℕ) (trusted T : ℕ) (C : Checks) (s : St) (o : Op) : s.released <+: (step admins trusted T C s o).released
~~~

### 582. honest_logged_release

Source: ControlStack/Scenarios/SC18Logging.lean:283 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_logged_release : let s
~~~

### 583. release_before_log_breaks

Source: ControlStack/Scenarios/SC18Logging.lean:289 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem release_before_log_breaks : let s
~~~

### 584. agent_writable_config_breaks

Source: ControlStack/Scenarios/SC18Logging.lean:297 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_writable_config_breaks : let s
~~~

### 585. fail_open_outage_breaks

Source: ControlStack/Scenarios/SC18Logging.lean:304 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fail_open_outage_breaks : (run [9] 0 2 { full with failOpen
~~~

### 586. watchdog_off_silent_release

Source: ControlStack/Scenarios/SC18Logging.lean:312 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem watchdog_off_silent_release : (run [9] 0 2 { full with watchdog
~~~

### 587. no_halt_check_breaks

Source: ControlStack/Scenarios/SC18Logging.lean:319 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run [9] 0 2 { full with haltCheck
~~~

## ControlStack/Scenarios/SC19Prod.lean

### 588. run_cons

Source: ControlStack/Scenarios/SC19Prod.lean:141 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 589. inv_init

Source: ControlStack/Scenarios/SC19Prod.lean:159 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) : Inv E init
~~~

### 590. Inv.good

Source: ControlStack/Scenarios/SC19Prod.lean:161 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {E : Env} {s : St} (h : Inv E s) : Good E s
~~~

### 591. inv_mono

Source: ControlStack/Scenarios/SC19Prod.lean:168 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_mono {E : Env} {s t : St} (h : Inv E s) (hs : s.snaps <+: t.snaps) (hv : s.verified ⊆ t.verified) (ha : s.approvals ⊆ t.approvals) (han : ∀ a ∈ t.approvals, a ∉ s.approvals → a.2.1 ∈ E.approvers ∧ a.2.1 ≠ a.2.2) (hd : t.destroyed = s.destroyed) (hdn : t.done = s.done) : Inv E t
~~~

### 592. inv_same

Source: ControlStack/Scenarios/SC19Prod.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_same {E : Env} {s t : St} (h : Inv E s) (hs : t.snaps = s.snaps) (hv : t.verified = s.verified) (ha : t.approvals = s.approvals) (hd : t.destroyed = s.destroyed) (hdn : t.done = s.done) : Inv E t
~~~

### 593. step_inv

Source: ControlStack/Scenarios/SC19Prod.lean:191 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o)
~~~

### 594. run_inv

Source: ControlStack/Scenarios/SC19Prod.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 595. sc19_safe

Source: ControlStack/Scenarios/SC19Prod.lean:259 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc19_safe (E : Env) (ops : List Op) : Good E (run E full init ops)
~~~

### 596. step_halted

Source: ControlStack/Scenarios/SC19Prod.lean:263 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s
~~~

### 597. halt_freezes

Source: ControlStack/Scenarios/SC19Prod.lean:273 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
~~~

### 598. destroyed_prefix

Source: ControlStack/Scenarios/SC19Prod.lean:280 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem destroyed_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.destroyed <+: (step E C s o).destroyed
~~~

### 599. honest_destructive_change

Source: ControlStack/Scenarios/SC19Prod.lean:309 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_destructive_change : (run E0 full init [.write 7 5, .snapshot 7, .verify 3 0, .prepare 1 0 7, .approve 2 0, .commit 0 0]).destroyed = [⟨0, 1, 7, 1, 5, 0⟩]
~~~

### 600. stale_snapshot_breaks

Source: ControlStack/Scenarios/SC19Prod.lean:315 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stale_snapshot_breaks : let ops
~~~

### 601. unverified_snapshot_breaks

Source: ControlStack/Scenarios/SC19Prod.lean:323 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unverified_snapshot_breaks : (run E0 { full with verified
~~~

### 602. blast_radius_race_breaks

Source: ControlStack/Scenarios/SC19Prod.lean:330 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem blast_radius_race_breaks : let ops
~~~

### 603. no_halt_check_breaks

Source: ControlStack/Scenarios/SC19Prod.lean:337 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : let ops
~~~

## ControlStack/Scenarios/SC23Injection.lean

### 604. run_cons

Source: ControlStack/Scenarios/SC23Injection.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (P : Policy) (C : Checks) (s : St) (o : Op) (ops : List Op) : run P C s (o :: ops) = run P C (step P C s o) ops
~~~

### 605. inv_init

Source: ControlStack/Scenarios/SC23Injection.lean:158 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (P : Policy) : Inv P init
~~~

### 606. Inv.good

Source: ControlStack/Scenarios/SC23Injection.lean:160 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {P : Policy} {s : St} (hi : Inv P s) : Good P s
~~~

### 607. argsOf_mem

Source: ControlStack/Scenarios/SC23Injection.lean:165 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem argsOf_mem {s : St} {args : List ℕ} {x : Val} (h : x ∈ argsOf s args) : x ∈ s.store
~~~

### 608. anyLabel_eq

Source: ControlStack/Scenarios/SC23Injection.lean:169 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem anyLabel_eq {xs : List Val} (h : ∀ x ∈ xs, x.label = x.prov) : anyLabel xs = anyProv xs
~~~

### 609. inv_of_mono

Source: ControlStack/Scenarios/SC23Injection.lean:177 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_of_mono {P : Policy} {s t : St} (hi : Inv P s) (hst : ∀ x ∈ t.store, x.label = x.prov) (hc : s.confs ⊆ t.confs) (hcn : ∀ cf ∈ t.confs, cf.by_ ∈ P.users) (he : t.executed = s.executed) (hu : t.used = s.used) : Inv P t
~~~

### 610. store_append

Source: ControlStack/Scenarios/SC23Injection.lean:186 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem store_append {P : Policy} {s : St} (hi : Inv P s) (x : Val) (hx : x.label = x.prov) : Inv P { s with store
~~~

### 611. exec_free

Source: ControlStack/Scenarios/SC23Injection.lean:193 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exec_free {P : Policy} {s : St} (hi : Inv P s) (tool : ℕ) (args : List ℕ) (hc : tool ∉ P.sensitive ∨ anyLabel (argsOf s args) = false) : Inv P (doExec s ⟨tool, (argsOf s args).map Val.v, anyProv (argsOf s args), none⟩ [])
~~~

### 612. exec_conf

Source: ControlStack/Scenarios/SC23Injection.lean:214 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exec_conf {P : Policy} {s : St} (hi : Inv P s) (tool : ℕ) (args : List ℕ) (n : ℕ) (cf : Conf) (hcf : confOf s n = some cf) (ht : cf.tool = tool) (hv : cf.vals = (argsOf s args).map Val.v) (hu : n ∉ s.used) : Inv P (doExec s ⟨tool, (argsOf s args).map Val.v, anyProv (argsOf s args), some n⟩ [n])
~~~

### 613. step_inv

Source: ControlStack/Scenarios/SC23Injection.lean:236 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (P : Policy) (s : St) (o : Op) (hi : Inv P s) : Inv P (step P full s o)
~~~

### 614. run_inv

Source: ControlStack/Scenarios/SC23Injection.lean:292 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (P : Policy) (s : St) (ops : List Op) (hi : Inv P s) : Inv P (run P full s ops)
~~~

### 615. sc23_safe

Source: ControlStack/Scenarios/SC23Injection.lean:300 | Family: F1 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc23_safe (P : Policy) (ops : List Op) : Good P (run P full init ops)
~~~

### 616. step_halted

Source: ControlStack/Scenarios/SC23Injection.lean:305 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (P : Policy) (s : St) (o : Op) (hh : s.halted = true) : step P full s o = s
~~~

### 617. halt_freezes

Source: ControlStack/Scenarios/SC23Injection.lean:315 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (P : Policy) (s : St) (ops : List Op) (hh : s.halted = true) : run P full s ops = s
~~~

### 618. executed_prefix

Source: ControlStack/Scenarios/SC23Injection.lean:322 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem executed_prefix (P : Policy) (C : Checks) (s : St) (o : Op) : s.executed <+: (step P C s o).executed
~~~

### 619. honest_untainted

Source: ControlStack/Scenarios/SC23Injection.lean:351 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_untainted : (run P0 full init [.userInput 0 42, .act 5 [0] 0]).executed = [⟨5, [42], false, none⟩]
~~~

### 620. honest_confirmed

Source: ControlStack/Scenarios/SC23Injection.lean:356 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_confirmed : (run P0 full init [.toolResult 0 66, .confirm 1 7 5 [66], .act 5 [0] 7]).executed = [⟨5, [66], true, some 7⟩]
~~~

### 621. tainted_unconfirmed_blocked

Source: ControlStack/Scenarios/SC23Injection.lean:361 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tainted_unconfirmed_blocked : (run P0 full init [.toolResult 0 66, .act 5 [0] 0]).executed = []
~~~

### 622. summarizer_drops_taint

Source: ControlStack/Scenarios/SC23Injection.lean:367 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem summarizer_drops_taint : (run P0 { full with propagate
~~~

### 623. paraphrase_confirmation_breaks

Source: ControlStack/Scenarios/SC23Injection.lean:374 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem paraphrase_confirmation_breaks : let s
~~~

### 624. no_taint_check_breaks

Source: ControlStack/Scenarios/SC23Injection.lean:381 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_taint_check_breaks : (run P0 { full with taintCheck
~~~

### 625. confirmation_reuse_breaks

Source: ControlStack/Scenarios/SC23Injection.lean:387 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem confirmation_reuse_breaks : (run P0 { full with oneUse
~~~

### 626. non_user_confirmation_refused

Source: ControlStack/Scenarios/SC23Injection.lean:396 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem non_user_confirmation_refused : (run P0 full init [.toolResult 0 66, .confirm 2 7 5 [66], .act 5 [0] 7]).executed = []
~~~

## ControlStack/Scenarios/SC25Audit.lean

### 627. run_cons

Source: ControlStack/Scenarios/SC25Audit.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (C : Checks) (s : St) (o : Op) (ops : List Op) : run R h cls C s (o :: ops) = run R h cls C (step R h cls C s o) ops
~~~

### 628. inv_init

Source: ControlStack/Scenarios/SC25Audit.lean:196 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) : Inv R h cls init
~~~

### 629. Inv.good

Source: ControlStack/Scenarios/SC25Audit.lean:199 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s : St} (hi : Inv R h cls s) : Good R h cls s
~~~

### 630. take_prefix

Source: ControlStack/Scenarios/SC25Audit.lean:206 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem take_prefix {α : Type} {l m : List α} (hp : l <+: m) {n : ℕ} (hn : n ≤ l.length) : m.take n = l.take n
~~~

### 631. inv_of_mono

Source: ControlStack/Scenarios/SC25Audit.lean:211 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_of_mono {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s t : St} (hi : Inv R h cls s) (hv : s.verdicts <+: t.verdicts) (ha : s.approvals <+: t.approvals) (hvn : ∀ v ∈ t.verdicts, v ∉ s.verdicts → ∃ a, v.by_ = some a ∧ a ∈ R.auditors) (han : ∀ ap ∈ t.approvals, ap ∉ s.approvals → ap.approver ∈ R.approvers) (he : t.executed = s.executed) : Inv R h cls t
~~~

### 632. mono_same

Source: ControlStack/Scenarios/SC25Audit.lean:229 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mono_same {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s t : St} (hi : Inv R h cls s) (hv : t.verdicts = s.verdicts) (ha : t.approvals = s.approvals) (he : t.executed = s.executed) : Inv R h cls t
~~~

### 633. audit_inv

Source: ControlStack/Scenarios/SC25Audit.lean:235 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem audit_inv {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s : St} (hi : Inv R h cls s) (v : Verdict) (hv : ∃ a, v.by_ = some a ∧ a ∈ R.auditors) : Inv R h cls { s with verdicts
~~~

### 634. approve_inv

Source: ControlStack/Scenarios/SC25Audit.lean:243 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem approve_inv {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s : St} (hi : Inv R h cls s) (ap : Appr) (ha : ap.approver ∈ R.approvers) : Inv R h cls { s with approvals
~~~

### 635. itemOf_id

Source: ControlStack/Scenarios/SC25Audit.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem itemOf_id {s : St} {id : ℕ} {it : Item} (h : itemOf s id = some it) : it.id = id
~~~

### 636. fire_inv

Source: ControlStack/Scenarios/SC25Audit.lean:254 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fire_inv {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s : St} (hi : Inv R h cls s) (id : ℕ) (it : Item) (hit : itemOf s id = some it) (hn : id ∉ s.executed.map Exec.id) (hval : Valid h cls full s it) : Inv R h cls { s with executed
~~~

### 637. step_inv

Source: ControlStack/Scenarios/SC25Audit.lean:279 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) (hi : Inv R h cls s) : Inv R h cls (step R h cls full s o)
~~~

### 638. run_inv

Source: ControlStack/Scenarios/SC25Audit.lean:304 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List Op) (hi : Inv R h cls s) : Inv R h cls (run R h cls full s ops)
~~~

### 639. sc25_safe

Source: ControlStack/Scenarios/SC25Audit.lean:314 | Family: F6 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc25_safe (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) : Good R h cls (run R h cls full init ops)
~~~

### 640. step_expired

Source: ControlStack/Scenarios/SC25Audit.lean:320 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_expired (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) (id : ℕ) (hx : id ∈ s.expired) (hn : id ∉ s.executed.map Exec.id) : id ∈ (step R h cls full s o).expired ∧ id ∉ (step R h cls full s o).executed.map Exec.id
~~~

### 641. expired_never_executes

Source: ControlStack/Scenarios/SC25Audit.lean:345 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem expired_never_executes (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List Op) (id : ℕ) (hx : id ∈ s.expired) (hn : id ∉ s.executed.map Exec.id) : id ∉ (run R h cls full s ops).executed.map Exec.id
~~~

### 642. step_halted

Source: ControlStack/Scenarios/SC25Audit.lean:355 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) (hh : s.halted = true) : (step R h cls full s o).executed = s.executed ∧ (step R h cls full s o).halted = true
~~~

### 643. halt_freezes

Source: ControlStack/Scenarios/SC25Audit.lean:363 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List Op) (hh : s.halted = true) : (run R h cls full s ops).executed = s.executed
~~~

### 644. executed_prefix

Source: ControlStack/Scenarios/SC25Audit.lean:374 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem executed_prefix (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (C : Checks) (s : St) (o : Op) : s.executed <+: (step R h cls C s o).executed
~~~

### 645. honest_reversible

Source: ControlStack/Scenarios/SC25Audit.lean:407 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_reversible : ((run R0 id cls0 full init [.submit 1 0 7 false, .audit 2 0 true, .check 0, .fire 0]).executed.map Exec.content) = [7]
~~~

### 646. honest_irreversible_with_crash

Source: ControlStack/Scenarios/SC25Audit.lean:414 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_irreversible_with_crash : ((run R0 id cls0 full init [.submit 1 0 100 true, .audit 2 0 true, .approve 3 0, .check 0, .crash, .fire 0, .check 0, .fire 0, .fire 0]).executed.map Exec.content) = [100]
~~~

### 647. audit_fail_blocks

Source: ControlStack/Scenarios/SC25Audit.lean:420 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem audit_fail_blocks : (run R0 id cls0 full init [.submit 1 0 7 false, .audit 2 0 false, .check 0, .fire 0]).executed = []
~~~

### 648. fail_open_timeout_breaks

Source: ControlStack/Scenarios/SC25Audit.lean:426 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fail_open_timeout_breaks : let s
~~~

### 649. digest_unchecked_breaks

Source: ControlStack/Scenarios/SC25Audit.lean:433 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem digest_unchecked_breaks : let s
~~~

### 650. nonatomic_check_race_breaks

Source: ControlStack/Scenarios/SC25Audit.lean:441 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nonatomic_check_race_breaks : (run R0 id cls0 { full with atomic
~~~

### 651. agent_declared_class_breaks

Source: ControlStack/Scenarios/SC25Audit.lean:450 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem agent_declared_class_breaks : let s
~~~

### 652. no_halt_check_breaks

Source: ControlStack/Scenarios/SC25Audit.lean:458 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run R0 id cls0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC26Transaction.lean

### 653. sound_full

Source: ControlStack/Scenarios/SC26Transaction.lean:124 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sound_full : Sound full
~~~

### 654. reqOf_append

Source: ControlStack/Scenarios/SC26Transaction.lean:198 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reqOf_append (s : St) (l : List Req) (k : ℕ) (r : Req) (h : reqOf s k = some r) : reqOf { s with reqs
~~~

### 655. inv_init

Source: ControlStack/Scenarios/SC26Transaction.lean:203 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (R : Roles) (cap : ℕ) : Inv R cap init
~~~

### 656. Approved.mono

Source: ControlStack/Scenarios/SC26Transaction.lean:211 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Approved.mono {R : Roles} {s t : St} {k : ℕ} {r : Req} (h : Ext s t) (ha : Approved R s k r) : Approved R t k r
~~~

### 657. amt_ext

Source: ControlStack/Scenarios/SC26Transaction.lean:216 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem amt_ext {s t : St} (h : Ext s t) (k : ℕ) (hk : ∃ r, reqOf s k = some r) : amt t k = amt s k
~~~

### 658. sum_ext

Source: ControlStack/Scenarios/SC26Transaction.lean:220 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_ext {s t : St} (h : Ext s t) (l : List ℕ) (hl : ∀ k ∈ l, ∃ r, reqOf s k = some r) : (l.map (amt t)).sum = (l.map (amt s)).sum
~~~

### 659. bank_sum

Source: ControlStack/Scenarios/SC26Transaction.lean:226 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bank_sum (s : St) (hb : ∀ e ∈ s.bank, ∃ r, reqOf s e.1 = some r ∧ r.tx = e.2) : (s.bank.map (fun e => e.2.amount)).sum = ((s.bank.map Prod.fst).map (amt s)).sum
~~~

### 660. sum_le_of_subperm

Source: ControlStack/Scenarios/SC26Transaction.lean:235 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_le_of_subperm (f : ℕ → ℕ) (l₁ l₂ : List ℕ) (h : List.Subperm l₁ l₂) : (l₁.map f).sum ≤ (l₂.map f).sum
~~~

### 661. Inv.good

Source: ControlStack/Scenarios/SC26Transaction.lean:240 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {R : Roles} {cap : ℕ} {s : St} (h : Inv R cap s) : Good R cap s
~~~

### 662. inv_of_ext

Source: ControlStack/Scenarios/SC26Transaction.lean:258 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_of_ext {R : Roles} {cap : ℕ} {s t : St} (h : Inv R cap s) (he : Ext s t) (happr : ∀ ap ∈ t.approvals, ap ∉ s.approvals → ∃ r, reqOf t ap.1 = some r ∧ ap.2.2 = r.tx ∧ ap.2.1 ∈ R.approvers ∧ ap.2.1 ≠ r.requester) (hres : t.reserved = s.reserved) (hsp : t.spent = s.spent) (hbank : t.bank = s.bank) (hnet : t.net = s.net) : Inv R cap t
~~~

### 663. ext_refl

Source: ControlStack/Scenarios/SC26Transaction.lean:287 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ext_refl (s : St) : Ext s s
~~~

### 664. bankAppend_inv

Source: ControlStack/Scenarios/SC26Transaction.lean:289 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bankAppend_inv {R : Roles} {cap : ℕ} {C : Checks} (hdd : C.bankDedup = true) {s : St} (h : Inv R cap s) (k : ℕ) (r : Req) (hk : k ∈ s.reserved) (hr : reqOf s k = some r) : Inv R cap (bankAppend C s k r.tx)
~~~

### 665. step_inv

Source: ControlStack/Scenarios/SC26Transaction.lean:307 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (R : Roles) (cap : ℕ) {C : Checks} (hC : Sound C) (s : St) (o : Op) (ho : legal R o) (h : Inv R cap s) : Inv R cap (step R cap C s o)
~~~

### 666. run_cons

Source: ControlStack/Scenarios/SC26Transaction.lean:395 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (R : Roles) (cap : ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) : run R cap C s (o :: ops) = run R cap C (step R cap C s o) ops
~~~

### 667. run_inv

Source: ControlStack/Scenarios/SC26Transaction.lean:398 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (R : Roles) (cap : ℕ) {C : Checks} (hC : Sound C) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) (h : Inv R cap s) : Inv R cap (run R cap C s ops)
~~~

### 668. safe_of_sound

Source: ControlStack/Scenarios/SC26Transaction.lean:409 | Family: F8 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem safe_of_sound (R : Roles) (cap : ℕ) {C : Checks} (hC : Sound C) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) : Good R cap (run R cap C init ops)
~~~

### 669. good_without_nonce

Source: ControlStack/Scenarios/SC26Transaction.lean:414 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem good_without_nonce (R : Roles) (cap : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) : Good R cap (run R cap { full with nonce
~~~

### 670. sc26_safe

Source: ControlStack/Scenarios/SC26Transaction.lean:426 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc26_safe (R : Roles) (cap : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) : Good R cap (run R cap full init ops)
~~~

### 671. sc26_safe_disjoint

Source: ControlStack/Scenarios/SC26Transaction.lean:431 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc26_safe_disjoint (R : Roles) (cap : ℕ) (hdisj : ∀ a ∈ R.approvers, a ∉ R.agents) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) : ∀ e ∈ (run R cap full init ops).bank, ∃ r a, reqOf (run R cap full init ops) e.1 = some r ∧ r.tx = e.2 ∧ (e.1, a, e.2) ∈ (run R cap full init ops).approvals ∧ a ∈ R.approvers ∧ a ∉ R.agents ∧ a ≠ r.requester
~~~

### 672. bankAppend_reserved

Source: ControlStack/Scenarios/SC26Transaction.lean:439 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bankAppend_reserved (C : Checks) (s : St) (k : ℕ) (tx : Tx) : (bankAppend C s k tx).reserved = s.reserved
~~~

### 673. step_res_nodup

Source: ControlStack/Scenarios/SC26Transaction.lean:443 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_res_nodup (R : Roles) (cap : ℕ) (C : Checks) (hn : C.nonce = true) (s : St) (o : Op) (h : s.reserved.Nodup) : (step R cap C s o).reserved.Nodup
~~~

### 674. sc26_once

Source: ControlStack/Scenarios/SC26Transaction.lean:484 | Family: F7 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc26_once (R : Roles) (cap : ℕ) (ops : List Op) : (run R cap full init ops).reserved.Nodup
~~~

### 675. bankAppend_mem

Source: ControlStack/Scenarios/SC26Transaction.lean:492 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bankAppend_mem (C : Checks) (s : St) (k : ℕ) (tx : Tx) (e : ℕ × Tx) (he : e ∈ (bankAppend C s k tx).bank) : e ∈ s.bank ∨ e = (k, tx)
~~~

### 676. step_halted

Source: ControlStack/Scenarios/SC26Transaction.lean:503 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (R : Roles) (cap : ℕ) (s : St) (o : Op) (ho : legal R o) (hh : s.halted = true) : (step R cap full s o).net = s.net ∧ (step R cap full s o).halted = true ∧ ∀ e ∈ (step R cap full s o).bank, e ∈ s.bank ∨ e ∈ s.net
~~~

### 677. halt_freezes

Source: ControlStack/Scenarios/SC26Transaction.lean:532 | Family: F3 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem halt_freezes (R : Roles) (cap : ℕ) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) (hh : s.halted = true) : (run R cap full s ops).net = s.net ∧ ∀ e ∈ (run R cap full s ops).bank, e ∈ s.bank ∨ e ∈ s.net
~~~

### 678. halt_freezes_quiescent

Source: ControlStack/Scenarios/SC26Transaction.lean:547 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes_quiescent (R : Roles) (cap : ℕ) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) (hh : s.halted = true) (hq : ∀ m ∈ s.net, m ∈ s.bank) : ∀ e ∈ (run R cap full s ops).bank, e ∈ s.bank
~~~

### 679. bankAppend_prefix

Source: ControlStack/Scenarios/SC26Transaction.lean:554 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bankAppend_prefix (C : Checks) (s : St) (k : ℕ) (tx : Tx) : s.bank <+: (bankAppend C s k tx).bank
~~~

### 680. bank_prefix

Source: ControlStack/Scenarios/SC26Transaction.lean:560 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bank_prefix (R : Roles) (cap : ℕ) (C : Checks) (s : St) (o : Op) : s.bank <+: (step R cap C s o).bank
~~~

### 681. not_good_of

Source: ControlStack/Scenarios/SC26Transaction.lean:613 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem not_good_of {R : Roles} {cap : ℕ} {s : St} (e : ℕ × Tx) (he : e ∈ s.bank) (hn : ∀ ap ∈ s.approvals, ap.1 = e.1 → ap.2.2 = e.2 → ap.2.1 ∈ R.approvers → False) : ¬ Good R cap s
~~~

### 682. honest_trace_pays

Source: ControlStack/Scenarios/SC26Transaction.lean:620 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_trace_pays : (run R0 20 full init [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .arrive 0, .deliver 0, .arrive 0, .arrive 0]).bank = [(0, tx1)]
~~~

### 683. payload_unchecked_breaks

Source: ControlStack/Scenarios/SC26Transaction.lean:625 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem payload_unchecked_breaks : let s
~~~

### 684. no_dedup_retry_duplicates

Source: ControlStack/Scenarios/SC26Transaction.lean:637 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_dedup_retry_duplicates : let s
~~~

### 685. no_dedup_breaks_cap

Source: ControlStack/Scenarios/SC26Transaction.lean:651 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_dedup_breaks_cap : let s
~~~

### 686. no_bank_auth_breaks

Source: ControlStack/Scenarios/SC26Transaction.lean:658 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_bank_auth_breaks : let s
~~~

### 687. same_payload_twice_is_good

Source: ControlStack/Scenarios/SC26Transaction.lean:669 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem same_payload_twice_is_good : let ops : List Op
~~~

### 688. no_cap_breaks

Source: ControlStack/Scenarios/SC26Transaction.lean:679 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_cap_breaks : let s
~~~

### 689. no_halt_check_breaks

Source: ControlStack/Scenarios/SC26Transaction.lean:693 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : let C
~~~

### 690. halt_check_blocks

Source: ControlStack/Scenarios/SC26Transaction.lean:700 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_check_blocks : let s
~~~

### 691. inflight_after_halt

Source: ControlStack/Scenarios/SC26Transaction.lean:706 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inflight_after_halt : let s
~~~

### 692. gate_credential_leak_breaks

Source: ControlStack/Scenarios/SC26Transaction.lean:712 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gate_credential_leak_breaks : let s
~~~

### 693. self_approval_without_distinct_check

Source: ControlStack/Scenarios/SC26Transaction.lean:724 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem self_approval_without_distinct_check : let s
~~~

### 694. distinct_check_blocks_self_approval

Source: ControlStack/Scenarios/SC26Transaction.lean:743 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem distinct_check_blocks_self_approval : (run R1 20 full init [.request 1 tx1, .approve 1 0 tx1, .execute 1 0, .deliver 0, .arrive 0]).bank = []
~~~

### 695. nonce_protects_budget_only

Source: ControlStack/Scenarios/SC26Transaction.lean:749 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nonce_protects_budget_only : let s
~~~

## ControlStack/Scenarios/SC27Chain.lean

### 696. chainHead_concat

Source: ControlStack/Scenarios/SC27Chain.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem chainHead_concat (H : ℕ → ℕ → ℕ) (h0 : ℕ) (l : List ℕ) (e : ℕ) : chainHead H h0 (l ++ [e]) = H (chainHead H h0 l) e
~~~

### 697. chainHead_injective

Source: ControlStack/Scenarios/SC27Chain.lean:53 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem chainHead_injective (H : ℕ → ℕ → ℕ) (h0 : ℕ) (hinj : ∀ a b c d, H a b = H c d → a = c ∧ b = d) (hne : ∀ a b, H a b ≠ h0) : Function.Injective (chainHead H h0)
~~~

### 698. run_cons

Source: ControlStack/Scenarios/SC27Chain.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) : run E C s (o :: ops) = run E C (step E C s o) ops
~~~

### 699. inv_init

Source: ControlStack/Scenarios/SC27Chain.lean:140 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (E : Env) : Inv E init
~~~

### 700. AccOk.mono

Source: ControlStack/Scenarios/SC27Chain.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem AccOk.mono {E : Env} {s t : St} (ha : s.anchors ⊆ t.anchors) {m : List ℕ} (h : AccOk E s m) : AccOk E t m
~~~

### 701. step_inv

Source: ControlStack/Scenarios/SC27Chain.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o)
~~~

### 702. run_inv

Source: ControlStack/Scenarios/SC27Chain.lean:182 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops)
~~~

### 703. sc27_safe

Source: ControlStack/Scenarios/SC27Chain.lean:191 | Family: F4 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc27_safe (E : Env) (ops : List Op) (hinj : Set.InjOn (chainHead E.H E.h0) {l | l ∈ (run E full init ops).accepted ∨ ∃ a ∈ (run E full init ops).anchors, a.2 = some l}) : ∀ m ∈ (run E full init ops).accepted, ∃ a ∈ (run E full init ops).anchors, a.2 = some m
~~~

### 704. step_halted

Source: ControlStack/Scenarios/SC27Chain.lean:202 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s
~~~

### 705. halt_freezes

Source: ControlStack/Scenarios/SC27Chain.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
~~~

### 706. accepted_prefix

Source: ControlStack/Scenarios/SC27Chain.lean:219 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem accepted_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.accepted <+: (step E C s o).accepted
~~~

### 707. honest_accept

Source: ControlStack/Scenarios/SC27Chain.lean:247 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_accept : (run E0 full init [.append 5, .append 6, .anchor, .verify [5, 6]]).accepted = [[5, 6]]
~~~

### 708. tamper_after_anchor_detected

Source: ControlStack/Scenarios/SC27Chain.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem tamper_after_anchor_detected : (run E0 full init [.append 5, .anchor, .rewrite [7], .verify [7]]).accepted = [] ∧ (run E0 full init [.append 5, .append 6, .anchor, .rewrite [6, 5], .verify [6, 5]]).accepted = []
~~~

### 709. no_anchor_rollback_breaks

Source: ControlStack/Scenarios/SC27Chain.lean:257 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_anchor_rollback_breaks : let s
~~~

### 710. self_signed_breaks

Source: ControlStack/Scenarios/SC27Chain.lean:263 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem self_signed_breaks : (run E0 { full with independentOnly
~~~

### 711. unanchored_suffix_breaks

Source: ControlStack/Scenarios/SC27Chain.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unanchored_suffix_breaks : (run E0 { full with noSuffix
~~~

### 712. collision_breaks

Source: ControlStack/Scenarios/SC27Chain.lean:275 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem collision_breaks : (run ⟨fun h e => (h + e) % 10, 0, [9]⟩ full init [.append 5, .anchor, .verify [2, 3]]).accepted = [[2, 3]]
~~~

### 713. rewrite_before_anchor_window

Source: ControlStack/Scenarios/SC27Chain.lean:280 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rewrite_before_anchor_window : let s
~~~

### 714. no_halt_check_breaks

Source: ControlStack/Scenarios/SC27Chain.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run E0 { full with haltCheck
~~~

## ControlStack/Scenarios/SC28Budget.lean

### 715. forkUpd_full_leases

Source: ControlStack/Scenarios/SC28Budget.lean:105 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem forkUpd_full_leases (s : St) (p ch nl : ℕ) : (forkUpd full s p ch nl).1 = s.leases
~~~

### 716. run_cons

Source: ControlStack/Scenarios/SC28Budget.lean:139 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_cons (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) : run admins G C s (o :: ops) = run admins G C (step admins G C s o) ops
~~~

### 717. Inv.good

Source: ControlStack/Scenarios/SC28Budget.lean:160 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Inv.good {G : ℕ} {s : St} (h : Inv G s) : Good G s
~~~

### 718. inv_init

Source: ControlStack/Scenarios/SC28Budget.lean:163 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_init (G : ℕ) : Inv G init
~~~

### 719. budgetOf_append

Source: ControlStack/Scenarios/SC28Budget.lean:167 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem budgetOf_append (s : St) (lid b : ℕ) (hfresh : budgetOf s lid = none) (l : ℕ) : budgetOf { s with leases
~~~

### 720. inv_of_same

Source: ControlStack/Scenarios/SC28Budget.lean:178 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inv_of_same {G : ℕ} {s t : St} (h : Inv G s) (hl : t.ledger = s.ledger) (hu : t.usage = s.usage) (hb : ∀ lid, (budgetOf s lid).getD 0 ≤ (budgetOf t lid).getD 0 ∨ spentL s lid = 0) : Inv G t
~~~

### 721. work_inv

Source: ControlStack/Scenarios/SC28Budget.lean:191 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem work_inv {G : ℕ} {s : St} (h : Inv G s) (w lid a b ch : ℕ) (hch : a ≤ ch) (h1 : 1 ≤ ch) (hb : budgetOf s lid = some b) (hcl : spentL s lid + ch ≤ b) (hcg : spentT s + ch ≤ G) : Inv G { s with ledger
~~~

### 722. step_inv

Source: ControlStack/Scenarios/SC28Budget.lean:225 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_inv (admins : List ℕ) (G : ℕ) (s : St) (o : Op) (ho : legal o) (h : Inv G s) : Inv G (step admins G full s o)
~~~

### 723. run_inv

Source: ControlStack/Scenarios/SC28Budget.lean:283 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem run_inv (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal o) (h : Inv G s) : Inv G (run admins G full s ops)
~~~

### 724. sc28_safe

Source: ControlStack/Scenarios/SC28Budget.lean:294 | Family: F5 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem sc28_safe (admins : List ℕ) (G : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal o) : Good G (run admins G full init ops)
~~~

### 725. step_revoked

Source: ControlStack/Scenarios/SC28Budget.lean:300 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_revoked (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (o : Op) (lid : ℕ) (hr : lid ∈ s.revoked) : lid ∈ (step admins G C s o).revoked ∧ usedL (step admins G C s o) lid = usedL s lid
~~~

### 726. revoked_lease_stops

Source: ControlStack/Scenarios/SC28Budget.lean:326 | Family: F5 | Adversary: TRACE_ARBITRARY | Status: PROVED_RECORDED

~~~lean
theorem revoked_lease_stops (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (ops : List Op) (lid : ℕ) (hr : lid ∈ s.revoked) : usedL (run admins G C s ops) lid = usedL s lid
~~~

### 727. fork_shares_lease

Source: ControlStack/Scenarios/SC28Budget.lean:337 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fork_shares_lease (admins : List ℕ) (G : ℕ) (s : St) (c p ch nl lid : ℕ) (hh : s.halted = false) (hp : leaseOf s p = some lid) (hfresh : ch ∉ s.assign.map Prod.fst) : leaseOf (step admins G full s (.fork c p ch nl)) ch = some lid
~~~

### 728. step_halted

Source: ControlStack/Scenarios/SC28Budget.lean:346 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem step_halted (admins : List ℕ) (G : ℕ) (s : St) (o : Op) (hh : s.halted = true) : (step admins G full s o).usage = s.usage ∧ (step admins G full s o).halted = true
~~~

### 729. halt_freezes

Source: ControlStack/Scenarios/SC28Budget.lean:356 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem halt_freezes (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op) (hh : s.halted = true) : (run admins G full s ops).usage = s.usage
~~~

### 730. usage_prefix

Source: ControlStack/Scenarios/SC28Budget.lean:367 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usage_prefix (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (o : Op) : s.usage <+: (step admins G C s o).usage
~~~

### 731. Good.entry

Source: ControlStack/Scenarios/SC28Budget.lean:381 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Good.entry {G : ℕ} {s : St} (h : Good G s) (e : ℕ × ℕ × ℕ) (he : e ∈ s.usage) : EntryOk s e
~~~

### 732. honest_trace_works

Source: ControlStack/Scenarios/SC28Budget.lean:402 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honest_trace_works : (run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0, .work 1 3 3, .restart, .work 1 4 4]).usage = [(1, 0, 3), (1, 0, 4)]
~~~

### 733. no_global_counter_breaks

Source: ControlStack/Scenarios/SC28Budget.lean:408 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_global_counter_breaks : usedT (run [9] 10 { full with global
~~~

### 734. fresh_fork_exceeds_parent

Source: ControlStack/Scenarios/SC28Budget.lean:416 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fresh_fork_exceeds_parent : (run [9] 100 { full with share
~~~

### 735. fresh_fork_escapes_revocation

Source: ControlStack/Scenarios/SC28Budget.lean:425 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fresh_fork_escapes_revocation : (run [9] 100 { full with share
~~~

### 736. reported_cost_breaks

Source: ControlStack/Scenarios/SC28Budget.lean:433 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reported_cost_breaks : let s
~~~

### 737. rollback_double_spends

Source: ControlStack/Scenarios/SC28Budget.lean:440 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rollback_double_spends : usedT (run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0, .work 1 10 0, .rollback 0, .work 1 10 0]) = 20
~~~

### 738. no_halt_check_breaks

Source: ControlStack/Scenarios/SC28Budget.lean:445 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem no_halt_check_breaks : (run [9] 10 { full with haltCheck
~~~

## ControlStack/SideChannel.lean

### 739. per_seed_side

Source: ControlStack/SideChannel.lean:31 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem per_seed_side {M V S O : Type} [Fintype M] [Fintype V] [Fintype S] [Fintype O] (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (enc : M → V × S → ℝ) (dec : V × O → M → ℝ) (henc : ∀ m, IsDist (enc m)) (hdec : ∀ y, IsDist (dec y)) : ∑ m, ∑ x : V × S, enc m x * ∑ o, W x.2 o * dec (x.1, o) m ≤ (Fintype.card V : ℝ) * ∑ o, c o
~~~

### 740. side_bound

Source: ControlStack/SideChannel.lean:78 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem side_bound {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O] [Nonempty M] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ W enc dec ≤ (Fintype.card V : ℝ) * (∑ o, c o) / (Fintype.card M : ℝ)
~~~

### 741. side_bound_uninfluenced

Source: ControlStack/SideChannel.lean:95 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem side_bound_uninfluenced {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O] [Nonempty M] (ρ : Ω → ℝ) (w : O → ℝ) (hw : IsDist w) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ (fun _ => w) enc dec ≤ (Fintype.card V : ℝ) / (Fintype.card M : ℝ)
~~~

### 742. side_bound_trivial

Source: ControlStack/SideChannel.lean:104 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem side_bound_trivial {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O] [Nonempty M] (ρ : Ω → ℝ) (W : S → O → ℝ) (hW : ∀ s, IsDist (W s)) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) : sideSuccess ρ W enc dec ≤ (Fintype.card V : ℝ) * (Fintype.card O : ℝ) / (Fintype.card M : ℝ)
~~~

### 743. dom_pi

Source: ControlStack/SideChannel.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dom_pi {E : ℕ} {S O : Fin E → Type} [∀ e, Fintype (O e)] (W : (e : Fin E) → S e → O e → ℝ) (c : (e : Fin E) → O e → ℝ) (hW0 : ∀ e s o, 0 ≤ W e s o) (hc : ∀ e s o, W e s o ≤ c e o) : (∀ (s : (e : Fin E) → S e) (o : (e : Fin E) → O e), ∏ e, W e (s e) (o e) ≤ ∏ e, c e (o e)) ∧ ∑ o : ((e : Fin E) → O e), ∏ e, c e (o e) = ∏ e, ∑ o, c e o
~~~

### 744. side_as_covert

Source: ControlStack/SideChannel.lean:128 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem side_as_covert {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) : sideSuccess ρ W enc dec = successProb ρ (fun ω m y => ∑ s, enc ω m (y.1, s) * W s y.2) dec
~~~

### 745. bsc_dom

Source: ControlStack/SideChannel.lean:147 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bsc_dom (q : ℝ) (hq : q ≤ 1 / 2) : ∀ s o, bsc q s o ≤ 1 - q
~~~

### 746. bsc_dist

Source: ControlStack/SideChannel.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bsc_dist (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (s : Bool) : IsDist (bsc q s)
~~~

## ControlStack/SoftHockey.lean

### 747. viewLaw_nonneg

Source: ControlStack/SoftHockey.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem viewLaw_nonneg {Z : Type} [Fintype Z] (c : ProbComp Z) (z : Z) : 0 ≤ viewLaw c z
~~~

### 748. viewLaw_sum

Source: ControlStack/SoftHockey.lean:22 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem viewLaw_sum {Z : Type} [Fintype Z] (c : ProbComp Z) : ∑ z, viewLaw c z = 1
~~~

### 749. passRule_isRule

Source: ControlStack/SoftHockey.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem passRule_isRule {Z : Type} (D : Z → ProbComp Bool) : isRule (fun z => (Pr[= true | D z]).toReal)
~~~

### 750. viewLaw_pass

Source: ControlStack/SoftHockey.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem viewLaw_pass {Z : Type} [Fintype Z] (c : ProbComp Z) (D : Z → ProbComp Bool) : ∑ z, viewLaw c z * (Pr[= true | D z]).toReal = (Pr[= true | c >>= D]).toReal
~~~

### 751. hockey_pass_bound

Source: ControlStack/SoftHockey.lean:38 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hockey_pass_bound {Z : Type} [Fintype Z] (η : ℝ) (P Q : Z → ℝ) (D : Z → ProbComp Bool) : (∑ z, P z * (Pr[= true | D z]).toReal) ≤ Real.exp η * (∑ z, Q z * (Pr[= true | D z]).toReal) + hs η P Q
~~~

### 752. operational_hockey_bound

Source: ControlStack/SoftHockey.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem operational_hockey_bound {Z : Type} [Fintype Z] (η δ : ℝ) (H : ProbComp Z) (X : ProbComp Z) (D : Z → ProbComp Bool) (hδ : hs η (viewLaw X) (viewLaw H) ≤ δ) : (Pr[= true | X >>= D]).toReal ≤ Real.exp η * (Pr[= true | H >>= D]).toReal + δ
~~~

### 753. softEndToEndHockey

Source: ControlStack/SoftHockey.lean:71 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem softEndToEndHockey {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) (r η δ : ℝ) (hns : 1 ≤ ns) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hδ0 : 0 ≤ δ) (hrec : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) (hhs : ∀ x, Bad x → hs η (viewLaw (M x)) (viewLaw (H >>= M)) ≤ δ) : (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal ≤ (1 - r) + r * (δ + Real.exp η * ((ns : ℝ) / ((nh : ℝ) + 1)))
~~~

## ControlStack/SoftSlack.lean

### 754. rejection_rate

Source: ControlStack/SoftSlack.lean:32 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rejection_rate (d : ℕ) : (Pr[= true | rejectionCoin d]).toReal = 1 / ((d + 1 : ℕ) : ℝ)
~~~

### 755. survives_step

Source: ControlStack/SoftSlack.lean:39 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survives_step {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (d n : ℕ) : Pr[= true | survives H M D d (n + 1)] = Pr[= true | H >>= M >>= D] * Pr[= false | rejectionCoin d] * Pr[= true | survives H M D d n] + Pr[= false | H >>= M >>= D] * Pr[= true | survives H M D d n]
~~~

### 756. survives_step_real

Source: ControlStack/SoftSlack.lean:58 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survives_step_real {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (d n : ℕ) : (Pr[= true | survives H M D d (n + 1)]).toReal = (1 - (Pr[= true | H >>= M >>= D]).toReal / ((d + 1 : ℕ) : ℝ)) * (Pr[= true | survives H M D d n]).toReal
~~~

### 757. bridge

Source: ControlStack/SoftSlack.lean:75 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bridge : BridgeClaim
~~~

### 758. geom_poly_bound

Source: ControlStack/SoftSlack.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem geom_poly_bound (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (1 + (n : ℝ) * x) * (1 - x) ^ n ≤ 1
~~~

### 759. soft_survival_first_moment

Source: ControlStack/SoftSlack.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem soft_survival_first_moment (nh ns : ℕ) (h : ℝ) (hns : 1 ≤ ns) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : h * (1 - h / (ns : ℝ)) ^ nh ≤ (ns : ℝ) / ((nh : ℝ) + 1)
~~~

### 760. protocol_factorization

Source: ControlStack/SoftSlack.lean:147 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem protocol_factorization {X Z Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) : (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal = ∑ ω, (Pr[= ω | ρ]).toReal * (Pr[= true | survives H M (D ω) (ns - 1) nh]).toReal * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
~~~

### 761. protocol_survival_formula

Source: ControlStack/SoftSlack.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem protocol_survival_formula {X Z Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) (hns : 1 ≤ ns) : (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal = ∑ ω, (Pr[= ω | ρ]).toReal * (1 - (Pr[= true | H >>= M >>= D ω]).toReal / (ns : ℝ)) ^ nh * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
~~~

### 762. softEndToEnd

Source: ControlStack/SoftSlack.lean:188 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem softEndToEnd {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) (r L : ℝ) (hns : 1 ≤ ns) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hrec : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) (hdom : ∀ x, Bad x → ∀ z, (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) : (Pr[= true | softProtocolGame Bad ρ H M D π A nh ns b N]).toReal ≤ (1 - r) + r * (L * ((ns : ℝ) / ((nh : ℝ) + 1)))
~~~

## ControlStack/Spike.lean

### 763. distinguish_le_tv

Source: ControlStack/Spike.lean:17 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem distinguish_le_tv {X Z : Type} (M : X → ProbComp Z) (PA PH : ProbComp X) (D : Z → ProbComp Bool) : |Pr[= true | PA >>= M >>= D].toReal - Pr[= true | PH >>= M >>= D].toReal| ≤ tvDist (PA >>= M) (PH >>= M)
~~~

### 764. mediated_tv_le

Source: ControlStack/Spike.lean:24 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mediated_tv_le {X Z : Type} (M : X → ProbComp Z) (PA PH : ProbComp X) : tvDist (PA >>= M) (PH >>= M) ≤ tvDist PA PH
~~~

## ControlStack/StratifiedGame.lean

### 765. classPasses_bridge

Source: ControlStack/StratifiedGame.lean:28 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classPasses_bridge {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (m sc : ℕ) : (Pr[= true | classPasses H M D m sc]).toReal = binCDF m sc (Pr[= true | H >>= M >>= D]).toReal
~~~

### 766. stratifiedSurvives_prob

Source: ControlStack/StratifiedGame.lean:37 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedSurvives_prob {X Z C : Type} (H : C → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (m sc : ℕ) (classes : List C) : (Pr[= true | stratifiedSurvives H M D m sc classes]).toReal = (classes.map fun e => (Pr[= true | classPasses (H e) M D m sc]).toReal).prod
~~~

### 767. stratifiedSurvives_binomial

Source: ControlStack/StratifiedGame.lean:54 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedSurvives_binomial {X Z C : Type} (H : C → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (m sc : ℕ) (classes : List C) : (Pr[= true | stratifiedSurvives H M D m sc classes]).toReal = (classes.map fun e => binCDF m sc (Pr[= true | H e >>= M >>= D]).toReal).prod
~~~

### 768. stratifiedProtocol_factorization

Source: ControlStack/StratifiedGame.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedProtocol_factorization {X Z C Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : Ω → C → ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (classes : List C) (m sc b N : ℕ) : (Pr[= true | stratifiedProtocolGame Bad ρ H M D π A classes m sc b N]).toReal = ∑ ω, (Pr[= ω | ρ]).toReal * (Pr[= true | stratifiedSurvives (H ω) M (D ω) m sc classes]).toReal * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
~~~

### 769. stratifiedProtocol_binomial

Source: ControlStack/StratifiedGame.lean:103 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedProtocol_binomial {X Z C Ω : Type} [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω) (H : Ω → C → ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (classes : List C) (m sc b N : ℕ) : (Pr[= true | stratifiedProtocolGame Bad ρ H M D π A classes m sc b N]).toReal = ∑ ω, (Pr[= ω | ρ]).toReal * (classes.map fun e => binCDF m sc (Pr[= true | H ω e >>= M >>= D ω]).toReal).prod * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
~~~

### 770. listProduct_nonneg

Source: ControlStack/StratifiedGame.lean:118 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem listProduct_nonneg {C : Type} (classes : List C) (f : C → ℝ) (hf0 : ∀ e ∈ classes, 0 ≤ f e) : 0 ≤ (classes.map f).prod
~~~

### 771. listProduct_le_one

Source: ControlStack/StratifiedGame.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem listProduct_le_one {C : Type} (classes : List C) (f : C → ℝ) (hf0 : ∀ e ∈ classes, 0 ≤ f e) (hf1 : ∀ e ∈ classes, f e ≤ 1) : (classes.map f).prod ≤ 1
~~~

### 772. listProduct_le_factor

Source: ControlStack/StratifiedGame.lean:148 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem listProduct_le_factor {C : Type} (classes : List C) (f : C → ℝ) (hf0 : ∀ e ∈ classes, 0 ≤ f e) (hf1 : ∀ e ∈ classes, f e ≤ 1) (e : C) (he : e ∈ classes) : (classes.map f).prod ≤ f e
~~~

### 773. stratifiedProtocolEndToEnd

Source: ControlStack/StratifiedGame.lean:179 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem stratifiedProtocolEndToEnd {X Z C Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (classOf : X → C) (classes : List C) (ρ : ProbComp Ω) (H : Ω → C → ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (m sc b N : ℕ) (r L : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hrec : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) (hclass : ∀ x, Bad x → classOf x ∈ classes) (hdom : ∀ ω x z, Bad x → (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H ω (classOf x) >>= M]).toReal) : (Pr[= true | stratifiedProtocolGame Bad ρ H M D π A classes m sc b N]).toReal ≤ (1 - r) + r * (L * (((sc : ℝ) + 1) / ((m : ℝ) + 1)))
~~~

## ControlStack/UseQ.lean

### 774. foldl_add_eq

Source: ControlStack/UseQ.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_add_eq {m : ℕ} (f : Fin m → ℚ) : ∀ (l : List (Fin m)) (acc : ℚ), l.foldl (fun acc i => acc + f i) acc = acc + (l.map f).sum
~~~

### 775. sumQ_eq

Source: ControlStack/UseQ.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sumQ_eq (m : ℕ) (f : Fin m → ℚ) : sumQ m f = ∑ i, f i
~~~

### 776. checkUseQ_spec

Source: ControlStack/UseQ.lean:33 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkUseQ_spec {N m t : ℕ} {rew : Fin t → Fin N → Fin m → ℚ} {K : Fin t → Fin N → Fin m → Fin m → ℚ} {adm : Fin t → Fin N → Fin m → Bool} {W : Fin (N + 1) → Fin m → ℚ} {s₀ : Fin m} {floor : ℚ} (hc : checkUseQ N m t rew K adm W s₀ floor = true) : 0 < t ∧ floor ≤ W (Fin.last N) s₀ ∧ (∀ s, W 0 s ≤ 0) ∧ (∀ i s, ∃ th, adm th i s = true) ∧ (∀ th i s, adm th i s = true → W i.succ s ≤ rew th i s + ∑ s', K th i s s' * W i.castSucc s')
~~~

### 777. selector_exists

Source: ControlStack/UseQ.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem selector_exists {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ) (K : Fin t → Fin N → Fin m → Fin m → ℚ) (adm : Fin t → Fin N → Fin m → Bool) (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ) (hc : checkUseQ N m t rew K adm W s₀ floor = true) : ∃ θ : ℕ → List (Fin m) → Fin m → Fin t, ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true
~~~

### 778. checkUseQ_sound

Source: ControlStack/UseQ.lean:76 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkUseQ_sound {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ) (K : Fin t → Fin N → Fin m → Fin m → ℚ) (adm : Fin t → Fin N → Fin m → Bool) (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ) (θ : ℕ → List (Fin m) → Fin m → Fin t) (hc : checkUseQ N m t rew K adm W s₀ floor = true) (hK : ∀ th i s, adm th i s = true → ∀ s', 0 ≤ K th i s s') (hθ : ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true) : (floor : ℝ) ≤ honestValue rew K θ N s₀ []
~~~

### 779. claim

Source: ControlStack/UseQ.lean:156 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 780. witness

Source: ControlStack/UseQ.lean:163 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## ControlStack/Witnesses/DeputyBridge.lean

### 781. payment_deputy_breaks_deploy_gate

Source: ControlStack/Witnesses/DeputyBridge.lean:40 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem payment_deputy_breaks_deploy_gate : let p
~~~

### 782. approved_inv

Source: ControlStack/Witnesses/DeputyBridge.lean:53 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem approved_inv : SC26.Inv SC26.R0 20 (SC26.run SC26.R0 20 SC26.full SC26.init [.request 1 SC26.tx1, .approve 2 0 SC26.tx1])
~~~

### 783. payment_deputy_not_admissible

Source: ControlStack/Witnesses/DeputyBridge.lean:58 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem payment_deputy_not_admissible : ¬ BridgeAdmissible (SC26.spec SC26.R0 20) (SC16.spec R16 id) paymentDeputy
~~~

### 784. gated_deputy_admissible

Source: ControlStack/Witnesses/DeputyBridge.lean:71 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gated_deputy_admissible (h : ℕ → ℕ) (cap : ℕ) (R : SC26.Roles) : BridgeAdmissible (SC26.spec R cap) (SC16.spec R16 h) (gatedDeputy h)
~~~

### 785. gated_deputy_deploys_nothing

Source: ControlStack/Witnesses/DeputyBridge.lean:79 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gated_deputy_deploys_nothing : ((withBridge (SC26.sys SC26.R0 20) (SC16.sys R16 id) (gatedDeputy id)).run start trace).s₂.deployed = []
~~~

## ControlStack/Witnesses/LeakWitness.lean

### 786. K_nonneg

Source: ControlStack/Witnesses/LeakWitness.lean:45 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem K_nonneg (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) (z : Unit × AOut Bool) : 0 ≤ K ε S h z
~~~

### 787. K_sum

Source: ControlStack/Witnesses/LeakWitness.lean:49 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem K_sum (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) : ∑ z, K ε S h z ≤ 1
~~~

### 788. K_cons

Source: ControlStack/Witnesses/LeakWitness.lean:59 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem K_cons (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) (y : Unit) (o : AOut Bool) (hK : K ε S h (y, o) ≠ 0) : o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length))
~~~

### 789. K_dom

Source: ControlStack/Witnesses/LeakWitness.lean:67 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem K_dom (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) (o : AOut Bool) (hf : o.2.2 = false) : ∑ y, K ε S h (y, o) ≤ cl ε (h.map Prod.snd) o
~~~

### 790. cl_nonneg

Source: ControlStack/Witnesses/LeakWitness.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cl_nonneg (g : List (AOut Bool)) (o : AOut Bool) : 0 ≤ cl ε g o
~~~

### 791. leak_mass

Source: ControlStack/Witnesses/LeakWitness.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem leak_mass : mass (dropStop caughtFlag (cl ε)) 2 [] = 2 * (1 - ε)
~~~

### 792. leak_bound

Source: ControlStack/Witnesses/LeakWitness.lean:93 | Family: F6 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem leak_bound : ∑ S : Finset (Fin 2), (if S ∈ AuditBudget.randomSchedules 2 1 then (Nat.choose 2 1 : ℝ)⁻¹ else 0) * val (K ε S) (survInd 1 S) 2 [] ≤ 1 - ε
~~~

## ControlStack/Witnesses/Necessity.lean

### 793. jointSuccess_indep

Source: ControlStack/Witnesses/Necessity.lean:35 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem jointSuccess_indep {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V] (ρ : Ω → ℝ) (enc : Ω → M → V → ℝ) (dec : Ω → V → M → ℝ) : jointSuccess (fun ω _ => ρ ω * (Fintype.card M : ℝ)⁻¹) enc dec = successProb ρ enc dec
~~~

### 794. seed_secret_breaks_covert

Source: ControlStack/Witnesses/Necessity.lean:48 | Family: F2 | Adversary: SHARED_SEED | Status: SOURCE_ONLY

~~~lean
theorem seed_secret_breaks_covert {M : Type} [Fintype M] [DecidableEq M] (hM : 2 ≤ Fintype.card M) : jointSuccess (fun (ω m : M) => if ω = m then (Fintype.card M : ℝ)⁻¹ else 0) (fun (_ _ : M) (_ : Unit) => (1 : ℝ)) (fun (ω : M) (_ : Unit) (m : M) => if m = ω then (1 : ℝ) else 0) = 1 ∧ (Fintype.card Unit : ℝ) / (Fintype.card M : ℝ) < 1
~~~

### 795. comono_dist

Source: ControlStack/Witnesses/Necessity.lean:79 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem comono_dist (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsDist (comono p)
~~~

### 796. comono_marginal

Source: ControlStack/Witnesses/Necessity.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem comono_marginal (p : ℝ) (i : Fin 64) : ∑ x, comono p x * (if x i = true then 1 else 0) = p
~~~

### 797. correlated_lifetimes_break_gate

Source: ControlStack/Witnesses/Necessity.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem correlated_lifetimes_break_gate : (∀ i : Fin 64, ∑ x, comono (9 / 10) x * (if x i = true then 1 else 0) = 9 / 10) ∧ ∑ x, comono (9 / 10) x * (if 63 ≤ count x then 1 else 0) = 9 / 10 ∧ ScenarioAUsefulness.passProb (9 / 10) ≤ 1 / 80 ∧ (1 : ℝ) / 80 < 9 / 10
~~~

### 798. marginal_certs_dont_compose

Source: ControlStack/Witnesses/Necessity.lean:117 | Family: F8 | Adversary: SIDE_OBSERVING | Status: SOURCE_ONLY

~~~lean
theorem marginal_certs_dont_compose : (∀ m b, ∑ o : Bool × Bool, xorLaw m o * (if o.1 = b then 1 else 0) = 1 / 2) ∧ (∀ m b, ∑ o : Bool × Bool, xorLaw m o * (if o.2 = b then 1 else 0) = 1 / 2) ∧ (1 / 2 : ℝ) * ∑ m : Bool, ∑ o : Bool × Bool, xorLaw m o * (if xor o.1 o.2 = m then 1 else 0) = 1
~~~

### 799. shared_score_product_unsound

Source: ControlStack/Witnesses/Necessity.lean:130 | Family: F8 | Adversary: SHARED_SEED | Status: SOURCE_ONLY

~~~lean
theorem shared_score_product_unsound : (∑ s : Bool, scoreLaw s * (if s = false then 1 else 0)) = 1 / 10 ∧ (∑ s : Bool, scoreLaw s * (if s = false ∧ s = false then 1 else 0)) = 1 / 10 ∧ (1 / 10 : ℝ) * (1 / 10) < 1 / 10
~~~

### 800. exhausted_no_audit

Source: ControlStack/Witnesses/Necessity.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exhausted_no_audit {N : ℕ} (B : ℕ) (flags : Fin N → Bool) (A : Finset (Fin N)) (h : ∀ i ∈ A, B ≤ (Finset.univ.filter (fun j : Fin N => j < i ∧ flags j = true)).card) : ∀ i ∈ A, audited B flags i = false
~~~

### 801. audited_last

Source: ControlStack/Witnesses/Necessity.lean:164 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem audited_last (b : Bool × Bool × Bool) : audited 1 (flagsOf b) 3 = (!b.1 && !b.2.1 && !b.2.2)
~~~

### 802. fp_exhaustion_breaks_audit

Source: ControlStack/Witnesses/Necessity.lean:176 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fp_exhaustion_breaks_audit : (∑ b : Bool × Bool × Bool, (1 / 8 : ℚ) * (if audited 1 (flagsOf b) 3 = false then 1 else 0)) = 7 / 8 ∧ (Nat.choose 3 1 : ℚ) / Nat.choose 4 1 = 3 / 4
~~~

## proofs/CANONF1.lean

### 803. k_aren_comp

Source: proofs/CANONF1.lean:4 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_aren_comp (f g : ℕ → ℕ) (a : AExp) : (a.rename f).rename g = a.rename (g ∘ f)
~~~

### 804. k_bren_comp

Source: proofs/CANONF1.lean:7 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_bren_comp (f g : ℕ → ℕ) (b : BExp) : (b.rename f).rename g = b.rename (g ∘ f)
~~~

### 805. k_sren_comp

Source: proofs/CANONF1.lean:10 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_sren_comp (f g : ℕ → ℕ) (s : Stmt) : (s.rename f).rename g = s.rename (g ∘ f)
~~~

### 806. k_pren_comp

Source: proofs/CANONF1.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_pren_comp (f g : ℕ → ℕ) (p : Prog) : (p.rename f).rename g = p.rename (g ∘ f)
~~~

### 807. k_aocc_ren

Source: proofs/CANONF1.lean:16 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_aocc_ren (f : ℕ → ℕ) (a : AExp) : (a.rename f).occ = a.occ.map f
~~~

### 808. k_bocc_ren

Source: proofs/CANONF1.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_bocc_ren (f : ℕ → ℕ) (b : BExp) : (b.rename f).occ = b.occ.map f
~~~

### 809. k_socc_ren

Source: proofs/CANONF1.lean:22 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_socc_ren (f : ℕ → ℕ) (s : Stmt) : (s.rename f).occ = s.occ.map f
~~~

### 810. k_pocc_ren

Source: proofs/CANONF1.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_pocc_ren (f : ℕ → ℕ) (p : Prog) : (p.rename f).occ = p.occ.map f
~~~

### 811. k_aren_congr

Source: proofs/CANONF1.lean:28 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_aren_congr {f g : ℕ → ℕ} (a : AExp) (h : ∀ v ∈ a.occ, f v = g v) : a.rename f = a.rename g
~~~

### 812. k_bren_congr

Source: proofs/CANONF1.lean:43 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_bren_congr {f g : ℕ → ℕ} (b : BExp) (h : ∀ v ∈ b.occ, f v = g v) : b.rename f = b.rename g
~~~

### 813. k_sren_congr

Source: proofs/CANONF1.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_sren_congr {f g : ℕ → ℕ} (s : Stmt) (h : ∀ v ∈ s.occ, f v = g v) : s.rename f = s.rename g
~~~

### 814. k_pren_congr

Source: proofs/CANONF1.lean:85 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_pren_congr {f g : ℕ → ℕ} (p : Prog) (h : ∀ v ∈ p.occ, f v = g v) : p.rename f = p.rename g
~~~

### 815. k_pren_id

Source: proofs/CANONF1.lean:91 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_pren_id (p : Prog) : p.rename id = p
~~~

### 816. k_aeval_ren

Source: proofs/CANONF1.lean:101 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_aeval_ren {f : ℕ → ℕ} {σ τ : State} (a : AExp) (h : ∀ v ∈ a.occ, τ (f v) = σ v) : (a.rename f).eval τ = a.eval σ
~~~

### 817. k_beval_ren

Source: proofs/CANONF1.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_beval_ren {f : ℕ → ℕ} {σ τ : State} (b : BExp) (h : ∀ v ∈ b.occ, τ (f v) = σ v) : (b.rename f).eval τ = b.eval σ
~~~

### 818. k_exec_seq_iff

Source: proofs/CANONF1.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_exec_seq_iff {s t : Stmt} {σ σ'' : State} : Exec (.seq s t) σ σ'' ↔ ∃ σ', Exec s σ σ' ∧ Exec t σ' σ''
~~~

### 819. k_exec_ite_iff

Source: proofs/CANONF1.lean:151 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_exec_ite_iff {b : BExp} {s t : Stmt} {σ σ' : State} : Exec (.ite b s t) σ σ' ↔ (b.eval σ = true ∧ Exec s σ σ') ∨ (b.eval σ = false ∧ Exec t σ σ')
~~~

### 820. k_exec_cfor_iff

Source: proofs/CANONF1.lean:162 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_exec_cfor_iff {i : Stmt} {c : BExp} {st body : Stmt} {σ σ' : State} : Exec (.cfor i c st body) σ σ' ↔ Exec (.seq i (.while c (.seq body st))) σ σ'
~~~

### 821. k_while_mono

Source: proofs/CANONF1.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_while_mono {b : BExp} {s s' : Stmt} (h : ∀ σ σ', Exec s σ σ' → Exec s' σ σ') : ∀ σ σ', Exec (.while b s) σ σ' → Exec (.while b s') σ σ'
~~~

### 822. k_seq_congr

Source: proofs/CANONF1.lean:189 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_seq_congr {s s' t t' : Stmt} (h1 : KSEq s s') (h2 : KSEq t t') : KSEq (.seq s t) (.seq s' t')
~~~

### 823. k_ite_congr

Source: proofs/CANONF1.lean:195 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_ite_congr {b : BExp} {s s' t t' : Stmt} (h1 : KSEq s s') (h2 : KSEq t t') : KSEq (.ite b s t) (.ite b s' t')
~~~

### 824. k_while_congr

Source: proofs/CANONF1.lean:201 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_while_congr {b : BExp} {s s' : Stmt} (h : KSEq s s') : KSEq (.while b s) (.while b s')
~~~

### 825. k_cfor_congr

Source: proofs/CANONF1.lean:206 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_cfor_congr {i i' : Stmt} {c : BExp} {st st' b b' : Stmt} (hi : KSEq i i') (hst : KSEq st st') (hb : KSEq b b') : KSEq (.cfor i c st b) (.cfor i' c st' b')
~~~

### 826. k_sEq_refl

Source: proofs/CANONF1.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_sEq_refl (s : Stmt) : KSEq s s
~~~

### 827. k_forstep_sEq

Source: proofs/CANONF1.lean:214 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_forstep_sEq {s t : Stmt} (h : ForStep s t) : KSEq s t
~~~

### 828. k_eqv_sEq

Source: proofs/CANONF1.lean:234 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_sEq {s t : Stmt} (h : Relation.EqvGen ForStep s t) : KSEq s t
~~~

### 829. k_exec_rename

Source: proofs/CANONF1.lean:243 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_exec_rename {f : ℕ → ℕ} {V : Set ℕ} (hf : Set.InjOn f V) {s : Stmt} {σ σ' : State} (h : Exec s σ σ') : (∀ v ∈ s.occ, v ∈ V) → ∀ τ : State, (∀ v ∈ V, τ (f v) = σ v) → ∃ τ', Exec (s.rename f) τ τ' ∧ ∀ v ∈ V, τ' (f v) = σ' v
~~~

### 830. k_runs_rename

Source: proofs/CANONF1.lean:294 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_runs_rename {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) {ins : List ℤ} {out : ℤ} (h : Runs p ins out) : Runs (p.rename f) ins out
~~~

### 831. k_ren_inverse

Source: proofs/CANONF1.lean:311 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_ren_inverse {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) : ∃ g, Admissible g (p.rename f) ∧ (p.rename f).rename g = p
~~~

### 832. k_runs_rename_iff

Source: proofs/CANONF1.lean:349 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_runs_rename_iff {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) (ins : List ℤ) (out : ℤ) : Runs p ins out ↔ Runs (p.rename f) ins out
~~~

### 833. k_append_assoc

Source: proofs/CANONF1.lean:362 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_append_assoc (a b c : Stmt) : (a.append b).append c = a.append (b.append c)
~~~

### 834. k_FF_step

Source: proofs/CANONF1.lean:369 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_FF_step {s t : Stmt} (h : ForStep s t) : KFF s = KFF t
~~~

### 835. k_FF_eqv

Source: proofs/CANONF1.lean:398 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_FF_eqv {s t : Stmt} (h : Relation.EqvGen ForStep s t) : KFF s = KFF t
~~~

### 836. k_desugar_ren

Source: proofs/CANONF1.lean:405 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_desugar_ren (f : ℕ → ℕ) (s : Stmt) : desugar (s.rename f) = (desugar s).rename f
~~~

### 837. k_append_ren

Source: proofs/CANONF1.lean:408 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_append_ren (f : ℕ → ℕ) (a b : Stmt) : (a.append b).rename f = (a.rename f).append (b.rename f)
~~~

### 838. k_flatten_ren

Source: proofs/CANONF1.lean:417 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_flatten_ren (f : ℕ → ℕ) (s : Stmt) : flatten (s.rename f) = (flatten s).rename f
~~~

### 839. k_FF_ren

Source: proofs/CANONF1.lean:420 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_FF_ren (f : ℕ → ℕ) (s : Stmt) : KFF (s.rename f) = (KFF s).rename f
~~~

### 840. k_occ_append

Source: proofs/CANONF1.lean:423 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_occ_append (a b : Stmt) : (a.append b).occ = a.occ ++ b.occ
~~~

### 841. k_occ_flatten

Source: proofs/CANONF1.lean:430 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_occ_flatten (s : Stmt) : (flatten s).occ = s.occ
~~~

### 842. k_mem_occ_desugar

Source: proofs/CANONF1.lean:433 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_occ_desugar (s : Stmt) (v : ℕ) : v ∈ (desugar s).occ ↔ v ∈ s.occ
~~~

### 843. k_mem_occ_FF

Source: proofs/CANONF1.lean:444 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_occ_FF (s : Stmt) (v : ℕ) : v ∈ (KFF s).occ ↔ v ∈ s.occ
~~~

### 844. k_firstOcc_eq

Source: proofs/CANONF1.lean:451 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_firstOcc_eq (l : List ℕ) : firstOcc l = l.foldl kstep []
~~~

### 845. k_mem_foldl

Source: proofs/CANONF1.lean:453 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_foldl (l acc : List ℕ) (v : ℕ) : v ∈ l.foldl kstep acc ↔ v ∈ acc ∨ v ∈ l
~~~

### 846. k_mem_firstOcc

Source: proofs/CANONF1.lean:472 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_firstOcc (l : List ℕ) (v : ℕ) : v ∈ firstOcc l ↔ v ∈ l
~~~

### 847. k_foldl_map

Source: proofs/CANONF1.lean:476 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_foldl_map {f : ℕ → ℕ} {S : Set ℕ} (hf : Set.InjOn f S) (l acc : List ℕ) (hl : ∀ v ∈ l, v ∈ S) (hacc : ∀ v ∈ acc, v ∈ S) : (l.map f).foldl kstep (acc.map f) = (l.foldl kstep acc).map f
~~~

### 848. k_firstOcc_map

Source: proofs/CANONF1.lean:509 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_firstOcc_map {f : ℕ → ℕ} {S : Set ℕ} (hf : Set.InjOn f S) (l : List ℕ) (hl : ∀ v ∈ l, v ∈ S) : firstOcc (l.map f) = (firstOcc l).map f
~~~

### 849. k_idxOf_map

Source: proofs/CANONF1.lean:515 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_idxOf_map {f : ℕ → ℕ} {S : Set ℕ} (hf : Set.InjOn f S) (v : ℕ) (hv : v ∈ S) : ∀ (L : List ℕ), (∀ w ∈ L, w ∈ S) → (L.map f).idxOf (f v) = L.idxOf v | [], _ => rfl | a :: L, hL => by rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, k_idxOf_map hf v hv L (fun w hw => hL w (by simp [hw]))] have ha : a ∈ S
~~~

### 850. k_canon_eq

Source: proofs/CANONF1.lean:532 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canon_eq (p : Prog) : canon p = kcanon' (desugarProg p)
~~~

### 851. k_mem_locals

Source: proofs/CANONF1.lean:534 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_mem_locals {d : Prog} {v : ℕ} : v ∈ d.locals ↔ v ∈ d.occ ∧ d.nparams ≤ v
~~~

### 852. k_canonMap_ren

Source: proofs/CANONF1.lean:537 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canonMap_ren {f : ℕ → ℕ} {d : Prog} (hA : Admissible f d) (v : ℕ) (hv : v ∈ d.occ) : (d.rename f).canonMap (f v) = d.canonMap v
~~~

### 853. k_canon'_ren

Source: proofs/CANONF1.lean:567 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canon'_ren {f : ℕ → ℕ} {d : Prog} (hA : Admissible f d) : kcanon' (d.rename f) = kcanon' d
~~~

### 854. k_desugarProg_ren

Source: proofs/CANONF1.lean:575 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_desugarProg_ren (f : ℕ → ℕ) (p : Prog) : desugarProg (p.rename f) = (desugarProg p).rename f
~~~

### 855. k_adm_desugar

Source: proofs/CANONF1.lean:581 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_adm_desugar {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) : Admissible f (desugarProg p)
~~~

### 856. k_canon_step

Source: proofs/CANONF1.lean:590 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canon_step {p q : Prog} (h : Step p q) : canon p = canon q
~~~

### 857. k_canon_syn

Source: proofs/CANONF1.lean:599 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_canon_syn {p q : Prog} (h : SynEquiv p q) : canon p = canon q
~~~

### 858. k_eqv_map

Source: proofs/CANONF1.lean:608 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_map {φ : Stmt → Stmt} (hφ : ∀ a b, ForStep a b → ForStep (φ a) (φ b)) {a b : Stmt} (h : Relation.EqvGen ForStep a b) : Relation.EqvGen ForStep (φ a) (φ b)
~~~

### 859. k_eqv_seq

Source: proofs/CANONF1.lean:616 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_seq {s s' t t' : Stmt} (h1 : Relation.EqvGen ForStep s s') (h2 : Relation.EqvGen ForStep t t') : Relation.EqvGen ForStep (.seq s t) (.seq s' t')
~~~

### 860. k_eqv_ite

Source: proofs/CANONF1.lean:621 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_ite {b : BExp} {s s' t t' : Stmt} (h1 : Relation.EqvGen ForStep s s') (h2 : Relation.EqvGen ForStep t t') : Relation.EqvGen ForStep (.ite b s t) (.ite b s' t')
~~~

### 861. k_eqv_while

Source: proofs/CANONF1.lean:626 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_while {b : BExp} {s s' : Stmt} (h : Relation.EqvGen ForStep s s') : Relation.EqvGen ForStep (.while b s) (.while b s')
~~~

### 862. k_eqv_cfor

Source: proofs/CANONF1.lean:630 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_cfor {i i' : Stmt} {c : BExp} {st st' body body' : Stmt} (hi : Relation.EqvGen ForStep i i') (hst : Relation.EqvGen ForStep st st') (hb : Relation.EqvGen ForStep body body') : Relation.EqvGen ForStep (.cfor i c st body) (.cfor i' c st' body')
~~~

### 863. k_eqv_append

Source: proofs/CANONF1.lean:640 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_append (a b : Stmt) : Relation.EqvGen ForStep (.seq a b) (a.append b)
~~~

### 864. k_eqv_flatten

Source: proofs/CANONF1.lean:646 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_flatten (s : Stmt) : Relation.EqvGen ForStep s (flatten s)
~~~

### 865. k_eqv_desugar

Source: proofs/CANONF1.lean:655 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_desugar (s : Stmt) : Relation.EqvGen ForStep s (desugar s)
~~~

### 866. k_eqv_FF

Source: proofs/CANONF1.lean:666 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_eqv_FF (s : Stmt) : Relation.EqvGen ForStep s (KFF s)
~~~

### 867. k_lift

Source: proofs/CANONF1.lean:669 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_lift {k : ℕ} {ret : AExp} {body body' : Stmt} (h : Relation.EqvGen ForStep body body') : SynEquiv ⟨k, body, ret⟩ ⟨k, body', ret⟩
~~~

### 868. k_adm_canonMap

Source: proofs/CANONF1.lean:677 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_adm_canonMap (d : Prog) : Admissible d.canonMap d
~~~

### 869. k_syn_canon

Source: proofs/CANONF1.lean:693 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_syn_canon (p : Prog) : SynEquiv p (canon p)
~~~

### 870. k_part2

Source: proofs/CANONF1.lean:697 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_part2 (p q : Prog) : canon p = canon q ↔ SynEquiv p q
~~~

### 871. k_runs_step

Source: proofs/CANONF1.lean:705 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_runs_step {p q : Prog} (h : Step p q) (ins : List ℤ) (out : ℤ) : Runs p ins out ↔ Runs q ins out
~~~

### 872. k_runs_syn

Source: proofs/CANONF1.lean:714 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_runs_syn {p q : Prog} (h : SynEquiv p q) (ins : List ℤ) (out : ℤ) : Runs p ins out ↔ Runs q ins out
~~~

### 873. k_part1

Source: proofs/CANONF1.lean:722 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem k_part1 (p : Prog) (ins : List ℤ) (out : ℤ) : Runs (canon p) ins out ↔ Runs p ins out
~~~

### 874. claim

Source: proofs/CANONF1.lean:725 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 875. witness

Source: proofs/CANONF1.lean:741 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## proofs/SANDBOX2F1.lean

### 876. fp2_split1

Source: proofs/SANDBOX2F1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fp2_split1 (W : Path) (sd : List Path) : PL_SANDBOX2F1.fixedPolicy2 W sd = [.bind [] [] .ro] ++ ([.tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++ sd.map (fun d => .bind d d .rw) ++ hiddenDirs.map .tmpfs ++ [.bind mathlibProj mathlibProj .ro])
~~~

### 877. fp2_split2

Source: proofs/SANDBOX2F1.lean:10 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fp2_split2 (W : Path) (sd : List Path) : PL_SANDBOX2F1.fixedPolicy2 W sd = ([.bind [] [] .ro, .tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++ sd.map (fun d => .bind d d .rw)) ++ (hiddenDirs.map .tmpfs ++ [.bind mathlibProj mathlibProj .ro])
~~~

### 878. part_a

Source: proofs/SANDBOX2F1.lean:16 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_a : ∀ W : Path, ["var", "tmp"] <+: W → ReadsHost (fixedPolicy W [home ++ [".agent-b"]]) (home ++ [".agent-b", "sessions", "s.jsonl"]) (home ++ [".agent-b", "sessions", "s.jsonl"])
~~~

### 879. part_b

Source: proofs/SANDBOX2F1.lean:24 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_b : ∀ (W : Path) (stateDirs : List Path) (canWrite : Path → Prop) (p hp : Path), WritesHost (PL_SANDBOX2F1.fixedPolicy2 W stateDirs) canWrite p hp → W <+: hp ∨ ∃ d ∈ stateDirs, d <+: hp
~~~

### 880. part_c

Source: proofs/SANDBOX2F1.lean:34 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c : ∀ (W : Path) (stateDirs : List Path) (p hp H : Path), ["var", "tmp"] <+: W → H ∈ hiddenDirs → H <+: hp → ReadsHost (PL_SANDBOX2F1.fixedPolicy2 W stateDirs) p hp → mathlibProj <+: hp
~~~

### 881. claim

Source: proofs/SANDBOX2F1.lean:64 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_SANDBOX2F1.Claim
~~~

### 882. witness

Source: proofs/SANDBOX2F1.lean:66 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_SANDBOX2F1.Witness
~~~

## proofs/SANDBOXF1.lean

### 883. eff_mem

Source: proofs/SANDBOXF1.lean:1 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem eff_mem {pol : Policy} {p : Path} {m : Mount} (h : effective pol p = some m) : m ∈ pol ∧ m.tgt <+: p
~~~

### 884. eff_tail

Source: proofs/SANDBOXF1.lean:6 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem eff_tail {l1 l2 : Policy} {p : Path} {m x : Mount} (h : effective (l1 ++ l2) p = some m) (hx : x ∈ l2) (hP : x.tgt <+: p) : m ∈ l2
~~~

### 885. head_eq

Source: proofs/SANDBOXF1.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem head_eq {a b : String} {as bs l : Path} (h1 : a :: as <+: l) (h2 : b :: bs <+: l) : a = b
~~~

### 886. hidden_head

Source: proofs/SANDBOXF1.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hidden_head : ∀ H ∈ hiddenDirs, ∃ as, H = "home" :: as ∨ H = "tmp" :: as
~~~

### 887. cur_split

Source: proofs/SANDBOXF1.lean:33 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cur_split (W : Path) : currentPolicy W = [.bind [] [] .rw] ++ ([.tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++ hiddenDirs.map .tmpfs ++ [.bind mathlibProj mathlibProj .ro])
~~~

### 888. claim_a

Source: proofs/SANDBOXF1.lean:38 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_a : ∀ W : Path, ["var", "tmp"] <+: W → WritesHost (currentPolicy W) (fun hp => home <+: hp ∨ ["var", "tmp"] <+: hp) (home ++ [".toolchain", "bin", "lake"]) (home ++ [".toolchain", "bin", "lake"])
~~~

### 889. claim_b

Source: proofs/SANDBOXF1.lean:47 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_b : ∀ (W : Path) (stateDirs : List Path) (canWrite : Path → Prop) (p hp : Path), WritesHost (fixedPolicy W stateDirs) canWrite p hp → W <+: hp ∨ ∃ d ∈ stateDirs, d <+: hp
~~~

### 890. claim_c

Source: proofs/SANDBOXF1.lean:57 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_c : ∀ (W p hp H : Path), ["var", "tmp"] <+: W → H ∈ hiddenDirs → H <+: hp → ReadsHost (currentPolicy W) p hp → mathlibProj <+: hp
~~~

### 891. claim

Source: proofs/SANDBOXF1.lean:81 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 892. witness

Source: proofs/SANDBOXF1.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## proofs/TMCERTF1.lean

### 893. claimS

Source: proofs/TMCERTF1.lean:2 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimS : ∀ (S A Θ : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ) (σ : RHist S A → S → A → ℝ) (θ : ℕ → RHist S A → S → A → Θ), AdmKNonneg N G adm → RiskCertUpTo N G adm V → IsPolicy σ → SelectorUpTo N adm θ → ∀ n, n ≤ N → ∀ s h, risk G θ σ n s h ≤ V n s
~~~

### 894. claimP

Source: proofs/TMCERTF1.lean:29 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimP : ∀ (S A Θ : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (σ : RHist S A → S → A → ℝ) (θ : ℕ → RHist S A → S → A → Θ), (∀ n, n < N → ∀ s a th, adm n s a th → 0 ≤ (G th).cat n s a ∧ (∀ s', 0 ≤ (G th).K n s a s') ∧ (G th).cat n s a + ∑ s', (G th).K n s a s' ≤ 1) → IsPolicy σ → SelectorUpTo N adm θ → ∀ n, n ≤ N → ∀ s h, 0 ≤ risk G θ σ n s h ∧ risk G θ σ n s h ≤ 1
~~~

### 895. claimS

Source: proofs/TMCERTF1.lean:63 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimS' : ∀ (S A Θ Ω : Type) [Fintype S] [Fintype A] [Fintype Ω] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ) (ρ : Ω → ℝ) (σ : Ω → RHist S A → S → A → ℝ) (θ : Ω → ℕ → RHist S A → S → A → Θ) (s₀ : S), AdmKNonneg N G adm → RiskCertUpTo N G adm V → (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, IsPolicy (σ ω)) → (∀ ω, SelectorUpTo N adm (θ ω)) → ∑ ω, ρ ω * risk G (θ ω) (σ ω) N s₀ [] ≤ V N s₀
~~~

### 896. claimFx

Source: proofs/TMCERTF1.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimFx : ∀ (S A : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Game S A) (V : ℕ → S → ℝ) (σ : RHist S A → S → A → ℝ) (s₀ : S), (∀ n, n < N → ∀ s a s', 0 ≤ G.K n s a s') → RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V → IsPolicy σ → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ N s₀ [] ≤ V N s₀
~~~

### 897. claimFxGap

Source: proofs/TMCERTF1.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimFxGap : risk (fun _ : Unit => gapG true) (fun _ _ _ _ => ()) (fun _ _ _ => 1) 2 () [] = 1/2 ∧ risk (fun _ : Unit => gapG false) (fun _ _ _ _ => ()) (fun _ _ _ => 1) 2 () [] = 1/2 ∧ risk gapG (fun n _ _ _ => decide (n = 1)) (fun _ _ _ => 1) 2 () [] = 3/4
~~~

### 898. claimObs

Source: proofs/TMCERTF1.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimObs : ∀ (S A O : Type) [Fintype A] (obs : RHist S A → S → O) (π : O → A → ℝ), (∀ o, (∀ a, 0 ≤ π o a) ∧ ∑ a, π o a = 1) → IsPolicy (liftObs obs π)
~~~

### 899. claimT

Source: proofs/TMCERTF1.lean:97 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimT : ∀ (S A : Type) [Fintype S] [Fintype A] [Nonempty A] (G : Game S A), Lawful G → (∀ N, RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) (Vstar G)) ∧ (∀ N V, RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V → ∀ n, n ≤ N → ∀ s, Vstar G n s ≤ V n s) ∧ (∀ n s, 0 ≤ Vstar G n s ∧ Vstar G n s ≤ 1) ∧ ∀ (N : ℕ) (s₀ : S), ∃ σ, IsPolicy σ ∧ (∀ h s a, σ h s a = 0 ∨ σ h s a = 1) ∧ (∀ h h' s, h.length = h'.length → σ h s = σ h' s) ∧ risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ N s₀ [] = Vstar G N s₀
~~~

### 900. claimTR

Source: proofs/TMCERTF1.lean:192 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimTR : ∀ (S A Θ : Type) [Fintype S] [Fintype A] [Fintype Θ] [Nonempty A] [Nonempty Θ] (G : Θ → Game S A), (∀ th, Lawful (G th)) → (∀ N, RiskCertUpTo N G (fun _ _ _ _ => True) (Vrob G)) ∧ (∀ N V, RiskCertUpTo N G (fun _ _ _ _ => True) V → ∀ n, n ≤ N → ∀ s, Vrob G n s ≤ V n s) ∧ ∀ (N : ℕ) (s₀ : S), ∃ σ θ, IsPolicy σ ∧ (∀ h s a, σ h s a = 0 ∨ σ h s a = 1) ∧ (∀ h h' s, h.length = h'.length → σ h s = σ h' s) ∧ (∀ n h h' s a, h.length = h'.length → θ n h s a = θ n h' s a) ∧ risk G θ σ N s₀ [] = Vrob G N s₀
~~~

### 901. claimU

Source: proofs/TMCERTF1.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimU : ∀ (S A Θ : Type) [Fintype S] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (a₀ : A) (rew : Θ → ℕ → S → ℝ) (W : ℕ → S → ℝ) (θ : ℕ → RHist S A → S → Θ), (∀ n, n < N → ∀ s th, adm n s a₀ th → ∀ s', 0 ≤ (G th).K n s a₀ s') → UseCertUpTo N G adm a₀ rew W → (∀ n, n < N → ∀ h s, adm n s a₀ (θ n h s)) → ∀ n, n ≤ N → ∀ s h, W n s ≤ honestER G a₀ rew θ n s h
~~~

### 902. foldl_add_eq

Source: proofs/TMCERTF1.lean:288 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_add_eq {m : ℕ} (f : Fin m → ℚ) : ∀ (l : List (Fin m)) (acc : ℚ), l.foldl (fun acc i => acc + f i) acc = acc + (l.map f).sum
~~~

### 903. sumQ_eq

Source: proofs/TMCERTF1.lean:298 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sumQ_eq (m : ℕ) (f : Fin m → ℚ) : sumQ m f = ∑ i, f i
~~~

### 904. checkRiskQ_spec

Source: proofs/TMCERTF1.lean:301 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkRiskQ_spec {N m k t : ℕ} {cat : Fin t → Fin N → Fin m → Fin k → ℚ} {K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ} {V : Fin (N + 1) → Fin m → ℚ} (hc : checkRiskQ N m k t cat K V = true) : 0 < t ∧ 0 < k ∧ (∀ j s, 0 ≤ V j s) ∧ (∀ th i s a, cat th i s a + ∑ s', K th i s a s' * V i.castSucc s' ≤ V i.succ s)
~~~

### 905. checkLawfulQ_spec

Source: proofs/TMCERTF1.lean:310 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkLawfulQ_spec {N m k t : ℕ} {cat : Fin t → Fin N → Fin m → Fin k → ℚ} {K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ} (hc : checkLawfulQ N m k t cat K = true) : ∀ th i s a, 0 ≤ cat th i s a ∧ (∀ s', 0 ≤ K th i s a s') ∧ cat th i s a + ∑ s', K th i s a s' ≤ 1
~~~

### 906. claimQ

Source: proofs/TMCERTF1.lean:319 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimQ : ∀ (N m k t : ℕ) (cat : Fin t → Fin N → Fin m → Fin k → ℚ) (K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ) (V : Fin (N + 1) → Fin m → ℚ), (checkRiskQ N m k t cat K V = true → RiskCertUpTo N (gameOfQ N m k t cat K) (fun _ _ _ _ => True) (valOfQ N m V) ∧ (∀ n s, 0 ≤ valOfQ N m V n s) ∧ 0 < t ∧ 0 < k) ∧ (checkLawfulQ N m k t cat K = true → ∀ th, Lawful (gameOfQ N m k t cat K th))
~~~

### 907. claimVx

Source: proofs/TMCERTF1.lean:350 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimVx : ∀ (S A ι : Type) [Fintype S] [Fintype ι] (N : ℕ) (Gv : ι → Game S A) (V : ℕ → S → ℝ), RiskCertUpTo N Gv (fun _ _ _ _ => True) V → RiskCertUpTo N (hullGame Gv) (fun _ _ _ lam => Simplex lam) V ∧ ((∀ i n s a s', 0 ≤ (Gv i).K n s a s') → ∀ n s a lam, Simplex lam → ∀ s', 0 ≤ (hullGame Gv lam).K n s a s')
~~~

### 908. claimAbsV

Source: proofs/TMCERTF1.lean:374 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimAbsV : ∀ (Sc Ac S A Θ : Type) [Fintype Sc] [Fintype Ac] [Fintype S] (N : ℕ) (Gc : Game Sc Ac) (α : Sc → S) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ) (σc : RHist Sc Ac → Sc → Ac → ℝ), (∀ n, n < N → ∀ x ac x', 0 ≤ Gc.K n x ac x') → CoveredV N Gc α G adm V → RiskCertUpTo N G adm V → IsPolicy σc → ∀ n, n ≤ N → ∀ x h, risk (fun _ : Unit => Gc) (fun _ _ _ _ => ()) σc n x h ≤ V n (α x)
~~~

### 909. claimAbsEq

Source: proofs/TMCERTF1.lean:400 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claimAbsEq : ∀ (Sc Ac S A Θ : Type) [Fintype Sc] [Fintype S] [DecidableEq S] (N : ℕ) (Gc : Game Sc Ac) (α : Sc → S) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ), Covered N Gc α G adm → CoveredV N Gc α G adm V
~~~

### 910. claim

Source: proofs/TMCERTF1.lean:417 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_TMCERTF1.Claim
~~~

### 911. witness

Source: proofs/TMCERTF1.lean:421 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_TMCERTF1.Witness
~~~

## proofs/TMCERTUSF1.lean

### 912. foldl_add_eq

Source: proofs/TMCERTUSF1.lean:1 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem foldl_add_eq {m : ℕ} (f : Fin m → ℚ) : ∀ (l : List (Fin m)) (acc : ℚ), l.foldl (fun acc i => acc + f i) acc = acc + (l.map f).sum
~~~

### 913. sumQ_eq

Source: proofs/TMCERTUSF1.lean:8 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sumQ_eq (m : ℕ) (f : Fin m → ℚ) : sumQ m f = ∑ i, f i
~~~

### 914. checkUseQ_spec

Source: proofs/TMCERTUSF1.lean:11 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkUseQ_spec {N m t : ℕ} {rew : Fin t → Fin N → Fin m → ℚ} {K : Fin t → Fin N → Fin m → Fin m → ℚ} {adm : Fin t → Fin N → Fin m → Bool} {W : Fin (N + 1) → Fin m → ℚ} {s₀ : Fin m} {floor : ℚ} (hc : checkUseQ N m t rew K adm W s₀ floor = true) : 0 < t ∧ floor ≤ W (Fin.last N) s₀ ∧ (∀ s, W 0 s ≤ 0) ∧ (∀ i s, ∃ th, adm th i s = true) ∧ (∀ th i s, adm th i s = true → W i.succ s ≤ rew th i s + ∑ s', K th i s s' * W i.castSucc s')
~~~

### 915. selector_exists

Source: proofs/TMCERTUSF1.lean:29 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem selector_exists {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ) (K : Fin t → Fin N → Fin m → Fin m → ℚ) (adm : Fin t → Fin N → Fin m → Bool) (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ) (hc : checkUseQ N m t rew K adm W s₀ floor = true) : ∃ θ : ℕ → List (Fin m) → Fin m → Fin t, ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true
~~~

### 916. checkUseQ_sound

Source: proofs/TMCERTUSF1.lean:45 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem checkUseQ_sound {N m t : ℕ} (rew : Fin t → Fin N → Fin m → ℚ) (K : Fin t → Fin N → Fin m → Fin m → ℚ) (adm : Fin t → Fin N → Fin m → Bool) (W : Fin (N + 1) → Fin m → ℚ) (s₀ : Fin m) (floor : ℚ) (θ : ℕ → List (Fin m) → Fin m → Fin t) (hc : checkUseQ N m t rew K adm W s₀ floor = true) (hK : ∀ th i s, adm th i s = true → ∀ s', 0 ≤ K th i s s') (hθ : ∀ n (hn : n < N) h s, adm (θ n h s) ⟨n, hn⟩ s = true) : (floor : ℝ) ≤ PL_TMCERTUSF1.honestValue rew K θ N s₀ []
~~~

### 917. claim

Source: proofs/TMCERTUSF1.lean:98 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_TMCERTUSF1.Claim
~~~

### 918. witness

Source: proofs/TMCERTUSF1.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_TMCERTUSF1.Witness
~~~

## proofs/TMGACF1.lean

### 919. risk_zero

Source: proofs/TMGACF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_zero' {S A Θ : Type} [Fintype S] [Fintype A] (G : Θ → Game S A) (θ : ℕ → RHist S A → S → A → Θ) (σ : RHist S A → S → A → ℝ) (s : S) (h : RHist S A) : risk G θ σ 0 s h = 0
~~~

### 920. risk_succ_bool

Source: proofs/TMGACF1.lean:10 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_succ_bool {S : Type} [Fintype S] (G : Game S Bool) (σ : RHist S Bool → S → Bool → ℝ) (n : ℕ) (s : S) (h : RHist S Bool) : risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ (n + 1) s h = σ h s true * (G.cat n s true + ∑ s', G.K n s true s' * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' (h ++ [(s, true)])) + σ h s false * (G.cat n s false + ∑ s', G.K n s false s' * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' (h ++ [(s, false)]))
~~~

### 921. risk_hist

Source: proofs/TMGACF1.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_hist {S A : Type} [Fintype S] [Fintype A] (G : Game S A) (σ : RHist S A → S → A → ℝ) (hσ : ∀ h s a, σ h s a = σ [] s a) : ∀ n s h, risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s h = risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s []
~~~

### 922. risk_succ_hf

Source: proofs/TMGACF1.lean:35 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_succ_hf {S : Type} [Fintype S] (G : Game S Bool) (σ : RHist S Bool → S → Bool → ℝ) (hσ : ∀ h s a, σ h s a = σ [] s a) (n : ℕ) (s : S) (h : RHist S Bool) : risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ (n + 1) s h = σ [] s true * (G.cat n s true + ∑ s', G.K n s true s' * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' []) + σ [] s false * (G.cat n s false + ∑ s', G.K n s false s' * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' [])
~~~

### 923. honestER_hist

Source: proofs/TMGACF1.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honestER_hist {S A : Type} [Fintype S] (G : Game S A) (a₀ : A) (rew : Unit → ℕ → S → ℝ) : ∀ n s h, honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) n s h = honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) n s []
~~~

### 924. honestER_succ_hf

Source: proofs/TMGACF1.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem honestER_succ_hf {S A : Type} [Fintype S] (G : Game S A) (a₀ : A) (rew : Unit → ℕ → S → ℝ) (n : ℕ) (s : S) (h : RHist S A) : honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) (n + 1) s h = rew () n s + ∑ s', G.K n s a₀ s' * honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) n s' []
~~~

### 925. sup'_bool

Source: proofs/TMGACF1.lean:69 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sup'_bool (g : Bool → ℝ) : (Finset.univ : Finset Bool).sup' Finset.univ_nonempty g = max (g true) (g false)
~~~

### 926. Vstar_succ_bool

Source: proofs/TMGACF1.lean:79 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Vstar_succ_bool {S : Type} [Fintype S] (G : Game S Bool) (n : ℕ) (s : S) : Vstar G (n + 1) s = max (G.cat n s true + ∑ s', G.K n s true s' * Vstar G n s') (G.cat n s false + ∑ s', G.K n s false s' * Vstar G n s')
~~~

### 927. constRed_t

Source: proofs/TMGACF1.lean:84 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem constRed_t {S : Type} (β : ℝ) (h : RHist S Bool) (s : S) : constRed β h s true = β
~~~

### 928. constRed_f

Source: proofs/TMGACF1.lean:85 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem constRed_f {S : Type} (β : ℝ) (h : RHist S Bool) (s : S) : constRed β h s false = 1 - β
~~~

### 929. gac_cat_true

Source: proofs/TMGACF1.lean:89 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_cat_true (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) : (gac C TA TD FA).cat n c true = (if 0 < c.val then 1 - TD n c.val else 1 - TD n c.val + TA n c.val)
~~~

### 930. gac_cat_false

Source: proofs/TMGACF1.lean:93 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_cat_false (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) : (gac C TA TD FA).cat n c false = 0
~~~

### 931. gac_sum_true

Source: proofs/TMGACF1.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_sum_true (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) (F : Fin (C + 1) → ℝ) : ∑ c', (gac C TA TD FA).K n c true c' * F c' = (TD n c.val - TA n c.val) * F c
~~~

### 932. gac_sum_false_zero

Source: proofs/TMGACF1.lean:100 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_sum_false_zero (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) (hc : c.val = 0) (F : Fin (C + 1) → ℝ) : ∑ c', (gac C TA TD FA).K n c false c' * F c' = F c
~~~

### 933. gac_sum_false_succ

Source: proofs/TMGACF1.lean:110 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gac_sum_false_succ (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n k : ℕ) (hk : k + 1 < C + 1) (F : Fin (C + 1) → ℝ) : ∑ c', (gac C TA TD FA).K n ⟨k + 1, hk⟩ false c' * F c' = FA n (k + 1) * F ⟨k, by omega⟩ + (1 - FA n (k + 1)) * F ⟨k + 1, hk⟩
~~~

### 934. conjL

Source: proofs/TMGACF1.lean:130 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjL : ∀ (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ), (∀ n c, 0 ≤ TA n c ∧ TA n c ≤ TD n c ∧ TD n c ≤ 1 ∧ 0 ≤ FA n c ∧ FA n c ≤ 1) → Lawful (gac C TA TD FA)
~~~

### 935. conjLQ

Source: proofs/TMGACF1.lean:159 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjLQ : ∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ), (∀ m c, 0 ≤ qa m c ∧ qa m c ≤ qd m c ∧ qd m c ≤ 1 ∧ 0 ≤ f (qa m c) ∧ f (qa m c) ≤ f (qd m c) ∧ f (qd m c) ≤ 1) → Lawful (gacQ C f qa qd)
~~~

### 936. conjZ

Source: proofs/TMGACF1.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjZ : ∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (β : ℝ), f 0 = 0 → (∀ m, qa m 0 = 0) → ∀ (m : ℕ) (c : Fin (C + 1)), 1 - risk (fun _ : Unit => gacQ C f qa qd) (fun _ _ _ _ => ()) (constRed β) m c [] = zGAC f qa qd β m c.val
~~~

### 937. conjUZ

Source: proofs/TMGACF1.lean:201 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjUZ : ∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (m : ℕ) (c : Fin (C + 1)), honestER (fun _ : Unit => gacQ C f qa qd) false (fun _ n c => usedReward qa qd n c.val) (fun _ _ _ => ()) m c [] = uGAC qa qd m c.val
~~~

### 938. conjM

Source: proofs/TMGACF1.lean:226 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjM : ∀ (S Ω : Type) [Fintype S] [Fintype Ω] (G : Game S Bool) (ρ : Ω → ℝ) (β : Ω → ℝ) (N : ℕ) (s₀ : S) (U : ℝ), (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, 0 ≤ β ω ∧ β ω ≤ 1) → (∀ b : ℝ, 0 ≤ b → b ≤ 1 → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] ≤ U) → ∑ ω, ρ ω * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed (β ω)) N s₀ [] ≤ U
~~~

### 939. rowval_bounds

Source: proofs/TMGACF1.lean:239 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rowval_bounds {S : Type} [Fintype S] (G : Game S Bool) (hG : Lawful G) (n : ℕ) (s : S) (a : Bool) (F : S → ℝ) (hF : ∀ s, 0 ≤ F s ∧ F s ≤ 1) : 0 ≤ G.cat n s a + ∑ s', G.K n s a s' * F s' ∧ G.cat n s a + ∑ s', G.K n s a s' * F s' ≤ 1
~~~

### 940. risk_const_bounds

Source: proofs/TMGACF1.lean:251 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem risk_const_bounds {S : Type} [Fintype S] (G : Game S Bool) (hG : Lawful G) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : ∀ n s, 0 ≤ risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) n s [] ∧ risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) n s [] ≤ 1
~~~

### 941. rowval_diff

Source: proofs/TMGACF1.lean:267 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rowval_diff {S : Type} [Fintype S] (G : Game S Bool) (hG : Lawful G) (n : ℕ) (s : S) (a : Bool) (F1 F2 : S → ℝ) (e : ℝ) (he : 0 ≤ e) (hF : ∀ s, |F1 s - F2 s| ≤ e) : |(G.cat n s a + ∑ s', G.K n s a s' * F1 s') - (G.cat n s a + ∑ s', G.K n s a s' * F2 s')| ≤ e
~~~

### 942. lip_comb

Source: proofs/TMGACF1.lean:286 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem lip_comb (b b' X Y X' Y' e : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hX0 : 0 ≤ X') (hX1 : X' ≤ 1) (hY0 : 0 ≤ Y') (hY1 : Y' ≤ 1) (hXX : |X - X'| ≤ e) (hYY : |Y - Y'| ≤ e) : |b * X + (1 - b) * Y - (b' * X' + (1 - b') * Y')| ≤ e + |b - b'|
~~~

### 943. conjLip

Source: proofs/TMGACF1.lean:303 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjLip : ∀ (S : Type) [Fintype S] (G : Game S Bool) (N : ℕ) (s₀ : S) (b b' : ℝ), Lawful G → 0 ≤ b → b ≤ 1 → 0 ≤ b' → b' ≤ 1 → |risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] - risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b') N s₀ []| ≤ N * |b - b'|
~~~

### 944. conjGrid

Source: proofs/TMGACF1.lean:329 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjGrid : ∀ (S : Type) [Fintype S] (G : Game S Bool) (N J : ℕ) (s₀ : S) (U : ℝ), Lawful G → 0 < J → (∀ j : ℕ, j ≤ J → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed ((j : ℝ) / J)) N s₀ [] ≤ U) → ∀ b : ℝ, 0 ≤ b → b ≤ 1 → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] ≤ U + N / (2 * J)
~~~

### 945. Vstar_zero

Source: proofs/TMGACF1.lean:364 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Vstar_zero' {S A : Type} [Fintype S] [Fintype A] [Nonempty A] (G : Game S A) (s : S) : Vstar G 0 s = 0
~~~

### 946. conjW

Source: proofs/TMGACF1.lean:368 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjW : ∀ (TA TD FA : ℕ → ℕ → ℝ), (∀ n c, 0 ≤ TA n c ∧ TA n c ≤ TD n c ∧ TD n c ≤ 1 ∧ 0 ≤ FA n c ∧ FA n c ≤ 1) → ∀ (N : ℕ) (c : Fin 1), risk (fun _ : Unit => gac 0 TA TD FA) (fun _ _ _ _ => ()) (constRed 1) N c [] = Vstar (gac 0 TA TD FA) N c
~~~

### 947. ex_row0t

Source: proofs/TMGACF1.lean:399 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_row0t (n : ℕ) (F : Fin 2 → ℝ) : exG3.cat n 0 true + ∑ s', exG3.K n 0 true s' * F s' = 1/4 + 3/4 * F 0
~~~

### 948. ex_row0f

Source: proofs/TMGACF1.lean:404 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_row0f (n : ℕ) (F : Fin 2 → ℝ) : exG3.cat n 0 false + ∑ s', exG3.K n 0 false s' * F s' = F 0
~~~

### 949. ex_row1t

Source: proofs/TMGACF1.lean:408 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_row1t (n : ℕ) (F : Fin 2 → ℝ) : exG3.cat n 1 true + ∑ s', exG3.K n 1 true s' * F s' = 1/4
~~~

### 950. ex_row1f

Source: proofs/TMGACF1.lean:413 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_row1f (n : ℕ) (F : Fin 2 → ℝ) : exG3.cat n 1 false + ∑ s', exG3.K n 1 false s' * F s' = 1/2 * F 0 + 1/2 * F 1
~~~

### 951. ex_step0

Source: proofs/TMGACF1.lean:418 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_step0 (σ : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ) (n : ℕ) (h : RHist (Fin 2) Bool) : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ (n + 1) 0 h = σ h 0 true * (1/4 + 3/4 * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 0 (h ++ [(0, true)])) + σ h 0 false * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 0 (h ++ [(0, false)])
~~~

### 952. ex_step1

Source: proofs/TMGACF1.lean:424 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_step1 (σ : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ) (n : ℕ) (h : RHist (Fin 2) Bool) : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ (n + 1) 1 h = σ h 1 true * (1/4) + σ h 1 false * (1/2 * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 0 (h ++ [(1, false)]) + 1/2 * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 1 (h ++ [(1, false)]))
~~~

### 953. ex_V0

Source: proofs/TMGACF1.lean:431 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_V0 (n : ℕ) : Vstar exG3 (n + 1) 0 = max (1/4 + 3/4 * Vstar exG3 n 0) (Vstar exG3 n 0)
~~~

### 954. ex_V1

Source: proofs/TMGACF1.lean:434 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_V1 (n : ℕ) : Vstar exG3 (n + 1) 1 = max (1/4) (1/2 * Vstar exG3 n 0 + 1/2 * Vstar exG3 n 1)
~~~

### 955. ex_poly

Source: proofs/TMGACF1.lean:438 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_poly (b : ℝ) : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed b) 3 1 [] = 3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3
~~~

### 956. ex_clocked

Source: proofs/TMGACF1.lean:444 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_clocked : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) clocked3 3 1 [] = 11/32
~~~

### 957. ex_coin

Source: proofs/TMGACF1.lean:448 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_coin : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) coinRed 3 1 [] = 9/32
~~~

### 958. ex_Vstar

Source: proofs/TMGACF1.lean:452 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ex_Vstar : Vstar exG3 3 1 = 11/32
~~~

### 959. conjT5

Source: proofs/TMGACF1.lean:463 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conjT5 : (∀ b : ℝ, 0 ≤ b → b ≤ 1 → risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed b) 3 1 [] = 3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3 ∧ 3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3 ≤ 13/50) ∧ risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed (4/5)) 3 1 [] = 13/50 ∧ IsPolicy clocked3 ∧ IsPolicy coinRed ∧ risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) coinRed 3 1 [] = 9/32 ∧ (13/50 : ℝ) < 9/32 ∧ risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) clocked3 3 1 [] = 11/32 ∧ Vstar exG3 3 1 = 11/32 ∧ (13/50 : ℝ) < 11/32
~~~

### 960. sound_unit

Source: proofs/TMGACF1.lean:497 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sound_unit {S A : Type} [Fintype S] [Fintype A] (G : Game S A) (N : ℕ) (V : ℕ → S → ℝ) (σ : RHist S A → S → A → ℝ) (hK : ∀ n, n < N → ∀ s a s', 0 ≤ G.K n s a s') (hV : RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V) (hσ : IsPolicy σ) : ∀ n, n ≤ N → ∀ s h, risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s h ≤ V n s
~~~

### 961. claim

Source: proofs/TMGACF1.lean:516 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_TMGACF1.Claim
~~~

### 962. witness

Source: proofs/TMGACF1.lean:519 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_TMGACF1.Witness
~~~

## proofs/TMLIPF1.lean

### 963. oneStep

Source: proofs/TMLIPF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem oneStep : OneStep
~~~

### 964. transfer

Source: proofs/TMLIPF1.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem transfer : Transfer
~~~

### 965. gridTransfer

Source: proofs/TMLIPF1.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gridTransfer : GridTransfer
~~~

### 966. gridRisk

Source: proofs/TMLIPF1.lean:125 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem gridRisk : GridRisk
~~~

### 967. claim

Source: proofs/TMLIPF1.lean:132 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_TMLIPF1.Claim
~~~

### 968. w_lawfulParam

Source: proofs/TMLIPF1.lean:134 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_lawfulParam : ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), LawfulUpTo 1 (paramGame p)
~~~

### 969. w_cover

Source: proofs/TMLIPF1.lean:141 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_cover : ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ q ∈ pGrid, |p - q| ≤ 1 / 8
~~~

### 970. w_lip

Source: proofs/TMLIPF1.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_lip : ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ q ∈ pGrid, RowClose 1 (paramGame q) (paramGame p) (2 * |p - q|)
~~~

### 971. w_gridCert

Source: proofs/TMLIPF1.lean:157 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_gridCert : ∀ q ∈ pGrid, RiskCertUpTo 1 (fun _ : Unit => paramGame q) (fun _ _ _ _ => True) (gridCert q) ∧ InRange 1 (gridCert q) ∧ ∀ s, gridCert q 1 s ≤ 3 / 8
~~~

### 972. witness

Source: proofs/TMLIPF1.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_TMLIPF1.Witness
~~~

## proofs/UMADAPTF1.lean

### 973. adSurv_zero

Source: proofs/UMADAPTF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_zero' {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (h : Hist X Z) : adSurv T M φ keep 0 h = keep h
~~~

### 974. adSurv_succ

Source: proofs/UMADAPTF1.lean:10 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_succ' {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ) (h : Hist X Z) : adSurv T M φ keep (n + 1) h = ∑ x, T h x * ∑ z, M x z * (φ z * adSurv T M φ keep n (h ++ [(x, z, true)]) + (1 - φ z) * adSurv T M φ keep n (h ++ [(x, z, false)]))
~~~

### 975. s_aux

Source: proofs/UMADAPTF1.lean:18 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem s_aux {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hk : ∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) : ∀ (n : ℕ) (h : Hist X Z), (∀ e ∈ h, e.2.2 = false) → adSurv T M (fun _ => 0) keep n h = 1
~~~

### 976. part_s

Source: proofs/UMADAPTF1.lean:39 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_s : ∀ (X Z : Type) [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ), IsKernel M → (∀ h, IsDist (T h)) → (∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) → AcceptsAllFlag T M keep n
~~~

### 977. surv_bounds

Source: proofs/UMADAPTF1.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_bounds {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hφ : IsRule φ) (hk : ∀ h, 0 ≤ keep h ∧ keep h ≤ 1) : ∀ (n : ℕ) (h : Hist X Z), 0 ≤ adSurv T M φ keep n h ∧ adSurv T M φ keep n h ≤ 1
~~~

### 978. Qf_zero

Source: proofs/UMADAPTF1.lean:83 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_zero {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (h : Hist X Z) : Qf T M w 0 h = 0
~~~

### 979. Qf_succ

Source: proofs/UMADAPTF1.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_succ {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (n : ℕ) (h : Hist X Z) : Qf T M w (n + 1) h = ∑ x, T h x * ∑ z, M x z * (w z + Qf T M w n (h ++ [(x, z, false)]))
~~~

### 980. Qf_nonneg

Source: proofs/UMADAPTF1.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_nonneg {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hw : ∀ z, 0 ≤ w z) : ∀ (n : ℕ) (h : Hist X Z), 0 ≤ Qf T M w n h
~~~

### 981. sum2_add

Source: proofs/UMADAPTF1.lean:105 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum2_add {X Z : Type} [Fintype X] [Fintype Z] (a : X → ℝ) (m : X → Z → ℝ) (f g : X → Z → ℝ) (t : ℝ) : ∑ x, a x * ∑ z, m x z * f x z + t * ∑ x, a x * ∑ z, m x z * g x z = ∑ x, a x * ∑ z, m x z * (f x z + t * g x z)
~~~

### 982. ref_lb

Source: proofs/UMADAPTF1.lean:116 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ref_lb {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ w : Z → ℝ) (t : ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hk : ∀ h, 0 ≤ keep h ∧ keep h ≤ 1) (hφ : IsRule φ) (hw : ∀ z, 0 ≤ w z) (ht : 0 ≤ t) (hφw : ∀ z, φ z ≤ t * w z) : ∀ (n : ℕ) (h : Hist X Z), adSurv T M (fun _ => 0) keep n h - t * Qf T M w n h ≤ adSurv T M φ keep n h
~~~

### 983. Q_sum_le

Source: proofs/UMADAPTF1.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Q_sum_le {X Z Ω : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (S : Finset Ω) (w : Ω → Z → ℝ) (hw1 : ∀ z, ∑ ω ∈ S, w ω z ≤ 1) : ∀ (n : ℕ) (h : Hist X Z), ∑ ω ∈ S, Qf T M (w ω) n h ≤ n
~~~

### 984. ind_sum_le

Source: proofs/UMADAPTF1.lean:172 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ind_sum_le {X Z C : Type} [DecidableEq C] (c : X → C) (g : Z → C) (S : Finset X) (hinj : Set.InjOn c (S : Set X)) (z : Z) : ∑ ω ∈ S, (if g z = c ω then (1 : ℝ) else 0) ≤ 1
~~~

### 985. classRule_rule

Source: proofs/UMADAPTF1.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classRule_rule {X Z C : Type} [DecidableEq C] (c : X → C) (g : Z → C) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ω : X) : IsRule (classRule c g t ω)
~~~

### 986. conv_a

Source: proofs/UMADAPTF1.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conv_a {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X) (hM : IsKernel M) (hbad : ∀ x ∈ S, Bad x) (hinj : Set.InjOn c (S : Set X)) (hS : 0 < S.card) (g : Z → C) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ) (hTk : AdTester T keep) (hacc : AcceptsAllFlag T M keep n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (r : ℝ) (b N : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hN : 1 ≤ N) : t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z
~~~

### 987. opt_arith

Source: proofs/UMADAPTF1.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem opt_arith (k n : ℝ) (hk : 0 < k) (hn : 1 ≤ n) : min (1 / 2) (k / (4 * n)) ≤ min 1 (k / (2 * n)) * max 0 (1 - min 1 (k / (2 * n)) * n / k)
~~~

### 988. part_a

Source: proofs/UMADAPTF1.lean:288 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_a : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X), Setup Bad M c S → ∃ g : Z → C, (∀ x z, M x z ≠ 0 → g z = c x) ∧ (∀ (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ), AdTester T keep → AcceptsAllFlag T M keep n → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N → t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z
~~~

### 989. adSurv_det

Source: proofs/UMADAPTF1.lean:321 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_det {X : Type} [Fintype X] [DecidableEq X] (T : Hist X X → X → ℝ) (M : X → X → ℝ) (q : Hist X X → X) (hT : ∀ h x, T h x = if x = q h then 1 else 0) (hM : ∀ x z, M x z = if z = x then 1 else 0) (φ : X → ℝ) (keep : Hist X X → ℝ) (n : ℕ) (h : Hist X X) : adSurv T M φ keep (n + 1) h = φ (q h) * adSurv T M φ keep n (h ++ [(q h, q h, true)]) + (1 - φ (q h)) * adSurv T M φ keep n (h ++ [(q h, q h, false)])
~~~

### 990. cat_id1

Source: proofs/UMADAPTF1.lean:331 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_id1 {X : Type} [Fintype X] [DecidableEq X] (M : X → X → ℝ) (hM : ∀ x z, M x z = if z = x then 1 else 0) (φ : X → ℝ) (ω : X) : cat (fun _ : X => True) M φ (seedPolicy (Z
~~~

### 991. det_dist

Source: proofs/UMADAPTF1.lean:336 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem det_dist {X : Type} [Fintype X] [DecidableEq X] (y : X) : IsDist (fun x : X => if x = y then (1 : ℝ) else 0)
~~~

### 992. keep01

Source: proofs/UMADAPTF1.lean:342 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem keep01 (P : Prop) [Decidable P] : 0 ≤ (if P then (1 : ℝ) else 0) ∧ (if P then (1 : ℝ) else 0) ≤ 1
~~~

### 993. setup_id

Source: proofs/UMADAPTF1.lean:346 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem setup_id {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] (M : X → X → ℝ) (hM : ∀ x z, M x z = if z = x then 1 else 0) : Setup (fun _ : X => True) M id (univ : Finset X)
~~~

### 994. misses_allflag

Source: proofs/UMADAPTF1.lean:359 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem misses_allflag {X Z : Type} (h : Hist X Z) (hh : ∀ e ∈ h, e.2.2 = false) : misses h = 0
~~~

### 995. c1_surv

Source: proofs/UMADAPTF1.lean:366 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c1_surv (t : ℝ) (ω : Bool) : adSurv ctrT idM (classRule id id t ω) ctrKeep 3 [] = if ω then 1 - t ^ 2 else (1 - t) + t * (1 - t) ^ 2
~~~

### 996. c1_risk

Source: proofs/UMADAPTF1.lean:372 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c1_risk (t : ℝ) : adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool)) (classRule id id t) (seedPolicy (Z
~~~

### 997. c2_surv

Source: proofs/UMADAPTF1.lean:383 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_surv (t : ℝ) (ω : Fin 3) : adSurv stT idM3 (classRule id id t ω) stKeep 3 [] = if ω = 0 then (1 - t) + t * (1 - t) ^ 2 else if ω = 1 then 1 - t ^ 2 else 1
~~~

### 998. c2_risk

Source: proofs/UMADAPTF1.lean:389 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_risk (t : ℝ) : adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3))) (classRule id id t) (seedPolicy (Z
~~~

### 999. c2_bound

Source: proofs/UMADAPTF1.lean:400 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t - t ^ 3 + t ^ 4 / 3 < 1 / 2
~~~

### 1000. w_surv

Source: proofs/UMADAPTF1.lean:404 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_surv (t : ℝ) (ω : Bool) : adSurv wT idM (classRule id id t ω) wKeep 1 [] = if ω then 1 else 1 - t
~~~

### 1001. wbad_surv

Source: proofs/UMADAPTF1.lean:409 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wbad_surv (t : ℝ) (ω : Bool) : adSurv wT idM (classRule id id t ω) wKeepBad 1 [] = if ω then 0 else t
~~~

### 1002. part_c1

Source: proofs/UMADAPTF1.lean:414 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c1 : (Setup (fun _ : Bool => True) idM id (univ : Finset Bool) ∧ AdTester ctrT ctrKeep ∧ AcceptsAllFlag ctrT idM ctrKeep 3 ∧ (∀ h : Hist Bool Bool, misses h ≤ 1 → ctrKeep h = 1) ∧ adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool)) (classRule id id (3/4)) (seedPolicy (Z
~~~

### 1003. part_c2

Source: proofs/UMADAPTF1.lean:439 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c2 : (Setup (fun _ : Fin 3 => True) idM3 id (univ : Finset (Fin 3)) ∧ AdTester stT stKeep ∧ AcceptsAllFlag stT idM3 stKeep 3 ∧ (∀ h : Hist (Fin 3) (Fin 3), misses h ≤ 1 → stKeep h = 1) ∧ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3))) (classRule id id t) (seedPolicy (Z
~~~

### 1004. claim

Source: proofs/UMADAPTF1.lean:460 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMADAPTF1.Claim
~~~

### 1005. witness

Source: proofs/UMADAPTF1.lean:463 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMADAPTF1.Witness
~~~

## proofs/UMADAPTF2.lean

### 1006. adSurv_zero

Source: proofs/UMADAPTF2.lean:6 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_zero' {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (h : Hist X Z) : adSurv T M φ keep 0 h = keep h
~~~

### 1007. adSurv_succ

Source: proofs/UMADAPTF2.lean:11 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_succ' {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ) (h : Hist X Z) : adSurv T M φ keep (n + 1) h = ∑ x, T h x * ∑ z, M x z * (φ z * adSurv T M φ keep n (h ++ [(x, z, true)]) + (1 - φ z) * adSurv T M φ keep n (h ++ [(x, z, false)]))
~~~

### 1008. s_aux

Source: proofs/UMADAPTF2.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem s_aux {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hk : ∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) : ∀ (n : ℕ) (h : Hist X Z), (∀ e ∈ h, e.2.2 = false) → adSurv T M (fun _ => 0) keep n h = 1
~~~

### 1009. part_s

Source: proofs/UMADAPTF2.lean:40 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_s : ∀ (X Z : Type) [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ), IsKernel M → (∀ h, IsDist (T h)) → (∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) → AcceptsAllFlag T M keep n
~~~

### 1010. surv_bounds

Source: proofs/UMADAPTF2.lean:49 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_bounds {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hφ : IsRule φ) (hk : ∀ h, 0 ≤ keep h ∧ keep h ≤ 1) : ∀ (n : ℕ) (h : Hist X Z), 0 ≤ adSurv T M φ keep n h ∧ adSurv T M φ keep n h ≤ 1
~~~

### 1011. Qf_zero

Source: proofs/UMADAPTF2.lean:84 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_zero {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (h : Hist X Z) : Qf T M w 0 h = 0
~~~

### 1012. Qf_succ

Source: proofs/UMADAPTF2.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_succ {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (n : ℕ) (h : Hist X Z) : Qf T M w (n + 1) h = ∑ x, T h x * ∑ z, M x z * (w z + Qf T M w n (h ++ [(x, z, false)]))
~~~

### 1013. Qf_nonneg

Source: proofs/UMADAPTF2.lean:93 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Qf_nonneg {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (w : Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hw : ∀ z, 0 ≤ w z) : ∀ (n : ℕ) (h : Hist X Z), 0 ≤ Qf T M w n h
~~~

### 1014. sum2_add

Source: proofs/UMADAPTF2.lean:106 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum2_add {X Z : Type} [Fintype X] [Fintype Z] (a : X → ℝ) (m : X → Z → ℝ) (f g : X → Z → ℝ) (t : ℝ) : ∑ x, a x * ∑ z, m x z * f x z + t * ∑ x, a x * ∑ z, m x z * g x z = ∑ x, a x * ∑ z, m x z * (f x z + t * g x z)
~~~

### 1015. ref_lb

Source: proofs/UMADAPTF2.lean:117 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ref_lb {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ w : Z → ℝ) (t : ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (hk : ∀ h, 0 ≤ keep h ∧ keep h ≤ 1) (hφ : IsRule φ) (hw : ∀ z, 0 ≤ w z) (ht : 0 ≤ t) (hφw : ∀ z, φ z ≤ t * w z) : ∀ (n : ℕ) (h : Hist X Z), adSurv T M (fun _ => 0) keep n h - t * Qf T M w n h ≤ adSurv T M φ keep n h
~~~

### 1016. Q_sum_le

Source: proofs/UMADAPTF2.lean:147 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem Q_sum_le {X Z Ω : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (S : Finset Ω) (w : Ω → Z → ℝ) (hw1 : ∀ z, ∑ ω ∈ S, w ω z ≤ 1) : ∀ (n : ℕ) (h : Hist X Z), ∑ ω ∈ S, Qf T M (w ω) n h ≤ n
~~~

### 1017. ind_sum_le

Source: proofs/UMADAPTF2.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ind_sum_le {X Z C : Type} [DecidableEq C] (c : X → C) (g : Z → C) (S : Finset X) (hinj : Set.InjOn c (S : Set X)) (z : Z) : ∑ ω ∈ S, (if g z = c ω then (1 : ℝ) else 0) ≤ 1
~~~

### 1018. classRule_rule

Source: proofs/UMADAPTF2.lean:184 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classRule_rule {X Z C : Type} [DecidableEq C] (c : X → C) (g : Z → C) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ω : X) : IsRule (classRule c g t ω)
~~~

### 1019. conv_a

Source: proofs/UMADAPTF2.lean:188 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conv_a {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X) (hM : IsKernel M) (hbad : ∀ x ∈ S, Bad x) (hinj : Set.InjOn c (S : Set X)) (hS : 0 < S.card) (g : Z → C) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ) (hTk : AdTester T keep) (hacc : AcceptsAllFlag T M keep n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (r : ℝ) (b N : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hN : 1 ≤ N) : t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z
~~~

### 1020. opt_arith

Source: proofs/UMADAPTF2.lean:270 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem opt_arith (k n : ℝ) (hk : 0 < k) (hn : 1 ≤ n) : min (1 / 2) (k / (4 * n)) ≤ min 1 (k / (2 * n)) * max 0 (1 - min 1 (k / (2 * n)) * n / k)
~~~

### 1021. part_a

Source: proofs/UMADAPTF2.lean:289 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_a : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X), Setup Bad M c S → ∃ g : Z → C, (∀ x z, M x z ≠ 0 → g z = c x) ∧ (∀ (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ), AdTester T keep → AcceptsAllFlag T M keep n → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N → t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z
~~~

### 1022. adSurv_det

Source: proofs/UMADAPTF2.lean:322 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_det {X : Type} [Fintype X] [DecidableEq X] (T : Hist X X → X → ℝ) (M : X → X → ℝ) (q : Hist X X → X) (hT : ∀ h x, T h x = if x = q h then 1 else 0) (hM : ∀ x z, M x z = if z = x then 1 else 0) (φ : X → ℝ) (keep : Hist X X → ℝ) (n : ℕ) (h : Hist X X) : adSurv T M φ keep (n + 1) h = φ (q h) * adSurv T M φ keep n (h ++ [(q h, q h, true)]) + (1 - φ (q h)) * adSurv T M φ keep n (h ++ [(q h, q h, false)])
~~~

### 1023. cat_id1

Source: proofs/UMADAPTF2.lean:332 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_id1 {X : Type} [Fintype X] [DecidableEq X] (M : X → X → ℝ) (hM : ∀ x z, M x z = if z = x then 1 else 0) (φ : X → ℝ) (ω : X) : cat (fun _ : X => True) M φ (seedPolicy (Z
~~~

### 1024. det_dist

Source: proofs/UMADAPTF2.lean:337 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem det_dist {X : Type} [Fintype X] [DecidableEq X] (y : X) : IsDist (fun x : X => if x = y then (1 : ℝ) else 0)
~~~

### 1025. keep01

Source: proofs/UMADAPTF2.lean:343 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem keep01 (P : Prop) [Decidable P] : 0 ≤ (if P then (1 : ℝ) else 0) ∧ (if P then (1 : ℝ) else 0) ≤ 1
~~~

### 1026. setup_id

Source: proofs/UMADAPTF2.lean:347 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem setup_id {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] (M : X → X → ℝ) (hM : ∀ x z, M x z = if z = x then 1 else 0) : Setup (fun _ : X => True) M id (univ : Finset X)
~~~

### 1027. misses_allflag

Source: proofs/UMADAPTF2.lean:360 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem misses_allflag {X Z : Type} (h : Hist X Z) (hh : ∀ e ∈ h, e.2.2 = false) : misses h = 0
~~~

### 1028. c1_surv

Source: proofs/UMADAPTF2.lean:367 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c1_surv (t : ℝ) (ω : Bool) : adSurv ctrT idM (PL_UMLOWERF1.classRule id id t ω) ctrKeep 3 [] = if ω then 1 - t ^ 2 else (1 - t) + t * (1 - t) ^ 2
~~~

### 1029. c1_risk

Source: proofs/UMADAPTF2.lean:373 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c1_risk (t : ℝ) : adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool)) (classRule id id t) (seedPolicy (Z
~~~

### 1030. c2_surv

Source: proofs/UMADAPTF2.lean:384 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_surv (t : ℝ) (ω : Fin 3) : adSurv stT idM3 (PL_UMLOWERF1.classRule id id t ω) stKeep 3 [] = if ω = 0 then (1 - t) + t * (1 - t) ^ 2 else if ω = 1 then 1 - t ^ 2 else 1
~~~

### 1031. c2_risk

Source: proofs/UMADAPTF2.lean:390 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_risk (t : ℝ) : adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3))) (classRule id id t) (seedPolicy (Z
~~~

### 1032. c2_bound

Source: proofs/UMADAPTF2.lean:401 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem c2_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t - t ^ 3 + t ^ 4 / 3 < 1 / 2
~~~

### 1033. w_surv

Source: proofs/UMADAPTF2.lean:405 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_surv (t : ℝ) (ω : Bool) : adSurv wT idM (PL_UMLOWERF1.classRule id id t ω) wKeep 1 [] = if ω then 1 else 1 - t
~~~

### 1034. wbad_surv

Source: proofs/UMADAPTF2.lean:410 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wbad_surv (t : ℝ) (ω : Bool) : adSurv wT idM (PL_UMLOWERF1.classRule id id t ω) wKeepBad 1 [] = if ω then 0 else t
~~~

### 1035. part_c1

Source: proofs/UMADAPTF2.lean:415 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c1 : (Setup (fun _ : Bool => True) idM id (univ : Finset Bool) ∧ AdTester ctrT ctrKeep ∧ AcceptsAllFlag ctrT idM ctrKeep 3 ∧ (∀ h : Hist Bool Bool, misses h ≤ 1 → ctrKeep h = 1) ∧ adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool)) (classRule id id (3/4)) (seedPolicy (Z
~~~

### 1036. part_c2

Source: proofs/UMADAPTF2.lean:440 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem part_c2 : (Setup (fun _ : Fin 3 => True) idM3 id (univ : Finset (Fin 3)) ∧ AdTester stT stKeep ∧ AcceptsAllFlag stT idM3 stKeep 3 ∧ (∀ h : Hist (Fin 3) (Fin 3), misses h ≤ 1 → stKeep h = 1) ∧ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3))) (classRule id id t) (seedPolicy (Z
~~~

### 1037. claim1

Source: proofs/UMADAPTF2.lean:461 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim1 : PL_UMADAPTF1.Claim
~~~

### 1038. witness1

Source: proofs/UMADAPTF2.lean:464 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness1 : PL_UMADAPTF1.Witness
~~~

### 1039. slope_mono

Source: proofs/UMADAPTF2.lean:494 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
private lemma slope_mono (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : ∀ {n k : ℕ}, n ≤ k → slope b n ≤ slope b k
~~~

### 1040. tangent_step

Source: proofs/UMADAPTF2.lean:506 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
private lemma tangent_step (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (m q : ℕ) (hmq : m ≤ q) : b ^ (q + 1) + ((m : ℝ) - ((q + 1 : ℕ) : ℝ)) * slope b (q + 1) ≤ b ^ q + ((m : ℝ) - (q : ℝ)) * slope b q
~~~

### 1041. balanced_bound

Source: proofs/UMADAPTF2.lean:522 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem balanced_bound (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (m q : ℕ) : b ^ m ≥ b ^ q + ((m : ℝ) - (q : ℝ)) * (b ^ (q + 1) - b ^ q)
~~~

### 1042. aggregate_balanced_budget

Source: proofs/UMADAPTF2.lean:550 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem aggregate_balanced_budget (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k q a : ℕ) (_hk : 0 < k) (ha : a < k) (counts : Fin k → ℕ) (hcounts : ∑ i : Fin k, counts i ≤ k * q + a) : ∑ i : Fin k, b ^ (counts i) ≥ ((k - a : ℕ) : ℝ) * b ^ q + (a : ℝ) * b ^ (q + 1)
~~~

### 1043. aggregate_balanced_exact

Source: proofs/UMADAPTF2.lean:591 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem aggregate_balanced_exact (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k n : ℕ) (hk : 0 < k) (counts : Fin k → ℕ) (hcounts : ∑ i : Fin k, counts i = n) : ∑ i : Fin k, b ^ (counts i) ≥ ((k - n % k : ℕ) : ℝ) * b ^ (n / k) + ((n % k : ℕ) : ℝ) * b ^ (n / k + 1)
~~~

### 1044. classCount_append_flag

Source: proofs/UMADAPTF2.lean:626 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classCount_append_flag {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (h : SharpHist X Z) (x : X) (z : Z) (ω : Fin k) : classCount g (h ++ [(x, z, false)]) ω = classCount g h ω + (if g z = some ω then 1 else 0)
~~~

### 1045. flagFactor

Source: proofs/UMADAPTF2.lean:632 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem flagFactor {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (b : ℝ) (ω : Fin k) (z : Z) : 1 - passProb g (1-b) ω z = if g z = some ω then b else 1
~~~

### 1046. passProb_bounds

Source: proofs/UMADAPTF2.lean:646 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem passProb_bounds {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ω : Fin k) (z : Z) : 0 ≤ passProb g t ω z ∧ passProb g t ω z ≤ 1
~~~

### 1047. fullSurv_nonneg

Source: proofs/UMADAPTF2.lean:653 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fullSurv_nonneg {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) : ∀ n h ω, 0 ≤ fullSurv T M g t keep ω n h
~~~

### 1048. fullSurv_ge_flagOnly

Source: proofs/UMADAPTF2.lean:684 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fullSurv_ge_flagOnly {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) : ∀ n h ω, flagOnly T M g t keep ω n h ≤ fullSurv T M g t keep ω n h
~~~

### 1049. refSurv_eq_fullSurv_zero

Source: proofs/UMADAPTF2.lean:730 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refSurv_eq_fullSurv_zero {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (keep : SharpHist X Z → ℝ) : ∀ n h ω, refSurv T M keep n h = fullSurv T M g 0 keep ω n h
~~~

### 1050. classPower_append_flag

Source: proofs/UMADAPTF2.lean:756 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem classPower_append_flag {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (b : ℝ) (h : SharpHist X Z) (x : X) (z : Z) (ω : Fin k) : b ^ classCount g h ω * (if g z = some ω then b else 1) = b ^ classCount g (h ++ [(x,z,false)]) ω
~~~

### 1051. weightedFactor_append

Source: proofs/UMADAPTF2.lean:763 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
private theorem weightedFactor_append {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (b : ℝ) (h : SharpHist X Z) (x : X) (z : Z) (ω : Fin k) (f : ℝ) : b ^ classCount g (h ++ [(x,z,false)]) ω * f = b ^ classCount g h ω * ((1 - passProb g (1-b) ω z) * f)
~~~

### 1052. weighted_double_sum

Source: proofs/UMADAPTF2.lean:779 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem weighted_double_sum {α β : Type} [Fintype α] [Fintype β] (a : α → ℝ) (c : β → ℝ) (f : α → β → ℝ) : (∑ i, a i * ∑ j, c j * f i j) = ∑ j, c j * ∑ i, a i * f i j
~~~

### 1053. weightedFlag_succ

Source: proofs/UMADAPTF2.lean:799 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem weightedFlag_succ {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (b : ℝ) (keep : SharpHist X Z → ℝ) (n : ℕ) (h : SharpHist X Z) : weightedFlag T M g b keep (n+1) h = ∑ x, T h x * ∑ z, M x z * weightedFlag T M g b keep n (h ++ [(x,z,false)])
~~~

### 1054. count_sum_le

Source: proofs/UMADAPTF2.lean:886 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem count_sum_le {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (h : SharpHist X Z) : (∑ ω : Fin k, classCount g h ω) ≤ h.length
~~~

### 1055. weightedFlag_lower

Source: proofs/UMADAPTF2.lean:928 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem weightedFlag_lower {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (N : ℕ) : ∀ n h, h.length + n = N → balancedTarget k N b * refSurv T M keep n h ≤ weightedFlag T M g b keep n h
~~~

### 1056. sharp_survival

Source: proofs/UMADAPTF2.lean:992 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_survival {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : refSurv T M keep n [] = 1) : balancedTarget k n (1-t) ≤ ∑ ω : Fin k, fullSurv T M g t keep ω n []
~~~

### 1057. sharp_uniform_cat

Source: proofs/UMADAPTF2.lean:1022 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_uniform_cat {k : ℕ} (hkpos : 0 < k) (t : ℝ) (ht0 : 0 ≤ t) (n : ℕ) (surv cat : Fin k → ℝ) (hsurv : ∀ i, 0 ≤ surv i) (hcat : ∀ i, t ≤ cat i) (hsum : balancedTarget k n (1-t) ≤ ∑ i : Fin k, surv i) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ (1 / (k : ℝ)) * ∑ i : Fin k, surv i * cat i
~~~

### 1058. seedDecoder_eq_some_iff

Source: proofs/UMADAPTF2.lean:1058 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seedDecoder_eq_some_iff {X C Z : Type} [DecidableEq C] {k : ℕ} (seed : Fin k → X) (c : X → C) (g : Z → C) (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (z : Z) (i : Fin k) : seedDecoder seed c g z = some i ↔ g z = c (seed i)
~~~

### 1059. seedDecoder_pass_eq

Source: proofs/UMADAPTF2.lean:1088 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seedDecoder_pass_eq {X C Z : Type} [DecidableEq C] {k : ℕ} (seed : Fin k → X) (c : X → C) (g : Z → C) (t : ℝ) (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (i : Fin k) (z : Z) : passProb (seedDecoder seed c g) t i z = classPass c g t (seed i) z
~~~

### 1060. refSurv_eq_passSurv_zero

Source: proofs/UMADAPTF2.lean:1109 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem refSurv_eq_passSurv_zero {X : Type} {Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (keep : SharpHist X Z → ℝ) : ∀ n h, refSurv T M keep n h = passSurv T M (fun _ => 0) keep n h
~~~

### 1061. fullSurv_eq_passSurv_seed

Source: proofs/UMADAPTF2.lean:1126 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fullSurv_eq_passSurv_seed {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (seed : Fin k → X) (c : X → C) (g : Z → C) (t : ℝ) (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (keep : SharpHist X Z → ℝ) (i : Fin k) : ∀ n h, fullSurv T M (seedDecoder seed c g) t keep i n h = passSurv T M (classPass c g t (seed i)) keep n h
~~~

### 1062. sharp_seedset_survival

Source: proofs/UMADAPTF2.lean:1148 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_seedset_survival {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : refSurv T M keep n [] = 1) : balancedTarget k n (1-t) ≤ ∑ i : Fin k, passSurv T M (classPass c g t ((e i).val)) keep n []
~~~

### 1063. sharp_seedset_catRisk

Source: proofs/UMADAPTF2.lean:1177 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_seedset_catRisk {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : refSurv T M keep n [] = 1) (cat : Fin k → ℝ) (hcat : ∀ i, t ≤ cat i) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ (1 / (k : ℝ)) * ∑ i : Fin k, passSurv T M (classPass c g t ((e i).val)) keep n [] * cat i
~~~

### 1064. adSurv_reference_eq

Source: proofs/UMADAPTF2.lean:1234 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem adSurv_reference_eq {X Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (keep : SharpHist X Z → ℝ) : ∀ n h, refSurv T M keep n h = adSurv T M (fun _ => 0) keep n h
~~~

### 1065. accepts_all_flag_reference

Source: proofs/UMADAPTF2.lean:1240 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem accepts_all_flag_reference {X Z : Type} [Fintype X] [Fintype Z] (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (keep : SharpHist X Z → ℝ) (n : ℕ) (hacc : adSurv T M (fun _ => 0) keep n [] = 1) : refSurv T M keep n [] = 1
~~~

### 1066. sharp_uniform_seed_risk

Source: proofs/UMADAPTF2.lean:1250 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_uniform_seed_risk {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : adSurv T M (fun _ => 0) keep n [] = 1) (cat : Fin k → ℝ) (hcat : ∀ i, t ≤ cat i) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ (1 / (k : ℝ)) * ∑ i : Fin k, adSurv T M (classRule c g t ((e i).val)) keep n [] * cat i
~~~

### 1067. protocolCatModel_eq

Source: proofs/UMADAPTF2.lean:1281 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem protocolCatModel_eq {X : Type} [Fintype X] [DecidableEq X] (S : Finset X) (surv cat : X → ℝ) : protocolCatModel S surv cat = (1 / (S.card : ℝ)) * ∑ x : {x // x ∈ S}, surv x.val * cat x.val
~~~

### 1068. sum_finEquiv_eq_sum_seed

Source: proofs/UMADAPTF2.lean:1301 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_finEquiv_eq_sum_seed {X : Type} {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (f : {x // x ∈ S} → ℝ) : (∑ i : Fin k, f (e i)) = ∑ x : {x // x ∈ S}, f x
~~~

### 1069. sharp_uniform_adProtocolCatModel

Source: proofs/UMADAPTF2.lean:1305 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_uniform_adProtocolCatModel {X C Z : Type} [DecidableEq C] [Fintype X] [Fintype Z] [DecidableEq X] {k : ℕ} (S : Finset X) (e : Fin k ≃ {x // x ∈ S}) (c : X → C) (g : Z → C) (hinjS : Set.InjOn c (S : Set X)) (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h) (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) (hkpos : 0 < k) (n : ℕ) (hacc : adSurv T M (fun _ => 0) keep n [] = 1) (cat : X → ℝ) (hcat : ∀ x ∈ S, t ≤ cat x) : (t / (k : ℝ)) * balancedTarget k n (1-t) ≤ protocolCatModel S (fun x => adSurv T M (classRule c g t x) keep n []) cat
~~~

### 1070. sharp_surv_eq_campaign

Source: proofs/UMADAPTF2.lean:1357 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharp_surv_eq_campaign {X Z : Type} [Fintype X] [Fintype Z] (T : _root_.PL_UMPROTF1.Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ) (keep : _root_.PL_UMPROTF1.Hist X Z → ℝ) : ∀ n h, SharpUM.adSurv T M φ keep n h = _root_.PL_UMADAPTF1.adSurv T M φ keep n h
~~~

### 1071. conv_a_sharp

Source: proofs/UMADAPTF2.lean:1379 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conv_a_sharp {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X) (hM : IsKernel M) (hbad : ∀ x ∈ S, Bad x) (hinj : Set.InjOn c (S : Set X)) (hS : 0 < S.card) (g : Z → C) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ) (hTk : AdTester T keep) (hacc : AcceptsAllFlag T M keep n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (r : ℝ) (b N : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hN : 1 ≤ N) : (t / (S.card : ℝ)) * balancedTarget S.card n (1-t) ≤ adProtocolCat Bad M T keep n r b N (seedLaw S) (_root_.PL_UMLOWERF1.classRule c g t) (seedPolicy (Z
~~~

### 1072. sharpTarget_eq

Source: proofs/UMADAPTF2.lean:1439 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sharpTarget_eq (k n : ℕ) (b : ℝ) : PL_UMADAPTF2.sharpTarget k n b = balancedTarget k n b
~~~

### 1073. claim

Source: proofs/UMADAPTF2.lean:1442 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMADAPTF2.Claim
~~~

### 1074. rr_surv

Source: proofs/UMADAPTF2.lean:1451 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rr_surv (t : ℝ) (ω : Bool) : PL_UMADAPTF1.adSurv rrT idM (PL_UMLOWERF1.classRule id id t ω) rrKeep 3 [] = if ω then 1 - t else (1 - t) ^ 2
~~~

### 1075. witness

Source: proofs/UMADAPTF2.lean:1456 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMADAPTF2.Witness
~~~

## proofs/UMCERTF1.lean

### 1076. capB_mono

Source: proofs/UMCERTF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB_mono (r : ℝ) (b : ℕ) (hr : 0 ≤ r) {a a' : ℝ} (h : a ≤ a') : capB r b a ≤ capB r b a'
~~~

### 1077. capB_nonneg

Source: proofs/UMCERTF1.lean:12 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB_nonneg (r : ℝ) (b : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ capB r b a
~~~

### 1078. capB_le

Source: proofs/UMCERTF1.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB_le (r : ℝ) (b : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {a : ℝ} (ha : a ≤ 1) : capB r b a ≤ 1 - r + r * a
~~~

### 1079. capB_one

Source: proofs/UMCERTF1.lean:26 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB_one (r : ℝ) (b : ℕ) : capB r b 1 = 1
~~~

### 1080. E_const

Source: proofs/UMCERTF1.lean:32 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_const {Z : Type} [Fintype Z] (P : Z → ℝ) (hP : ∑ z, P z = 1) (t : ℝ) : E P (fun _ => t) = t
~~~

### 1081. E_push

Source: proofs/UMCERTF1.lean:37 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_push {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (P : X → ℝ) (ψ : Z → ℝ) : E (push M P) ψ = ∑ x, P x * E (M x) ψ
~~~

### 1082. unit_dist

Source: proofs/UMCERTF1.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem unit_dist : IsDist (fun _ : Unit => (1 : ℝ))
~~~

### 1083. point_dist

Source: proofs/UMCERTF1.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem point_dist {X : Type} [Fintype X] [DecidableEq X] (x : X) : IsDist (fun x' : X => if x' = x then (1 : ℝ) else 0)
~~~

### 1084. cat_empty

Source: proofs/UMCERTF1.lean:60 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_empty {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (b : ℕ) (hB : ∀ x, ¬ Bad x) : ∀ n u h, cat Bad M φ π r b n u h = 0
~~~

### 1085. cat_oneshot

Source: proofs/UMCERTF1.lean:71 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_oneshot {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] [DecidableEq X] (M : X → Z → ℝ) (ψ : Z → ℝ) (r : ℝ) (b N : ℕ) (x : X) (hM : IsKernel M) (hx : Bad x) (hN : 1 ≤ N) : cat Bad M ψ (fun _ x' => if x' = x then 1 else 0) r b N 0 [] = capB r b (E (M x) ψ)
~~~

### 1086. exists_worst

Source: proofs/UMCERTF1.lean:88 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exists_worst {X : Type} [Fintype X] (Bad : X → Prop) [DecidablePred Bad] (f : X → ℝ) (hex : ∃ x, Bad x) : ∃ x0, Bad x0 ∧ ∀ x, Bad x → f x ≤ f x0
~~~

### 1087. oneshot_value

Source: proofs/UMCERTF1.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem oneshot_value {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] [DecidableEq X] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (ψ : Z → ℝ) (x : X) (hM : IsKernel M) (hP : IsDist PH) (hx : Bad x) (hN : 1 ≤ N) : protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (fun _ => ψ) (fun _ _ x' => if x' = x then 1 else 0) = survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ)
~~~

### 1088. strat_oneshot_value

Source: proofs/UMCERTF1.lean:108 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem strat_oneshot_value {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (g : Z → C) (Es : Finset C) (m sc b N : ℕ) (r t : ℝ) (x : X) (hK : IsKernel K) (hdec : ∀ e z, K e z ≠ 0 → g z = e) (hx : Bad x) (hcx : c x ∈ Es) (hN : 1 ≤ N) : stratProtocolCat Bad K c Es m sc r b N (fun _ : Unit => 1) (fun _ z => if g z = c x then t else 0) (fun _ _ x' => if x' = x then 1 else 0) = binCDF m sc t * capB r b t
~~~

### 1089. seed_le

Source: proofs/UMCERTF1.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seed_le {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (hM : IsKernel M) (hP : IsDist PH) (hφ : IsRule φ) (hπ : ∀ h, IsDist (π h)) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hU : 0 ≤ U) (hyp : ∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) ≤ U) : surv (push M PH) φ κ nh 0 * cat Bad M φ π r b N 0 [] ≤ U
~~~

### 1090. reduce_le

Source: proofs/UMCERTF1.lean:150 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem reduce_le {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) (hM : IsKernel M) (hP : IsDist PH) (hρ : IsDist ρ) (hφ : ∀ ω, IsRule (φ ω)) (hπ : ∀ ω h, IsDist (π ω h)) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hU : 0 ≤ U) (hyp : ∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) ≤ U) : protocolCat Bad M PH κ nh r b N ρ φ π ≤ U
~~~

### 1091. survH_aux

Source: proofs/UMCERTF1.lean:167 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survH_aux (κ : ℕ → ℝ) (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ 1) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) : ∀ n j, (1 - κ j) * survH h κ n (j + 1) ≤ survH h κ n j
~~~

### 1092. survH_anti

Source: proofs/UMCERTF1.lean:190 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem survH_anti (κ : ℕ → ℝ) (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ 1) : ∀ n j (s t : ℝ), 0 ≤ s → s ≤ t → t ≤ 1 → survH t κ n j ≤ survH s κ n j
~~~

### 1093. GridOK_cons2

Source: proofs/UMCERTF1.lean:218 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem GridOK_cons2 (S F : ℝ → ℝ) (U s t : ℝ) (rest : List ℝ) : GridOK S F U (s :: t :: rest) ↔ s ≤ t ∧ S s * F t ≤ U ∧ GridOK S F U (t :: rest)
~~~

### 1094. GridOK_single

Source: proofs/UMCERTF1.lean:221 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem GridOK_single (S F : ℝ → ℝ) (U a : ℝ) : GridOK S F U [a] ↔ True
~~~

### 1095. grid_aux

Source: proofs/UMCERTF1.lean:223 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem grid_aux (S F : ℝ → ℝ) (U : ℝ) (hS : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s) (hF : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t) (h0 : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t) : ∀ (rest : List ℝ) (a b : ℝ), GridOK S F U (a :: b :: rest) → (a :: b :: rest).getLast? = some 1 → 0 ≤ a → a ≤ 1 ∧ ∀ t, a ≤ t → t ≤ 1 → S t * F t ≤ U
~~~

### 1096. grid_cert

Source: proofs/UMCERTF1.lean:263 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem grid_cert (S F : ℝ → ℝ) (U : ℝ) (ts : List ℝ) (hS : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s) (hF : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t) (h0 : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t) (hG : GridCert S F U ts) : ∀ t, 0 ≤ t → t ≤ 1 → S t * F t ≤ U
~~~

### 1097. bin_anti

Source: proofs/UMCERTF1.lean:282 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bin_anti (m sc : ℕ) : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → binCDF m sc t ≤ binCDF m sc s
~~~

### 1098. bin_nonneg

Source: proofs/UMCERTF1.lean:287 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bin_nonneg (m sc : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ binCDF m sc t
~~~

### 1099. dom_content

Source: proofs/UMCERTF1.lean:293 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dom_content {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] (K : C → Z → ℝ) (c : X → C) (PH : X → ℝ) (p : ℝ) (hK : IsKernel K) (hP : IsDist PH) (hp : 0 < p) (x : X) (hcov : p ≤ contentLaw c PH (c x)) (z : Z) : (fun x => K (c x)) x z ≤ (1 / p) * push (fun x => K (c x)) PH z
~~~

### 1100. claim_R

Source: proofs/UMCERTF1.lean:315 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_R : ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ), IsKernel M → IsDist PH → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N → 0 ≤ U → ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ↔ (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) ≤ U))
~~~

### 1101. claim_C

Source: proofs/UMCERTF1.lean:333 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_C : ∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (env : ℝ → ℝ) (U : ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 0 ≤ U → (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ env (E (push M PH) ψ)) → (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b (min 1 (env t)) ≤ U) → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U
~~~

### 1102. claim_E1

Source: proofs/UMCERTF1.lean:355 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_E1 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (L : ℝ) (x : X), (∀ z, M x z ≤ L * push M PH z) → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ L * E (push M PH) ψ
~~~

### 1103. claim_E2

Source: proofs/UMCERTF1.lean:361 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_E2 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (η δ : ℝ) (x : X), hs η (M x) (push M PH) ≤ δ → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ Real.exp η * E (push M PH) ψ + δ
~~~

### 1104. claim_G0

Source: proofs/UMCERTF1.lean:368 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_G0 : ∀ (κ : ℕ → ℝ) (n j : ℕ) (s t : ℝ), (∀ i, 0 ≤ κ i ∧ κ i ≤ 1) → 0 ≤ s → s ≤ t → t ≤ 1 → survH t κ n j ≤ survH s κ n j
~~~

### 1105. claim_G

Source: proofs/UMCERTF1.lean:372 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_G : ∀ (S F : ℝ → ℝ) (U : ℝ) (ts : List ℝ), (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s) → (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t) → (∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t) → GridCert S F U ts → ∀ t, 0 ≤ t → t ≤ 1 → S t * F t ≤ U
~~~

### 1106. claim_CG

Source: proofs/UMCERTF1.lean:379 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_CG : ∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (env : ℝ → ℝ) (U : ℝ) (ts : List ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ env (E (push M PH) ψ)) → (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → env s ≤ env t) → (∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ env t) → GridCert (fun t => survH t κ nh 0) (fun t => capB r b (min 1 (env t))) U ts → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U
~~~

### 1107. claim_S1

Source: proofs/UMCERTF1.lean:404 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_S1 : ∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 → (∀ x, Bad x → c x ∈ Es) → (∀ t : ℝ, 0 ≤ t → t ≤ 1 → binCDF m sc t * capB r b t ≤ U) → stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U
~~~

### 1108. claim_SG

Source: proofs/UMCERTF1.lean:440 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_SG : ∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ) (ts : List ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 → (∀ x, Bad x → c x ∈ Es) → GridCert (fun t => binCDF m sc t) (fun t => capB r b t) U ts → stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U
~~~

### 1109. claim_D1

Source: proofs/UMCERTF1.lean:455 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_D1 : ∀ (n s b : ℕ) (r L t : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ L → 0 ≤ t → t ≤ 1 → survH t (hardKill s) n 0 * capB r b (min 1 (L * t)) ≤ (1 - r) + r * (L * (((s : ℝ) + 1) / ((n : ℝ) + 1)))
~~~

### 1110. claim_D2

Source: proofs/UMCERTF1.lean:468 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_D2 : ∀ (n ns b : ℕ) (r L t : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ L → 1 ≤ ns → 0 ≤ t → t ≤ 1 → survH t (softKill ns) n 0 * capB r b (min 1 (L * t)) ≤ (1 - r) + r * (L * ((ns : ℝ) / ((n : ℝ) + 1)))
~~~

### 1111. claim_F

Source: proofs/UMCERTF1.lean:487 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_F : ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ), IsKernel M → IsDist PH → 1 ≤ N → (∃ x, Bad x) → (∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b t ≤ U
~~~

### 1112. claim_X

Source: proofs/UMCERTF1.lean:504 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_X : ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ), IsKernel M → IsDist PH → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N → (∃ x, Bad x) → (∀ x, Bad x → ∀ z, M x z ≤ push M PH z) → ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ↔ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b t ≤ U))
~~~

### 1113. claim_Xp

Source: proofs/UMCERTF1.lean:532 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_Xp : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (g : Z → C) (PH : X → ℝ) (p : ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ), IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → IsDist PH → 0 < p → (∀ x, Bad x → p ≤ contentLaw c PH (c x)) → (∃ x, Bad x ∧ contentLaw c PH (c x) = p) → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N → ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → protocolCat Bad (fun x => K (c x)) PH κ nh r b N ρ φ π ≤ U) ↔ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b (min 1 ((1 / p) * t)) ≤ U))
~~~

### 1114. claim_S2

Source: proofs/UMCERTF1.lean:620 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim_S2 : ∀ (X Z C : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (g : Z → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ), IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → 0 ≤ r → r ≤ 1 → 1 ≤ N → (∃ x, Bad x) → (∀ x, Bad x → c x ∈ Es) → ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U) ↔ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → binCDF m sc t * capB r b t ≤ U))
~~~

### 1115. claim

Source: proofs/UMCERTF1.lean:646 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMCERTF1.Claim
~~~

### 1116. bin12

Source: proofs/UMCERTF1.lean:652 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bin12 (s : ℝ) : binCDF 12 1 s = (1 - s) ^ 12 + 12 * s * (1 - s) ^ 11
~~~

### 1117. bin30

Source: proofs/UMCERTF1.lean:655 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bin30 (s : ℝ) : binCDF 30 1 s = (1 - s) ^ 30 + 30 * s * (1 - s) ^ 29
~~~

### 1118. soft5

Source: proofs/UMCERTF1.lean:658 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem soft5 (t : ℝ) : survH t (softKill 5) 100 0 = (1 - 1 / 5 * t) ^ 100
~~~

### 1119. hard1

Source: proofs/UMCERTF1.lean:665 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hard1 (t : ℝ) : survH t (hardKill 1) 30 0 = binCDF 30 1 t
~~~

### 1120. capB11

Source: proofs/UMCERTF1.lean:668 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capB11 (a : ℝ) : capB 1 1 a = a
~~~

### 1121. capBk

Source: proofs/UMCERTF1.lean:672 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem capBk (a : ℝ) : capB (9 / 10) 1 a = 1 / 10 + 9 / 10 * a
~~~

### 1122. idK_kernel

Source: proofs/UMCERTF1.lean:676 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem idK_kernel : IsKernel idK
~~~

### 1123. idK_dec

Source: proofs/UMCERTF1.lean:684 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem idK_dec : ∀ e z : Bool, idK e z ≠ 0 → id z = e
~~~

### 1124. ptTrue_dist

Source: proofs/UMCERTF1.lean:691 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem ptTrue_dist : IsDist ptTrue
~~~

### 1125. w_main

Source: proofs/UMCERTF1.lean:698 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_main : GridCert (fun t => binCDF 12 1 t) (fun t => capB 1 1 t) (7/100) gridMain
~~~

### 1126. w_soft

Source: proofs/UMCERTF1.lean:704 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_soft : GridCert (fun t => survH t (softKill 5) 100 0) (fun t => capB 1 1 (min 1 (1 * t))) (19/1000) gridSoft
~~~

### 1127. w_kink

Source: proofs/UMCERTF1.lean:711 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_kink : GridCert (fun t => survH t (hardKill 1) 30 0) (fun t => capB (9/10) 1 (min 1 (4 * t))) (17/100) gridKink
~~~

### 1128. w_strat

Source: proofs/UMCERTF1.lean:718 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_strat : (6833/100000 : ℝ) ≤ stratProtocolCat (fun x : Bool => x = true) idK id Finset.univ 12 1 1 1 1 (fun _ : Unit => 1) (fun _ z => if z = true then 1/8 else 0) (fun _ _ x => if x = true then 1 else 0)
~~~

### 1129. w_prot

Source: proofs/UMCERTF1.lean:727 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_prot : (6833/100000 : ℝ) ≤ protocolCat (fun x : Bool => x = true) idK ptTrue (hardKill 1) 12 1 1 1 (fun _ : Unit => 1) (fun _ _ => 1/8) (fun _ _ x => if x = true then 1 else 0)
~~~

### 1130. witness

Source: proofs/UMCERTF1.lean:738 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMCERTF1.Witness
~~~

## proofs/UMDEFERF1.lean

### 1131. mul_le_mul_of_pos_imp

Source: proofs/UMDEFERF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mul_le_mul_of_pos_imp {p x y : ℝ} (hp : 0 ≤ p) (h : 0 < p → x ≤ y) : p * x ≤ p * y
~~~

### 1132. conv01

Source: proofs/UMDEFERF1.lean:11 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem conv01 {p v w : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : 0 ≤ p * v + (1 - p) * w ∧ p * v + (1 - p) * w ≤ 1
~~~

### 1133. wsum01

Source: proofs/UMDEFERF1.lean:18 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum01 {Y : Type} [Fintype Y] (w f : Y → ℝ) (hw : IsDist w) (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) : 0 ≤ ∑ y, w y * f y ∧ ∑ y, w y * f y ≤ 1
~~~

### 1134. prod3_nonneg

Source: proofs/UMDEFERF1.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prod3_nonneg {p q c : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hc : 0 ≤ c) : 0 ≤ p * q * c
~~~

### 1135. prod3_le_one

Source: proofs/UMDEFERF1.lean:26 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prod3_le_one {p q c : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : p * q * c ≤ 1
~~~

### 1136. theta_bounds

Source: proofs/UMDEFERF1.lean:31 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem theta_bounds {η α : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : 0 ≤ theta η α ∧ theta η α ≤ 1
~~~

### 1137. one_sub_theta

Source: proofs/UMDEFERF1.lean:38 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem one_sub_theta (η α : ℝ) : 1 - theta η α = (1 - η) * (1 - α)
~~~

### 1138. retry_zero

Source: proofs/UMDEFERF1.lean:43 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_zero (A θ : ℝ) : retry A θ 0 = 0
~~~

### 1139. retry_succ

Source: proofs/UMDEFERF1.lean:45 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_succ (A θ : ℝ) (n : ℕ) : retry A θ (n + 1) = A + (1 - A) * (1 - θ) * retry A θ n
~~~

### 1140. retry_bounds

Source: proofs/UMDEFERF1.lean:48 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_bounds {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : ∀ n, 0 ≤ retry A θ n ∧ retry A θ n ≤ 1
~~~

### 1141. retry_le_succ

Source: proofs/UMDEFERF1.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_le_succ {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ1 : θ ≤ 1) : ∀ n, retry A θ n ≤ retry A θ (n + 1)
~~~

### 1142. retry_mono

Source: proofs/UMDEFERF1.lean:73 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_mono {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ1 : θ ≤ 1) {m n : ℕ} (hmn : m ≤ n) : retry A θ m ≤ retry A θ n
~~~

### 1143. retry_closed

Source: proofs/UMDEFERF1.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_closed (A θ : ℝ) : ∀ n, (θ + A * (1 - θ)) * retry A θ n = A * (1 - ((1 - A) * (1 - θ)) ^ n)
~~~

### 1144. retry_le_ratio

Source: proofs/UMDEFERF1.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_le_ratio (A θ : ℝ) (n : ℕ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hD : 0 < θ + A * (1 - θ)) : retry A θ n ≤ A / (θ + A * (1 - θ))
~~~

### 1145. retry_limit

Source: proofs/UMDEFERF1.lean:93 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem retry_limit (A θ : ℝ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hD : 0 < θ + A * (1 - θ)) : Tendsto (fun n : ℕ => retry A θ n) atTop (𝓝 (A / (θ + A * (1 - θ))))
~~~

### 1146. theta_retry_le

Source: proofs/UMDEFERF1.lean:112 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem theta_retry_le {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ) : θ * retry A θ n ≤ A
~~~

### 1147. fc_zero

Source: proofs/UMDEFERF1.lean:121 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_zero (r A θ : ℝ) (b u : ℕ) : finiteCap r A θ b 0 u = 0
~~~

### 1148. fc_ge

Source: proofs/UMDEFERF1.lean:124 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_ge (r A θ : ℝ) {b u : ℕ} (n : ℕ) (hbu : b ≤ u) : finiteCap r A θ b n u = retry A θ n
~~~

### 1149. fc_lt

Source: proofs/UMDEFERF1.lean:132 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_lt (r A θ : ℝ) {b u : ℕ} (n : ℕ) (hu : u < b) : finiteCap r A θ b (n + 1) u = max (1 - r + r * A) (retry A θ (n + 1 - (b - u)))
~~~

### 1150. fc_le_succ

Source: proofs/UMDEFERF1.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_le_succ {r A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (b n u : ℕ) : finiteCap r A θ b n u ≤ finiteCap r A θ b (n + 1) u
~~~

### 1151. fc_step

Source: proofs/UMDEFERF1.lean:151 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem fc_step {r A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {b u : ℕ} (n : ℕ) (hu : u < b) : finiteCap r A θ b n (u + 1) ≤ finiteCap r A θ b (n + 1) u
~~~

### 1152. catV_eta_one

Source: proofs/UMDEFERF1.lean:174 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catV_eta_one (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (a : Service X Z) (b : ℕ) : ∀ n u h, catV Bad M φ π r 1 a b n u h = cat Bad M φ π r b n u h
~~~

### 1153. catV_bounds

Source: proofs/UMDEFERF1.lean:185 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catV_bounds (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η : ℝ) (a : Service X Z) (b : ℕ) (hc : Core M φ π r η) (ha : IsService a) : ∀ n u h, 0 ≤ catV Bad M φ π r η a b n u h ∧ catV Bad M φ π r η a b n u h ≤ 1
~~~

### 1154. catD_cap

Source: proofs/UMDEFERF1.lean:221 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem catD_cap (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α A : ℝ) (b : ℕ) (hc : Core M φ π r η) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hbad : ∀ x, Bad x → E (M x) φ ≤ A) : ∀ n u h, catD Bad M φ π r η α b n u h ≤ finiteCap r A (theta η α) b n u
~~~

### 1155. bridge

Source: proofs/UMDEFERF1.lean:306 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bridge (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α : ℝ) (a : Service X Z) (b n0 u0 : ℕ) (h0 : Hist X Z) (hc : Core M φ π r η) (ha : IsService a) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hfl : UniformFloor Bad M φ π η a b n0 u0 h0 α) : ∀ n u h, Reach Bad M φ π η a b n0 u0 h0 n u h → catV Bad M φ π r η a b n u h ≤ catD Bad M φ π r η α b n u h
~~~

### 1156. attain

Source: proofs/UMDEFERF1.lean:382 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attain [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (r η α A : ℝ) (b u : ℕ) (x : X) (hM : IsKernel M) (hx : Bad x) (hbu : b ≤ u) : ∀ n (h : Hist X Z), catD Bad M (fun _ => A) (fun _ x' => if x' = x then 1 else 0) r η α b n u h = retry A (theta η α) n
~~~

### 1157. seed_bound

Source: proofs/UMDEFERF1.lean:403 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem seed_bound {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r η α L : ℝ) (a : Service X Z) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (hPH : IsDist PH) (hc : Core M φ π r η) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hL : 0 ≤ L) (ha : IsService a) (hfl : UniformFloor Bad M φ π η a b N 0 [] α) (hdom : ∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ surv (push M PH) φ (hardKill ns) nh 0 * catV Bad M φ π r η a b N 0 [] ≤ survH t (hardKill ns) nh 0 * finiteCap r (min 1 (L * t)) (theta η α) b N 0
~~~

### 1158. cert

Source: proofs/UMDEFERF1.lean:427 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cert {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r η α L U : ℝ) (a : Ω → Service X Z) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) (hpc : PairCore M PH ρ φ π r η) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hL : 0 ≤ L) (hfl : ProtocolFloor Bad M φ π η a b N α) (hdom : ∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) (hU : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t (hardKill ns) nh 0 * finiteCap r (min 1 (L * t)) (theta η α) b N 0 ≤ U) : protocolCatV Bad M PH (hardKill ns) nh r η a b N ρ φ π ≤ U
~~~

### 1159. coarse_bound

Source: proofs/UMDEFERF1.lean:445 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem coarse_bound (r θ L t : ℝ) (b N nh ns : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : survH t (hardKill ns) nh 0 * finiteCap r (min 1 (L * t)) θ b N 0 ≤ max (if 0 < b then (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) else 0) (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)) / θ)
~~~

### 1160. cnt_append

Source: proofs/UMDEFERF1.lean:486 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cnt_append (h : Hist Bool Bool) (x z c : Bool) : ((h ++ [(x, z, c)]).filter (fun e => e.2.2 = false)).length = (h.filter (fun e => e.2.2 = false)).length + (if c = false then 1 else 0)
~~~

### 1161. attack_phase

Source: proofs/UMDEFERF1.lean:491 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem attack_phase (r t : ℝ) (b : ℕ) : ∀ n (u : ℕ) (h : Hist Bool Bool), b ≤ u → b ≤ (h.filter (fun e => e.2.2 = false)).length → catV (X
~~~

### 1162. burn_phase

Source: proofs/UMDEFERF1.lean:511 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem burn_phase (r t : ℝ) (b : ℕ) : ∀ n k (u : ℕ) (h : Hist Bool Bool), u = (h.filter (fun e => e.2.2 = false)).length → u + k = b → catV (X
~~~

### 1163. nogo_eq

Source: proofs/UMDEFERF1.lean:533 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nogo_eq (PH : Bool → ℝ) (nh ns b N : ℕ) (r t : ℝ) (hPH : IsDist PH) : protocolCatD (X
~~~

### 1164. nogo_lb

Source: proofs/UMDEFERF1.lean:549 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem nogo_lb (PH : Bool → ℝ) (nh ns b N : ℕ) (t : ℝ) (hPH : IsDist PH) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (1 - t) ^ nh * (1 - (1 - t) ^ (N - b)) ≤ binCDF nh ns (PH true * t) * (1 - (1 - t) ^ (N - b))
~~~

### 1165. limit_e

Source: proofs/UMDEFERF1.lean:576 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem limit_e' (nh : ℕ) : Tendsto (fun K : ℕ => (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ nh * (1 - (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ K)) atTop (𝓝 1)
~~~

### 1166. claim

Source: proofs/UMDEFERF1.lean:625 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMDEFERF1.Claim
~~~

### 1167. witness

Source: proofs/UMDEFERF1.lean:665 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMDEFERF1.Witness
~~~

## proofs/UMHSF1.lean

### 1168. mul_le_max0

Source: proofs/UMHSF1.lean:1 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem mul_le_max0 (a φ : ℝ) (h0 : 0 ≤ φ) (h1 : φ ≤ 1) : a * φ ≤ max 0 a
~~~

### 1169. t2

Source: proofs/UMHSF1.lean:8 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t2 : ∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q φ : Z → ℝ), IsRule φ → E P φ ≤ Real.exp η * E Q φ + hs η P Q
~~~

### 1170. t2att

Source: proofs/UMHSF1.lean:19 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t2att : ∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q : Z → ℝ), ∃ φ, IsRule φ ∧ E P φ = Real.exp η * E Q φ + hs η P Q
~~~

### 1171. hs0_symm

Source: proofs/UMHSF1.lean:35 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hs0_symm {Z : Type} [Fintype Z] (P Q : Z → ℝ) (hP : ∑ z, P z = 1) (hQ : ∑ z, Q z = 1) : hs 0 Q P = hs 0 P Q
~~~

### 1172. t1

Source: proofs/UMHSF1.lean:50 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t1 : ∀ (Z : Type) [Fintype Z] (P Q φ : Z → ℝ), IsDist P → IsDist Q → IsRule φ → |E P φ - E Q φ| ≤ hs 0 P Q
~~~

### 1173. max0_sum_le

Source: proofs/UMHSF1.lean:60 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem max0_sum_le {X : Type} [Fintype X] (w f : X → ℝ) (hw : ∀ x, 0 ≤ w x) : max 0 (∑ x, w x * f x) ≤ ∑ x, w x * max 0 (f x)
~~~

### 1174. t4a

Source: proofs/UMHSF1.lean:66 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4a : ∀ (X Z : Type) [Fintype X] [Fintype Z] (η : ℝ) (K : X → Z → ℝ) (P Q : X → ℝ), IsKernel K → hs η (push K P) (push K Q) ≤ hs η P Q
~~~

### 1175. push_contentLaw

Source: proofs/UMHSF1.lean:87 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_contentLaw {X Z C : Type} [Fintype X] [Fintype C] [DecidableEq C] (K : C → Z → ℝ) (c : X → C) (P : X → ℝ) : push K (contentLaw c P) = push (fun x => K (c x)) P
~~~

### 1176. t4b

Source: proofs/UMHSF1.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4b : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η : ℝ) (M : X → Z → ℝ) (c : X → C) (PA PH : X → ℝ), ContentOnly M c → hs η (push M PA) (push M PH) ≤ hs η (contentLaw c PA) (contentLaw c PH)
~~~

### 1177. delta_dist

Source: proofs/UMHSF1.lean:106 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem delta_dist {C : Type} [Fintype C] [DecidableEq C] (e : C) : IsDist (delta e)
~~~

### 1178. push_decode

Source: proofs/UMHSF1.lean:111 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_decode {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (P : X → ℝ) : push (fun z => delta (g z)) (push M P) = contentLaw c P
~~~

### 1179. t4c

Source: proofs/UMHSF1.lean:126 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4c : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η : ℝ) (M : X → Z → ℝ) (c : X → C) (PA PH : X → ℝ), IsKernel M → ContentPreserving M c → hs η (contentLaw c PA) (contentLaw c PH) ≤ hs η (push M PA) (push M PH)
~~~

### 1180. t5d

Source: proofs/UMHSF1.lean:135 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t5d : ∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q P' Q' : Z → ℝ), hs η P Q ≤ hs η P' Q' + ∑ z, max 0 (P z - P' z) + Real.exp η * ∑ z, max 0 (Q' z - Q z)
~~~

### 1181. sum_max0_mix

Source: proofs/UMHSF1.lean:153 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_max0_mix {Z C : Type} [Fintype Z] [Fintype C] (w : Z → ℝ) (hw : ∀ z, 0 ≤ w z) (f : Z → C → ℝ) : ∑ e, max 0 (∑ z, w z * f z e) ≤ ∑ z, w z * ∑ e, max 0 (f z e)
~~~

### 1182. sum_max0_delta_sub_le

Source: proofs/UMHSF1.lean:161 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem sum_max0_delta_sub_le {C : Type} [Fintype C] [DecidableEq C] (a b : C) : ∑ e, max 0 (delta a e - delta b e) ≤ 1
~~~

### 1183. inner_A

Source: proofs/UMHSF1.lean:171 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inner_A {Z C : Type} [Fintype Z] [Fintype C] [DecidableEq C] (m : Z → ℝ) (hm : IsDist m) (a : C) (g : Z → C) : ∑ e, max 0 (delta a e - ∑ z, m z * delta (g z) e) ≤ ∑ z, m z * (if g z = a then 0 else 1)
~~~

### 1184. inner_H

Source: proofs/UMHSF1.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inner_H {Z C : Type} [Fintype Z] [Fintype C] [DecidableEq C] (m : Z → ℝ) (hm : IsDist m) (a : C) (g : Z → C) : ∑ e, max 0 (∑ z, m z * delta (g z) e - delta a e) ≤ ∑ z, m z * (if g z = a then 0 else 1)
~~~

### 1185. push_push

Source: proofs/UMHSF1.lean:203 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_push {X Z C : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (D : Z → C → ℝ) (P : X → ℝ) (e : C) : push D (push M P) e = ∑ x, P x * ∑ z, M x z * D z e
~~~

### 1186. approx_A

Source: proofs/UMHSF1.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem approx_A {X Z C : Type} [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (γ : ℝ) (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PA : X → ℝ) (hM : IsKernel M) (hPA : IsDist PA) (hγ : ∀ x, ∑ z, M x z * (if g z = c x then 0 else 1) ≤ γ) : ∑ e, max 0 (contentLaw c PA e - push (fun z => delta (g z)) (push M PA) e) ≤ γ
~~~

### 1187. approx_H

Source: proofs/UMHSF1.lean:231 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem approx_H {X Z C : Type} [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (γ : ℝ) (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PH : X → ℝ) (hM : IsKernel M) (hPH : IsDist PH) (hγ : ∀ x, ∑ z, M x z * (if g z = c x then 0 else 1) ≤ γ) : ∑ e, max 0 (push (fun z => delta (g z)) (push M PH) e - contentLaw c PH e) ≤ γ
~~~

### 1188. t4c_approx

Source: proofs/UMHSF1.lean:250 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4c_approx : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η γ : ℝ) (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PA PH : X → ℝ), IsKernel M → IsDist PA → IsDist PH → (∀ x, ∑ z, M x z * (if g z = c x then 0 else 1) ≤ γ) → hs η (contentLaw c PA) (contentLaw c PH) ≤ hs η (push M PA) (push M PH) + (1 + Real.exp η) * γ
~~~

### 1189. t4c'1

Source: proofs/UMHSF1.lean:266 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4c'1 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (B : Finset X) (hB : B.Nonempty) (Q : Z → ℝ) (L : ℝ), IsKernel M → IsDist Q → (∀ x ∈ B, ∀ z, M x z ≤ L * Q z) → ∑ z, B.sup' hB (fun x => M x z) ≤ L
~~~

### 1190. t4c'2

Source: proofs/UMHSF1.lean:275 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t4c'2 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (B : Finset X) (hB : B.Nonempty), IsKernel M → ∃ Q, IsDist Q ∧ ∀ x ∈ B, ∀ z, M x z ≤ (∑ z', B.sup' hB (fun x' => M x' z')) * Q z
~~~

### 1191. dom

Source: proofs/UMHSF1.lean:299 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem dom : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (PH : X → ℝ) (Bad : X → Prop) (p : ℝ), ContentOnly M c → IsDist PH → 0 < p → (∀ x, Bad x → p ≤ contentLaw c PH (c x)) → ∀ x, Bad x → ∀ z, M x z ≤ (1 / p) * push M PH z
~~~

### 1192. claim

Source: proofs/UMHSF1.lean:320 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 1193. idKernel

Source: proofs/UMHSF1.lean:323 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem idKernel : IsKernel (fun (x : Bool) (z : Bool) => if z = x then (1 : ℝ) else 0)
~~~

### 1194. witness

Source: proofs/UMHSF1.lean:329 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## proofs/UMLOWERF1.lean

### 1195. pat_sum_prod

Source: proofs/UMLOWERF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pat_sum_prod {n : ℕ} (f : Fin n → Bool → ℝ) : ∑ pat : Fin n → Bool, ∏ i, f i (pat i) = ∏ i, ∑ b, f i b
~~~

### 1196. bern_nonneg

Source: proofs/UMLOWERF1.lean:7 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bern_nonneg {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (pat : Fin n → Bool) : 0 ≤ ∏ i, (if pat i then a i else 1 - a i)
~~~

### 1197. bern_sum

Source: proofs/UMLOWERF1.lean:15 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bern_sum {n : ℕ} (a : Fin n → ℝ) : ∑ pat : Fin n → Bool, ∏ i, (if pat i then a i else 1 - a i) = 1
~~~

### 1198. bern_mean

Source: proofs/UMLOWERF1.lean:20 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem bern_mean {n : ℕ} (a : Fin n → ℝ) : ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) * ((univ.filter (fun i => pat i = true)).card : ℝ) = ∑ i, a i
~~~

### 1199. keep_lb

Source: proofs/UMLOWERF1.lean:49 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem keep_lb (ns : ℕ) (k : ℝ) (m : ℕ) (hk0 : 0 ≤ k) (hk : m ≤ ns → k = 1) : 1 - (m : ℝ) / ((ns : ℝ) + 1) ≤ k
~~~

### 1200. inner_lb

Source: proofs/UMLOWERF1.lean:61 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inner_lb {n : ℕ} (ns : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (kp : (Fin n → Bool) → ℝ) (hk0 : ∀ pat, 0 ≤ kp pat) (hk1 : ∀ pat, (univ.filter (fun i => pat i = true)).card ≤ ns → kp pat = 1) : 1 - (∑ i, a i) / ((ns : ℝ) + 1) ≤ ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) * kp pat
~~~

### 1201. inner_nonneg

Source: proofs/UMLOWERF1.lean:77 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem inner_nonneg {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (kp : (Fin n → Bool) → ℝ) (hk0 : ∀ pat, 0 ≤ kp pat) : 0 ≤ ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) * kp pat
~~~

### 1202. pass_eq

Source: proofs/UMLOWERF1.lean:82 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem pass_eq {X Z C : Type} [Fintype Z] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (t : ℝ) (x ω : X) : ∑ z, M x z * (if g z = c ω then t else 0) = if c x = c ω then t else 0
~~~

### 1203. class_sum_le

Source: proofs/UMLOWERF1.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem class_sum_le {X C : Type} [DecidableEq C] (c : X → C) (S : Finset X) (hinj : Set.InjOn c (S : Set X)) (t : ℝ) (ht : 0 ≤ t) (x : X) : ∑ ω ∈ S, (if c x = c ω then t else 0) ≤ t
~~~

### 1204. cat_ge

Source: proofs/UMLOWERF1.lean:104 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_ge {X Z : Type} [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (r : ℝ) (b N : ℕ) (ω : X) (hM : IsKernel M) (hφ : IsRule φ) (hr1 : r ≤ 1) (hN : 1 ≤ N) (hω : Bad ω) : ∑ z, M ω z * φ z ≤ cat Bad M φ (fun _ x => if x = ω then 1 else 0) r b N 0 []
~~~

### 1205. surv_sum_lb

Source: proofs/UMLOWERF1.lean:119 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_sum_lb {X Ω : Type} [Fintype X] (n ns : ℕ) (D : (Fin n → X) → ℝ) (hD : IsDist D) (keep : (Fin n → X) → (Fin n → Bool) → ℝ) (hkeep : ∀ xs pat, 0 ≤ keep xs pat) (hkeep1 : ∀ xs pat, (univ.filter (fun i => pat i = true)).card ≤ ns → keep xs pat = 1) (S : Finset Ω) (a : Ω → X → ℝ) (ha : ∀ ω x, 0 ≤ a ω x ∧ a ω x ≤ 1) (t : ℝ) (hsumA : ∀ x, ∑ ω ∈ S, a ω x ≤ t) : (S.card : ℝ) - n * t / ((ns : ℝ) + 1) ≤ ∑ ω ∈ S, ∑ xs, D xs * ∑ pat : Fin n → Bool, (∏ i, (if pat i then a ω (xs i) else 1 - a ω (xs i))) * keep xs pat
~~~

### 1206. combine

Source: proofs/UMLOWERF1.lean:151 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem combine {X : Type} [Fintype X] [DecidableEq X] (S : Finset X) (n ns : ℕ) (sv ct : X → ℝ) (t : ℝ) (hS : 0 < S.card) (ht : 0 ≤ t) (hsv0 : ∀ ω, 0 ≤ sv ω) (hct : ∀ ω ∈ S, t ≤ ct ω) (hsum : (S.card : ℝ) - n * t / ((ns : ℝ) + 1) ≤ ∑ ω ∈ S, sv ω) : t * (1 - t * (n : ℝ) / ((S.card : ℝ) * ((ns : ℝ) + 1))) ≤ ∑ ω, (if ω ∈ S then 1 / (S.card : ℝ) else 0) * sv ω * ct ω
~~~

### 1207. claim

Source: proofs/UMLOWERF1.lean:176 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMLOWERF1.Claim
~~~

### 1208. none_pass

Source: proofs/UMLOWERF1.lean:227 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem none_pass {n : ℕ} (a : Fin n → ℝ) : ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) * (if (univ.filter (fun i => pat i = true)).card ≤ 0 then (1 : ℝ) else 0) = ∏ i, (1 - a i)
~~~

### 1209. witness

Source: proofs/UMLOWERF1.lean:252 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMLOWERF1.Witness
~~~

## proofs/UMNOGOF1.lean

### 1210. submit_sum

Source: proofs/UMNOGOF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma submit_sum {X Z : Type} [Fintype X] (xs : X) (ω : Unit) (h : Hist X Z) (f : X → ℝ) : ∑ x, submit (Z
~~~

### 1211. submit_dist

Source: proofs/UMNOGOF1.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma submit_dist {X Z : Type} [Fintype X] (xs : X) (ω : Unit) (h : Hist X Z) : IsDist (submit (Z
~~~

### 1212. classMonitor_rule

Source: proofs/UMNOGOF1.lean:22 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma classMonitor_rule {Z C : Type} [DecidableEq C] (g : Z → C) (e : C) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : ∀ ω, IsRule (classMonitor g e t ω)
~~~

### 1213. protocolCat_unit

Source: proofs/UMNOGOF1.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma protocolCat_unit {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (φ : Unit → Z → ℝ) (π : Unit → Hist X Z → X → ℝ) : protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) φ π = surv (push M PH) (φ ()) κ nh 0 * cat Bad M (φ ()) (π ()) r b N 0 []
~~~

### 1214. cat_submit

Source: proofs/UMNOGOF1.lean:39 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma cat_submit {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (xs : X) (hx : Bad xs) (r : ℝ) (b N : ℕ) (hN : 1 ≤ N) : cat Bad M φ (submit (Z
~~~

### 1215. rate_eq

Source: proofs/UMNOGOF1.lean:47 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma rate_eq {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (PH : X → ℝ) (e : C) (t : ℝ) : ∑ z, push M PH z * classMonitor g e t () z = t * contentLaw c PH e
~~~

### 1216. pass_sum

Source: proofs/UMNOGOF1.lean:70 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma pass_sum {X Z C : Type} [Fintype Z] [DecidableEq C] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (xs : X) (t K : ℝ) : ∑ z, M xs z * (classMonitor g (c xs) t () z * 1 + (1 - classMonitor g (c xs) t () z) * K) = t + (1 - t) * K
~~~

### 1217. prot_formula

Source: proofs/UMNOGOF1.lean:82 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma prot_formula {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PH : X → ℝ) (xs : X) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (hPH : IsDist PH) (hx : Bad xs) (t : ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (hN : 1 ≤ N) : protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (classMonitor g (c xs) t) (submit (Z
~~~

### 1218. survH_ge

Source: proofs/UMNOGOF1.lean:93 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma survH_ge (h : ℝ) (κ : ℕ → ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1) : ∀ n j, (1 - h) ^ n ≤ survH h κ n j
~~~

### 1219. contentLaw_nonneg

Source: proofs/UMNOGOF1.lean:112 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma contentLaw_nonneg {X C : Type} [Fintype X] [DecidableEq C] (c : X → C) (PH : X → ℝ) (hPH : IsDist PH) (e : C) : 0 ≤ contentLaw c PH e
~~~

### 1220. classes_sum_le

Source: proofs/UMNOGOF1.lean:122 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma classes_sum_le {X C : Type} [Fintype X] [DecidableEq C] (c : X → C) (PH : X → ℝ) (hPH : IsDist PH) (S : Finset X) (hinj : Set.InjOn c (S : Set X)) : ∑ x ∈ S, contentLaw c PH (c x) ≤ 1
~~~

### 1221. claim

Source: proofs/UMNOGOF1.lean:145 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMNOGOF1.Claim
~~~

### 1222. witnessM_kernel

Source: proofs/UMNOGOF1.lean:187 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witnessM_kernel : IsKernel witnessM
~~~

### 1223. witnessM_dec

Source: proofs/UMNOGOF1.lean:195 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witnessM_dec : ∀ x z, witnessM x z ≠ 0 → (id : Fin 4 → Fin 4) z = id x
~~~

### 1224. witnessPH_dist

Source: proofs/UMNOGOF1.lean:202 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witnessPH_dist : IsDist witnessPH
~~~

### 1225. witness_content

Source: proofs/UMNOGOF1.lean:209 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witness_content : contentLaw (id : Fin 4 → Fin 4) witnessPH 2 = 1 / 4
~~~

### 1226. witnessS_card

Source: proofs/UMNOGOF1.lean:212 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma witnessS_card : witnessS.card = 4
~~~

### 1227. witness

Source: proofs/UMNOGOF1.lean:215 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMNOGOF1.Witness
~~~

## proofs/UMPROTF1.lean

### 1228. wsum_le

Source: proofs/UMPROTF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum_le {Y : Type} [Fintype Y] (w f : Y → ℝ) (c : ℝ) (hw : IsDist w) (hf : ∀ y, f y ≤ c) : ∑ y, w y * f y ≤ c
~~~

### 1229. wsum_nonneg

Source: proofs/UMPROTF1.lean:9 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wsum_nonneg {Y : Type} [Fintype Y] (w f : Y → ℝ) (hw : ∀ y, 0 ≤ w y) (hf : ∀ y, 0 ≤ f y) : 0 ≤ ∑ y, w y * f y
~~~

### 1230. t3a

Source: proofs/UMPROTF1.lean:13 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem t3a {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r A : ℝ) (b : ℕ) (hM : IsKernel M) (hφ : IsRule φ) (hπ : ∀ h, IsDist (π h)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hbad : ∀ x, Bad x → E (M x) φ ≤ A) : ∀ n u h, 0 ≤ cat Bad M φ π r b n u h ∧ cat Bad M φ π r b n u h ≤ (if u < b then 1 - r + r * A else A)
~~~

### 1231. cat_le

Source: proofs/UMPROTF1.lean:86 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_le {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r A : ℝ) (b : ℕ) (hM : IsKernel M) (hφ : IsRule φ) (hπ : ∀ h, IsDist (π h)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hbad : ∀ x, Bad x → E (M x) φ ≤ A) (n u : ℕ) (h : Hist X Z) : 0 ≤ cat Bad M φ π r b n u h ∧ cat Bad M φ π r b n u h ≤ 1 - r + r * A
~~~

### 1232. push_dist

Source: proofs/UMPROTF1.lean:96 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem push_dist {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (hM : IsKernel M) (hP : IsDist PH) : IsDist (push M PH)
~~~

### 1233. prot_bound

Source: proofs/UMPROTF1.lean:108 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem prot_bound {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) (C : ℝ) (hM : IsKernel M) (hρ : IsDist ρ) (hφ : ∀ ω, IsRule (φ ω)) (hπ : ∀ ω h, IsDist (π ω h)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hω : ∀ ω, ∃ A, 0 ≤ A ∧ A ≤ 1 ∧ (∀ x, Bad x → E (M x) (φ ω) ≤ A) ∧ 0 ≤ surv (push M PH) (φ ω) κ nh 0 ∧ surv (push M PH) (φ ω) κ nh 0 * (1 - r + r * A) ≤ C) : protocolCat Bad M PH κ nh r b N ρ φ π ≤ C
~~~

### 1234. rate_facts

Source: proofs/UMPROTF1.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rate_facts {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (φ : Z → ℝ) (hM : IsKernel M) (hP : IsDist PH) (hφ : IsRule φ) : 0 ≤ ∑ z, push M PH z * φ z ∧ ∑ z, push M PH z * φ z ≤ 1
~~~

### 1235. E_le_one

Source: proofs/UMPROTF1.lean:133 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_le_one {X Z : Type} [Fintype Z] (M : X → Z → ℝ) (φ : Z → ℝ) (hM : IsKernel M) (hφ : IsRule φ) (x : X) : E (M x) φ ≤ 1
~~~

### 1236. surv_eq

Source: proofs/UMPROTF1.lean:137 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_eq {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (φ : Z → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (hM : IsKernel M) (hP : IsDist PH) : surv (push M PH) φ κ nh 0 = survH (∑ z, push M PH z * φ z) κ nh 0
~~~

### 1237. final_dom

Source: proofs/UMPROTF1.lean:142 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem final_dom (S h L r A B : ℝ) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hA : A ≤ L * h) (hB : h * S ≤ B) : S * (1 - r + r * A) ≤ (1 - r) + r * (L * B)
~~~

### 1238. final_hs

Source: proofs/UMPROTF1.lean:155 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem final_hs (S h r A δ c B : ℝ) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hA : A ≤ c * h + δ) (hB : h * S ≤ B) : S * (1 - r + r * A) ≤ (1 - r) + r * (δ + c * B)
~~~

### 1239. hardKill_prob

Source: proofs/UMPROTF1.lean:170 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem hardKill_prob (ns : ℕ) : ∀ i, 0 ≤ hardKill ns i ∧ hardKill ns i ≤ 1
~~~

### 1240. E_dom

Source: proofs/UMPROTF1.lean:173 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_dom {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (φ : Z → ℝ) (hφ : IsRule φ) (L : ℝ) (x : X) (hd : ∀ z, M x z ≤ L * push M PH z) : E (M x) φ ≤ L * ∑ z, push M PH z * φ z
~~~

### 1241. claim

Source: proofs/UMPROTF1.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMPROTF1.Claim
~~~

### 1242. witness

Source: proofs/UMPROTF1.lean:269 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMPROTF1.Witness
~~~

## proofs/UMSTRATF1.lean

### 1243. surv_eq_bin

Source: proofs/UMSTRATF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem surv_eq_bin {Z : Type} [Fintype Z] (q φ : Z → ℝ) (hq : ∑ z, q z = 1) (m sc : ℕ) : surv q φ (hardKill sc) m 0 = binCDF m sc (E q φ)
~~~

### 1244. rate01

Source: proofs/UMSTRATF1.lean:9 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem rate01 {Z : Type} [Fintype Z] (q φ : Z → ℝ) (hq : IsDist q) (hφ : IsRule φ) : 0 ≤ E q φ ∧ E q φ ≤ 1
~~~

### 1245. factor01

Source: proofs/UMSTRATF1.lean:14 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem factor01 {Z : Type} [Fintype Z] (q φ : Z → ℝ) (hq : IsDist q) (hφ : IsRule φ) (m sc : ℕ) : 0 ≤ surv q φ (hardKill sc) m 0 ∧ surv q φ (hardKill sc) m 0 ≤ 1
~~~

### 1246. strat01

Source: proofs/UMSTRATF1.lean:23 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem strat01 {Z C : Type} [Fintype Z] (K : C → Z → ℝ) (Es : Finset C) (φ : Z → ℝ) (m sc : ℕ) (hK : IsKernel K) (hφ : IsRule φ) : 0 ≤ stratSurv K Es φ m sc ∧ stratSurv K Es φ m sc ≤ 1
~~~

### 1247. strat_le_factor

Source: proofs/UMSTRATF1.lean:31 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem strat_le_factor {Z C : Type} [Fintype Z] (K : C → Z → ℝ) (Es : Finset C) (φ : Z → ℝ) (m sc : ℕ) (hK : IsKernel K) (hφ : IsRule φ) (e : C) (he : e ∈ Es) : stratSurv K Es φ m sc ≤ surv (K e) φ (hardKill sc) m 0
~~~

### 1248. exists_A

Source: proofs/UMSTRATF1.lean:44 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem exists_A {X Z C : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (φ : Z → ℝ) (m sc : ℕ) (hK : IsKernel K) (hφ : IsRule φ) (hEs : ∀ x, Bad x → c x ∈ Es) : ∃ A, 0 ≤ A ∧ A ≤ 1 ∧ (∀ x, Bad x → E (K (c x)) φ ≤ A) ∧ A * stratSurv K Es φ m sc ≤ ((sc : ℝ) + 1) / ((m : ℝ) + 1)
~~~

### 1249. claim1

Source: proofs/UMSTRATF1.lean:72 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim1 : ∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r : ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ), IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 → (∀ x, Bad x → c x ∈ Es) → stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ (1 - r) + r * (((sc : ℝ) + 1) / ((m : ℝ) + 1))
~~~

### 1250. binCDF_at_zero

Source: proofs/UMSTRATF1.lean:98 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem binCDF_at_zero (m sc : ℕ) : binCDF m sc 0 = 1
~~~

### 1251. E_dec

Source: proofs/UMSTRATF1.lean:103 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem E_dec {Z C : Type} [Fintype Z] [DecidableEq C] (K : C → Z → ℝ) (g : Z → C) (t : ℝ) (e0 e : C) (hK : IsKernel K) (hdec : ∀ e z, K e z ≠ 0 → g z = e) : E (K e) (fun z => if g z = e0 then t else 0) = if e = e0 then t else 0
~~~

### 1252. strat_att

Source: proofs/UMSTRATF1.lean:127 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem strat_att {Z C : Type} [Fintype Z] [DecidableEq C] (K : C → Z → ℝ) (g : Z → C) (Es : Finset C) (t : ℝ) (e0 : C) (m sc : ℕ) (hK : IsKernel K) (hdec : ∀ e z, K e z ≠ 0 → g z = e) (he0 : e0 ∈ Es) : stratSurv K Es (fun z => if g z = e0 then t else 0) m sc = binCDF m sc t
~~~

### 1253. cat_point

Source: proofs/UMSTRATF1.lean:138 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem cat_point {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] [DecidableEq X] (M : X → Z → ℝ) (φ : Z → ℝ) (r : ℝ) (b N : ℕ) (x : X) (hM : IsKernel M) (hx : Bad x) (hN : 1 ≤ N) (hb : 1 ≤ b) : cat Bad M φ (fun _ x' => if x' = x then 1 else 0) r b N 0 [] = 1 - r + r * E (M x) φ
~~~

### 1254. claim2

Source: proofs/UMSTRATF1.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim2 : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq C] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (g : Z → C) (Es : Finset C) (m sc b N : ℕ) (r t : ℝ) (x : X), IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → Bad x → c x ∈ Es → 1 ≤ N → 1 ≤ b → 0 ≤ t → t ≤ 1 → stratProtocolCat Bad K c Es m sc r b N (fun _ : Unit => 1) (fun _ z => if g z = c x then t else 0) (fun _ _ x' => if x' = x then 1 else 0) = binCDF m sc t * (1 - r + r * t)
~~~

### 1255. claim

Source: proofs/UMSTRATF1.lean:166 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMSTRATF1.Claim
~~~

### 1256. wK

Source: proofs/UMSTRATF1.lean:168 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wK : IsKernel witnessK
~~~

### 1257. wdec

Source: proofs/UMSTRATF1.lean:176 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wdec : ∀ e z : Bool, witnessK e z ≠ 0 → id z = e
~~~

### 1258. wval

Source: proofs/UMSTRATF1.lean:183 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wval : stratProtocolCat (fun x : Bool => x = true) witnessK id (Finset.univ : Finset Bool) 12 1 1 1 1 (fun _ : Unit => 1) witnessPhi witnessPi = binCDF 12 1 (1 / 6) * (1 - 1 + 1 * (1 / 6 : ℝ))
~~~

### 1259. wbin

Source: proofs/UMSTRATF1.lean:190 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wbin : binCDF 12 1 (1 / 6 : ℝ) = (5 / 6) ^ 12 + 12 * (1 / 6) * (5 / 6) ^ 11
~~~

### 1260. witness

Source: proofs/UMSTRATF1.lean:194 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMSTRATF1.Witness
~~~

## proofs/UMSURVF1.lean

### 1261. binTerm_pascal

Source: proofs/UMSURVF1.lean:3 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binTerm_pascal (n k : ℕ) (h : ℝ) : ((n + 1).choose (k + 1) : ℝ) * h ^ (k + 1) * (1 - h) ^ (n + 1 - (k + 1)) = h * ((n.choose k : ℝ) * h ^ k * (1 - h) ^ (n - k)) + (1 - h) * ((n.choose (k + 1) : ℝ) * h ^ (k + 1) * (1 - h) ^ (n - (k + 1)))
~~~

### 1262. binCDF_zero_n

Source: proofs/UMSURVF1.lean:21 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binCDF_zero_n (s : ℕ) (h : ℝ) : binCDF 0 s h = 1
~~~

### 1263. binCDF_n_zero

Source: proofs/UMSURVF1.lean:30 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binCDF_n_zero (n : ℕ) (h : ℝ) : binCDF n 0 h = (1 - h) ^ n
~~~

### 1264. binCDF_pascal

Source: proofs/UMSURVF1.lean:34 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binCDF_pascal (n s : ℕ) (h : ℝ) : binCDF (n + 1) (s + 1) h = (1 - h) * binCDF n (s + 1) h + h * binCDF n s h
~~~

### 1265. survH_hard

Source: proofs/UMSURVF1.lean:43 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma survH_hard (h : ℝ) (ns : ℕ) : ∀ n j, j ≤ ns → survH h (hardKill ns) n j = binCDF n (ns - j) h
~~~

### 1266. survH_const

Source: proofs/UMSURVF1.lean:66 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma survH_const (h k : ℝ) : ∀ (n j : ℕ), survH h (fun _ => k) n j = (1 - k * h) ^ n
~~~

### 1267. survH_prob

Source: proofs/UMSURVF1.lean:75 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma survH_prob (h : ℝ) (κ : ℕ → ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ 1) : ∀ n j, 0 ≤ survH h κ n j ∧ survH h κ n j ≤ 1
~~~

### 1268. binCDF_le_one

Source: proofs/UMSURVF1.lean:99 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma binCDF_le_one (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : binCDF n s h ≤ 1
~~~

### 1269. first_moment

Source: proofs/UMSURVF1.lean:106 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma first_moment (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : ((n : ℝ) + 1) * (h * binCDF n s h) ≤ (s : ℝ) + 1
~~~

### 1270. first_moment

Source: proofs/UMSURVF1.lean:146 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
lemma first_moment' (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : h * binCDF n s h ≤ ((s : ℝ) + 1) / ((n : ℝ) + 1)
~~~

### 1271. claim

Source: proofs/UMSURVF1.lean:152 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : Claim
~~~

### 1272. witness

Source: proofs/UMSURVF1.lean:191 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : Witness
~~~

## proofs/UMUSEF1.lean

### 1273. usef_split

Source: proofs/UMUSEF1.lean:5 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_split {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (μ : X → ℝ) (φ : Z → ℝ) (hM : IsKernel M) (hμ : IsDist μ) (A B : ℝ) : ∑ x, μ x * ∑ z, M x z * (φ z * A + (1 - φ z) * B) = (1 - flagRate M μ φ) * A + flagRate M μ φ * B
~~~

### 1274. usef_flag01

Source: proofs/UMUSEF1.lean:25 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_flag01 {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (μ : X → ℝ) (φ : Z → ℝ) (hM : IsKernel M) (hφ : IsRule φ) (hμ : IsDist μ) : 0 ≤ flagRate M μ φ ∧ flagRate M μ φ ≤ 1
~~~

### 1275. usef_halt

Source: proofs/UMUSEF1.lean:37 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_halt {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (μ : X → ℝ) (b : ℕ) (hM : IsKernel M) (hμ : IsDist μ) (hsupp : ∀ x, μ x ≠ 0 → ¬ Bad x) : ∀ n u h, 1 - haltP Bad M φ (fun _ => μ) b n u h = survH (flagRate M μ φ) (hardKill b) n u
~~~

### 1276. usef_bin01

Source: proofs/UMUSEF1.lean:74 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_bin01 (n s : ℕ) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : 0 ≤ binCDF n s a ∧ binCDF n s a ≤ 1
~~~

### 1277. usef_hc

Source: proofs/UMUSEF1.lean:80 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_hc {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh b N : ℕ) (φ₀ : Z → ℝ) (μ : X → ℝ) (hM : IsKernel M) (hP : IsDist PH) (hμ : IsDist μ) (hsupp : ∀ x, μ x ≠ 0 → ¬ Bad x) : honestCompletion Bad M PH κ nh b N φ₀ μ = survH (missRate M PH φ₀) κ nh 0 * binCDF N b (flagRate M μ φ₀)
~~~

### 1278. usef_vb

Source: proofs/UMUSEF1.lean:92 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_vb {X Z : Type} [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r h : ℝ) (b N : ℕ) (x : X) (hM : IsKernel M) (hP : IsDist PH) (hx : Bad x) (hN : 1 ≤ N) : viewBlindRisk Bad M PH κ nh r b N h x = survH h κ nh 0 * (h + (if 0 < b then (1 - r) * (1 - h) else 0))
~~~

### 1279. usefB_nonneg

Source: proofs/UMUSEF1.lean:120 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_nonneg (n : ℕ) (a : ℝ) (j : ℕ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : 0 ≤ usefB n a j
~~~

### 1280. usefB_step

Source: proofs/UMUSEF1.lean:123 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_step (n : ℕ) (a : ℝ) (g : ℕ → ℝ) : ∑ j ∈ range (n + 1 + 1), usefB (n + 1) a j * g j = (1 - a) * ∑ j ∈ range (n + 1), usefB n a j * g j + a * ∑ j ∈ range (n + 1), usefB n a j * g (j + 1)
~~~

### 1281. usefB_m0

Source: proofs/UMUSEF1.lean:154 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_m0 (a : ℝ) : ∀ n : ℕ, ∑ j ∈ range (n + 1), usefB n a j = 1
~~~

### 1282. usefB_m1

Source: proofs/UMUSEF1.lean:164 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_m1 (a : ℝ) : ∀ n : ℕ, ∑ j ∈ range (n + 1), usefB n a j * (j : ℝ) = n * a
~~~

### 1283. usefB_m2

Source: proofs/UMUSEF1.lean:181 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_m2 (a : ℝ) : ∀ n : ℕ, ∑ j ∈ range (n + 1), usefB n a j * (j : ℝ) ^ 2 = n * a * (1 - a) + (n * a) ^ 2
~~~

### 1284. usefB_var

Source: proofs/UMUSEF1.lean:200 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_var (a c : ℝ) (n : ℕ) : ∑ j ∈ range (n + 1), usefB n a j * ((j : ℝ) - c) ^ 2 = n * a * (1 - a) + (n * a - c) ^ 2
~~~

### 1285. usefB_ext

Source: proofs/UMUSEF1.lean:210 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usefB_ext (n K : ℕ) (a : ℝ) (g : ℕ → ℝ) (hK : n + 1 ≤ K) : ∑ j ∈ range K, usefB n a j * g j = ∑ j ∈ range (n + 1), usefB n a j * g j
~~~

### 1286. usef_cant_alg

Source: proofs/UMUSEF1.lean:220 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_cant_alg (d σ W : ℝ) (hd : 0 < d) (hσ : 0 ≤ σ) (hW : 0 ≤ W) (h : ∀ t, 0 ≤ t → (d + t) ^ 2 * W ≤ σ + t ^ 2) : d ^ 2 * W ≤ σ * (1 - W)
~~~

### 1287. usef_lower

Source: proofs/UMUSEF1.lean:246 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_lower (n s : ℕ) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : (max 0 ((n : ℝ) * a - s)) ^ 2 * binCDF n s a ≤ n * a * (1 - a) * (1 - binCDF n s a)
~~~

### 1288. usef_upper

Source: proofs/UMUSEF1.lean:284 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_upper (n s : ℕ) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : (max 0 ((s : ℝ) + 1 - n * a)) ^ 2 * (1 - binCDF n s a) ≤ n * a * (1 - a) * binCDF n s a
~~~

### 1289. usef_cat_r

Source: proofs/UMUSEF1.lean:337 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem usef_cat_r {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r r' : ℝ) : ∀ n u h, cat Bad M φ π r 0 n u h = cat Bad M φ π r' 0 n u h
~~~

### 1290. claim

Source: proofs/UMUSEF1.lean:349 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem claim : PL_UMUSEF1.Claim
~~~

### 1291. wM_k

Source: proofs/UMUSEF1.lean:486 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wM_k : IsKernel wM
~~~

### 1292. wPH_d

Source: proofs/UMUSEF1.lean:494 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem wPH_d : IsDist wPH
~~~

### 1293. w_supp

Source: proofs/UMUSEF1.lean:518 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_supp : ∀ x, wμ x ≠ 0 → ¬ x = true
~~~

### 1294. w_miss

Source: proofs/UMUSEF1.lean:524 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_miss : missRate wM wPH wφ = 9 / 40
~~~

### 1295. w_flag

Source: proofs/UMUSEF1.lean:528 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_flag : flagRate wM wμ wφ = 13 / 40
~~~

### 1296. w_hs

Source: proofs/UMUSEF1.lean:532 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem w_hs : hs 0 (push wM wμ) (push wM wPH) = 1 / 2
~~~

### 1297. witness

Source: proofs/UMUSEF1.lean:536 | Family: UNMAPPED | Adversary: UNKNOWN | Status: SOURCE_ONLY

~~~lean
theorem witness : PL_UMUSEF1.Witness
~~~

## Reviewer obligations

Check fully elaborated Lean goals and quantified premises; inspect what Bad, observations, harm, authority and budgets mean; review model-to-runtime correspondence independently.
