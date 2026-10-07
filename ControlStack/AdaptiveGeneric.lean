import ControlStack.AdaptiveBalance
import Mathlib.Tactic

/-! Direct recursive proof layer for the sharp adaptive converse. It avoids an
explicit dependent `Path` type: all-FLAG prefixes are the histories already
used by `adSurv`, with decoder-class query counts tracked as a potential. -/

namespace ControlStack.AdaptiveGeneric

abbrev Hist (X : Type) (Z : Type) := List (X × Z × Bool)

def passProb {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (t : ℝ)
    (ω : Fin k) (z : Z) : ℝ := if g z = some ω then t else 0

def classCount {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k))
    (h : Hist X Z) (ω : Fin k) : ℕ :=
  (h.filter (fun e => g e.2.1 = some ω)).length

theorem classCount_append_flag {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k))
    (h : Hist X Z) (x : X) (z : Z) (ω : Fin k) :
    classCount g (h ++ [(x, z, false)]) ω =
      classCount g h ω + (if g z = some ω then 1 else 0) := by
  by_cases hmatch : g z = some ω <;> simp [classCount, List.filter_append, List.filter_cons, hmatch]

theorem flagFactor {k : ℕ} {Z : Type} (g : Z → Option (Fin k))
    (b : ℝ) (ω : Fin k) (z : Z) :
    1 - passProb g (1-b) ω z = if g z = some ω then b else 1 := by
  by_cases h : g z = some ω <;> simp [passProb, h]

noncomputable def fullSurv {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (t : ℝ) (keep : Hist X Z → ℝ) (ω : Fin k) :
    ℕ → Hist X Z → ℝ
  | 0, h => keep h
  | n + 1, h => ∑ x, T h x * ∑ z, M x z *
      (passProb g t ω z * fullSurv T M g t keep ω n (h ++ [(x,z,true)]) +
       (1 - passProb g t ω z) * fullSurv T M g t keep ω n (h ++ [(x,z,false)]))

theorem passProb_bounds {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ω : Fin k) (z : Z) :
    0 ≤ passProb g t ω z ∧ passProb g t ω z ≤ 1 := by
  by_cases h : g z = some ω
  · simp [passProb, h, ht0, ht1]
  · simp [passProb, h]

theorem fullSurv_nonneg {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) :
    ∀ n h ω, 0 ≤ fullSurv T M g t keep ω n h := by
  intro n
  induction n with
  | zero => intro h ω; simp [fullSurv, hk]
  | succ n ih =>
      intro h ω
      rw [fullSurv]
      apply Finset.sum_nonneg
      intro x _
      apply mul_nonneg (hT h x)
      apply Finset.sum_nonneg
      intro z _
      apply mul_nonneg (hM x z)
      obtain ⟨hp0, hp1⟩ := passProb_bounds g t ht0 ht1 ω z
      have htrue := ih (h ++ [(x,z,true)]) ω
      have hfalse := ih (h ++ [(x,z,false)]) ω
      exact add_nonneg (mul_nonneg hp0 htrue) (mul_nonneg (sub_nonneg.mpr hp1) hfalse)

noncomputable def flagOnly {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (t : ℝ) (keep : Hist X Z → ℝ) (ω : Fin k) :
    ℕ → Hist X Z → ℝ
  | 0, h => keep h
  | n + 1, h => ∑ x, T h x * ∑ z, M x z *
      (1 - passProb g t ω z) * flagOnly T M g t keep ω n (h ++ [(x,z,false)])

theorem fullSurv_ge_flagOnly {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) :
    ∀ n h ω, flagOnly T M g t keep ω n h ≤ fullSurv T M g t keep ω n h := by
  intro n
  induction n with
  | zero => intro h ω; rfl
  | succ n ih =>
      intro h ω
      rw [flagOnly, fullSurv]
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hT h x)
      apply Finset.sum_le_sum
      intro z _
      obtain ⟨hp0, hp1⟩ := passProb_bounds g t ht0 ht1 ω z
      have hfalse := ih (h ++ [(x,z,false)]) ω
      have htrue := fullSurv_nonneg T M g t ht0 ht1 keep hk hT hM n
        (h ++ [(x,z,true)]) ω
      have hprod := mul_le_mul_of_nonneg_left hfalse (sub_nonneg.mpr hp1)
      have hnonneg := mul_nonneg hp0 htrue
      have hbracket :
          (1 - passProb g t ω z) * flagOnly T M g t keep ω n (h ++ [(x,z,false)]) ≤
          passProb g t ω z * fullSurv T M g t keep ω n (h ++ [(x,z,true)]) +
            (1 - passProb g t ω z) * fullSurv T M g t keep ω n (h ++ [(x,z,false)]) := by
        nlinarith
      calc
        M x z * (1 - passProb g t ω z) *
            flagOnly T M g t keep ω n (h ++ [(x,z,false)]) =
          M x z * ((1 - passProb g t ω z) *
            flagOnly T M g t keep ω n (h ++ [(x,z,false)])) := by ring
        _ ≤ M x z * (passProb g t ω z *
              fullSurv T M g t keep ω n (h ++ [(x,z,true)]) +
            (1 - passProb g t ω z) *
              fullSurv T M g t keep ω n (h ++ [(x,z,false)])) :=
          mul_le_mul_of_nonneg_left hbracket (hM x z)

noncomputable def refSurv {X : Type} {Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (keep : Hist X Z → ℝ) : ℕ → Hist X Z → ℝ
  | 0, h => keep h
  | n + 1, h => ∑ x, T h x * ∑ z, M x z *
      refSurv T M keep n (h ++ [(x,z,false)])

theorem refSurv_eq_fullSurv_zero {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (keep : Hist X Z → ℝ) :
    ∀ n h ω, refSurv T M keep n h = fullSurv T M g 0 keep ω n h := by
  intro n
  induction n with
  | zero => intro h ω; rfl
  | succ n ih =>
      intro h ω
      rw [refSurv, fullSurv]
      apply Finset.sum_congr rfl
      intro x _
      apply congrArg (T h x * ·)
      apply Finset.sum_congr rfl
      intro z _
      have hz : passProb g 0 ω z = 0 := by simp [passProb]
      rw [hz, ih]
      ring

noncomputable def weightedFlag {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (b : ℝ) (keep : Hist X Z → ℝ) :
    ℕ → Hist X Z → ℝ
  | n, h => ∑ ω : Fin k,
      b ^ (classCount g h ω) * flagOnly T M g (1-b) keep ω n h

theorem classPower_append_flag {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k))
    (b : ℝ) (h : Hist X Z) (x : X) (z : Z) (ω : Fin k) :
    b ^ classCount g h ω * (if g z = some ω then b else 1) =
      b ^ classCount g (h ++ [(x,z,false)]) ω := by
  rw [classCount_append_flag]
  by_cases hmatch : g z = some ω <;> simp [hmatch, pow_succ]

private theorem weightedFactor_append {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k))
    (b : ℝ) (h : Hist X Z) (x : X) (z : Z) (ω : Fin k) (f : ℝ) :
    b ^ classCount g (h ++ [(x,z,false)]) ω * f =
      b ^ classCount g h ω * ((1 - passProb g (1-b) ω z) * f) := by
  rw [flagFactor]
  by_cases hm : g z = some ω
  · have hc := classCount_append_flag g h x z ω
    rw [hc, if_pos hm]
    simp only [if_pos hm]
    rw [pow_succ]
    ring
  · have hc := classCount_append_flag g h x z ω
    rw [hc, if_neg hm]
    simp only [if_neg hm]
    simp

theorem weighted_double_sum {α β : Type} [Fintype α] [Fintype β]
    (a : α → ℝ) (c : β → ℝ) (f : α → β → ℝ) :
    (∑ i, a i * ∑ j, c j * f i j) =
      ∑ j, c j * ∑ i, a i * f i j := by
  calc
    (∑ i, a i * ∑ j, c j * f i j) =
        ∑ i, ∑ j, a i * (c j * f i j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = ∑ j, ∑ i, a i * (c j * f i j) := by
          rw [Finset.sum_comm]
    _ = ∑ j, c j * ∑ i, a i * f i j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring

theorem weightedFlag_succ {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (b : ℝ) (keep : Hist X Z → ℝ)
    (n : ℕ) (h : Hist X Z) :
    weightedFlag T M g b keep (n+1) h =
      ∑ x, T h x * ∑ z, M x z *
        weightedFlag T M g b keep n (h ++ [(x,z,false)]) := by
  simp only [weightedFlag, flagOnly, mul_assoc]
  calc
    (∑ ω : Fin k, b ^ classCount g h ω *
      ∑ x : X, T h x * ∑ z : Z, M x z *
        ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
          (h ++ [(x,z,false)])))
      = ∑ ω : Fin k, ∑ x : X,
          b ^ classCount g h ω * T h x * ∑ z : Z, M x z *
            ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
              (h ++ [(x,z,false)])) := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ x : X, ∑ ω : Fin k,
          b ^ classCount g h ω * T h x * ∑ z : Z, M x z *
            ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
              (h ++ [(x,z,false)])) := by
          let F : Fin k → X → ℝ := fun ω x =>
            b ^ classCount g h ω * T h x * ∑ z : Z, M x z *
              ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
                (h ++ [(x,z,false)]))
          simpa [F] using
            (Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := F))
    _ = ∑ x : X, T h x * ∑ z : Z, M x z *
          ∑ ω : Fin k, b ^ classCount g h ω *
            ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
              (h ++ [(x,z,false)])) := by
          apply Finset.sum_congr rfl
          intro x _
          calc
            (∑ ω : Fin k, b ^ classCount g h ω * T h x *
              ∑ z : Z, M x z *
                ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
                  (h ++ [(x,z,false)])))
              = T h x * ∑ ω : Fin k, b ^ classCount g h ω *
                  ∑ z : Z, M x z *
                    ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
                      (h ++ [(x,z,false)])) := by
                    calc
                      _ = ∑ ω : Fin k,
                          (b ^ classCount g h ω *
                            ∑ z : Z, M x z *
                              ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
                                (h ++ [(x,z,false)]))) * T h x := by
                              apply Finset.sum_congr rfl
                              intro ω _
                              ring
                      _ = (∑ ω : Fin k, b ^ classCount g h ω *
                            ∑ z : Z, M x z *
                              ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
                                (h ++ [(x,z,false)]))) * T h x := by rw [Finset.sum_mul]
                      _ = T h x * ∑ ω : Fin k, b ^ classCount g h ω *
                            ∑ z : Z, M x z *
                              ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
                                (h ++ [(x,z,false)])) := by ring
            _ = T h x * ∑ z : Z, M x z * ∑ ω : Fin k,
                  b ^ classCount g h ω *
                    ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
                      (h ++ [(x,z,false)])) := by
                    exact congrArg (T h x * ·)
                      (weighted_double_sum (fun ω => b ^ classCount g h ω)
                        (fun z => M x z)
                        (fun ω z => (1 - passProb g (1-b) ω z) *
                          flagOnly T M g (1-b) keep ω n (h ++ [(x,z,false)])))
    _ = ∑ x : X, T h x * ∑ z : Z, M x z *
          weightedFlag T M g b keep n (h ++ [(x,z,false)]) := by
          apply Finset.sum_congr rfl
          intro x _
          apply congrArg (T h x * ·)
          apply Finset.sum_congr rfl
          intro z _
          apply congrArg (M x z * ·)
          rw [weightedFlag]
          apply Finset.sum_congr rfl
          intro ω _
          rw [flagFactor, ← mul_assoc, classPower_append_flag]

theorem count_sum_le {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k))
    (h : Hist X Z) :
    (∑ ω : Fin k, classCount g h ω) ≤ h.length := by
  induction h with
  | nil => simp [classCount]
  | cons e h ih =>
      have hrec : ∀ ω, classCount g (e :: h) ω =
          (if g e.2.1 = some ω then 1 else 0) + classCount g h ω := by
        intro ω
        by_cases heq : g e.2.1 = some ω
        · simp [classCount, heq]
          omega
        · simp [classCount, heq]
      rw [Finset.sum_congr rfl (fun ω _ => hrec ω)]
      rw [Finset.sum_add_distrib]
      have hdelta : (∑ ω : Fin k, if g e.2.1 = some ω then 1 else 0) ≤ 1 := by
        classical
        by_cases hex : ∃ i, g e.2.1 = some i
        · obtain ⟨i, hi⟩ := hex
          have hone : (∑ ω : Fin k, if g e.2.1 = some ω then 1 else 0) = 1 := by
            rw [Finset.sum_eq_single i]
            · simp [hi]
            · intro ω _ hω
              have hne : g e.2.1 ≠ some ω := by
                intro heq
                apply hω
                exact (Option.some.inj (hi.symm.trans heq)).symm
              simp [hne]
            · simp
          rw [hone]
        · have hnone : ∀ i, g e.2.1 ≠ some i := by
            intro i hi
            exact hex ⟨i, hi⟩
          simp [hnone]
      have hsumle := Nat.add_le_add hdelta ih
      simpa [List.length_cons, Nat.add_comm] using hsumle

noncomputable def balancedTarget (k n : ℕ) (b : ℝ) : ℝ :=
    ((k - n % k : ℕ) : ℝ) * b ^ (n / k) +
      ((n % k : ℕ) : ℝ) * b ^ (n / k + 1)

/-- All-FLAG reference histories retain the sharp balanced mass. -/
theorem weightedFlag_lower {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z)
    (hkpos : 0 < k) (N : ℕ) :
    ∀ n h, h.length + n = N →
      balancedTarget k N b * refSurv T M keep n h ≤ weightedFlag T M g b keep n h := by
  intro n
  induction n with
  | zero =>
      intro h hlen
      have hsum := count_sum_le g h
      have hcounts : ∑ ω : Fin k, classCount g h ω ≤ N := by omega
      let counts : Fin k → ℕ := fun ω => classCount g h ω
      have hb := ControlStack.AdaptiveBalance.aggregate_balanced_budget
        b hb0 hb1 k (N / k) (N % k) hkpos (Nat.mod_lt N hkpos) counts
        (by
          calc
            ∑ ω : Fin k, counts ω ≤ N := by simpa [counts] using hcounts
            _ = N % k + k * (N / k) := (Nat.mod_add_div N k).symm
            _ = k * (N / k) + N % k := Nat.add_comm _ _)
      simp [weightedFlag, flagOnly, refSurv]
      dsimp [balancedTarget]
      have hk' := hk h
      have hsumPow : ∑ ω : Fin k, b ^ classCount g h ω = ∑ ω : Fin k, b ^ counts ω := by
        simp [counts]
      rw [← Finset.sum_mul, hsumPow]
      exact mul_le_mul_of_nonneg_right hb hk'
  | succ n ih =>
      intro h hlen
      rw [weightedFlag_succ, refSurv]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      calc
        balancedTarget k N b *
            (T h x * ∑ z, M x z * refSurv T M keep n (h ++ [(x,z,false)]))
          = T h x * ∑ z, M x z *
              (balancedTarget k N b * refSurv T M keep n (h ++ [(x,z,false)])) := by
                calc
                  _ = T h x * (balancedTarget k N b *
                      ∑ z, M x z * refSurv T M keep n (h ++ [(x,z,false)])) := by ring
                  _ = T h x * ∑ z, balancedTarget k N b *
                      (M x z * refSurv T M keep n (h ++ [(x,z,false)])) := by
                        rw [Finset.mul_sum]
                  _ = T h x * ∑ z, M x z *
                      (balancedTarget k N b * refSurv T M keep n (h ++ [(x,z,false)])) := by
                        congr 1
                        apply Finset.sum_congr rfl
                        intro z _
                        ring
        _ ≤ T h x * ∑ z, M x z *
              weightedFlag T M g b keep n (h ++ [(x,z,false)]) := by
                apply mul_le_mul_of_nonneg_left _ (hT h x)
                apply Finset.sum_le_sum
                intro z _
                apply mul_le_mul_of_nonneg_left _ (hM x z)
                apply ih
                simp [List.length_append] at hlen ⊢
                omega

/-- Sharp aggregate survival under an all-FLAG acceptance contract. The decoder
may return `none` on views outside the seed classes. -/
theorem sharp_survival {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z)
    (hkpos : 0 < k) (n : ℕ)
    (hacc : refSurv T M keep n [] = 1) :
    balancedTarget k n (1-t) ≤
      ∑ ω : Fin k, fullSurv T M g t keep ω n [] := by
  have hb0 : 0 ≤ 1-t := by linarith
  have hb1 : 1-t ≤ 1 := by linarith
  have hcore := weightedFlag_lower T M g (1-t) hb0 hb1 keep hk hT hM hkpos n
    n [] (by simp)
  rw [hacc] at hcore
  have hroot : weightedFlag T M g (1-t) keep n [] =
      ∑ ω : Fin k, flagOnly T M g t keep ω n [] := by
    simp [weightedFlag, classCount]
  have hflag := calc
      balancedTarget k n (1-t) ≤ weightedFlag T M g (1-t) keep n [] := by
        simpa using hcore
      _ = ∑ ω : Fin k, flagOnly T M g t keep ω n [] := hroot
  have hfull : (∑ ω : Fin k, flagOnly T M g t keep ω n []) ≤
      ∑ ω : Fin k, fullSurv T M g t keep ω n [] := by
    apply Finset.sum_le_sum
    intro ω _
    exact fullSurv_ge_flagOnly T M g t ht0 ht1 keep hk hT hM n [] ω
  exact hflag.trans hfull

/-- Uniform seed averaging turns the sharp survival sum into a risk bound,
assuming each seed has deployment catastrophe probability at least `t`. -/
theorem sharp_uniform_cat {k : ℕ} (hkpos : 0 < k) (t : ℝ) (ht0 : 0 ≤ t)
    (n : ℕ) (surv cat : Fin k → ℝ)
    (hsurv : ∀ i, 0 ≤ surv i)
    (hcat : ∀ i, t ≤ cat i)
    (hsum : balancedTarget k n (1-t) ≤ ∑ i : Fin k, surv i) :
    (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
      (1 / (k : ℝ)) * ∑ i : Fin k, surv i * cat i := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hrec : ∀ i : Fin k, t * surv i ≤ surv i * cat i := by
    intro i
    calc
      t * surv i ≤ cat i * surv i := mul_le_mul_of_nonneg_right (hcat i) (hsurv i)
      _ = surv i * cat i := by ring
  have hsumcat : t * ∑ i : Fin k, surv i ≤ ∑ i : Fin k, surv i * cat i := by
    calc
      t * ∑ i : Fin k, surv i = ∑ i : Fin k, t * surv i := by rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin k, surv i * cat i := Finset.sum_le_sum (fun i _ => hrec i)
  have hscale := mul_le_mul_of_nonneg_left hsumcat (by positivity : 0 ≤ (1 / (k : ℝ)))
  have htarg : (t / (k : ℝ)) * balancedTarget k n (1-t) =
      (1 / (k : ℝ)) * (t * balancedTarget k n (1-t)) := by ring
  have hsrhs : (1 / (k : ℝ)) * (t * ∑ i : Fin k, surv i) ≤
      (1 / (k : ℝ)) * ∑ i : Fin k, surv i * cat i := hscale
  calc
    (t / (k : ℝ)) * balancedTarget k n (1-t) =
        (1 / (k : ℝ)) * (t * balancedTarget k n (1-t)) := htarg
    _ ≤ (1 / (k : ℝ)) * (t * ∑ i : Fin k, surv i) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (1 / (k : ℝ)))
      exact mul_le_mul_of_nonneg_left hsum ht0
    _ ≤ (1 / (k : ℝ)) * ∑ i : Fin k, surv i * cat i := hsrhs

/-- Index the unique seed class matched by a decoder output; unmatched outputs map to None. -/
noncomputable def seedDecoder {X C Z : Type} [DecidableEq C] {k : ℕ}
    (seed : Fin k → X) (c : X → C) (g : Z → C) (z : Z) : Option (Fin k) := by
  classical
  exact if h : ∃ i, g z = c (seed i) then some (Classical.choose h) else none

theorem seedDecoder_eq_some_iff {X C Z : Type} [DecidableEq C] {k : ℕ}
    (seed : Fin k → X) (c : X → C) (g : Z → C)
    (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (z : Z) (i : Fin k) :
    seedDecoder seed c g z = some i ↔ g z = c (seed i) := by
  classical
  by_cases hex : ∃ j, g z = c (seed j)
  · let j := Classical.choose hex
    have hj := Classical.choose_spec hex
    unfold seedDecoder
    rw [dif_pos hex]
    constructor
    · intro hs
      have hji : Classical.choose hex = i := Option.some.inj hs
      subst i
      exact hj
    · intro hi
      congr 1
      apply hinj
      exact hj.symm.trans hi
  · unfold seedDecoder
    rw [dif_neg hex]
    constructor
    · intro h; cases h
    · intro hi
      exact False.elim (hex ⟨i, hi⟩)

def classPass {X C Z : Type} [DecidableEq C]
    (c : X → C) (g : Z → C) (t : ℝ) (x : X) (z : Z) : ℝ :=
  if g z = c x then t else 0

theorem seedDecoder_pass_eq {X C Z : Type} [DecidableEq C] {k : ℕ}
    (seed : Fin k → X) (c : X → C) (g : Z → C) (t : ℝ)
    (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (i : Fin k) (z : Z) :
    passProb (seedDecoder seed c g) t i z = classPass c g t (seed i) z := by
  by_cases h : g z = c (seed i)
  · have hd := (seedDecoder_eq_some_iff seed c g hinj z i).2 h
    simp [passProb, classPass, hd, h]
  · have hd : seedDecoder seed c g z ≠ some i := by
      intro hd
      exact h ((seedDecoder_eq_some_iff seed c g hinj z i).1 hd)
    simp [passProb, classPass, hd, h]


noncomputable def passSurv {X : Type} {Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ)
    (keep : Hist X Z → ℝ) : ℕ → Hist X Z → ℝ
  | 0, h => keep h
  | n + 1, h => ∑ x, T h x * ∑ z, M x z *
      (φ z * passSurv T M φ keep n (h ++ [(x,z,true)]) +
       (1-φ z) * passSurv T M φ keep n (h ++ [(x,z,false)]))

theorem refSurv_eq_passSurv_zero {X : Type} {Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) :
    ∀ n h, refSurv T M keep n h = passSurv T M (fun _ => 0) keep n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      intro h
      rw [refSurv, passSurv]
      apply Finset.sum_congr rfl
      intro x _
      apply congrArg (T h x * ·)
      apply Finset.sum_congr rfl
      intro z _
      rw [ih (h ++ [(x,z,false)])]
      ring

theorem fullSurv_eq_passSurv_seed {X C Z : Type} [DecidableEq C]
    [Fintype X] [Fintype Z] {k : ℕ}
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (seed : Fin k → X) (c : X → C) (g : Z → C) (t : ℝ)
    (hinj : ∀ i j, c (seed i) = c (seed j) → i = j)
    (keep : Hist X Z → ℝ) (i : Fin k) :
    ∀ n h, fullSurv T M (seedDecoder seed c g) t keep i n h =
      passSurv T M (classPass c g t (seed i)) keep n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      intro h
      rw [fullSurv, passSurv]
      apply Finset.sum_congr rfl
      intro x _
      apply congrArg (T h x * ·)
      apply Finset.sum_congr rfl
      intro z _
      rw [seedDecoder_pass_eq seed c g t hinj i z]
      rw [ih (h ++ [(x,z,true)]), ih (h ++ [(x,z,false)])]

theorem sharp_seedset_survival {X C Z : Type} [DecidableEq C]
    [Fintype X] [Fintype Z] {k : ℕ}
    (S : Finset X) (e : Fin k ≃ {x // x ∈ S})
    (c : X → C) (g : Z → C)
    (hinjS : Set.InjOn c (S : Set X))
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z)
    (hkpos : 0 < k) (n : ℕ)
    (hacc : refSurv T M keep n [] = 1) :
    balancedTarget k n (1-t) ≤
      ∑ i : Fin k, passSurv T M (classPass c g t ((e i).val)) keep n [] := by
  have hclass : ∀ i j, c ((e i).val) = c ((e j).val) → i = j := by
    intro i j hij
    have hx : (e i).val = (e j).val :=
      hinjS (e i).property (e j).property hij
    apply e.injective
    exact Subtype.ext hx
  let dec : Z → Option (Fin k) := seedDecoder (fun i => (e i).val) c g
  have hsurv := sharp_survival T M dec t ht0 ht1 keep hk hT hM hkpos n hacc
  calc
    balancedTarget k n (1-t) ≤
        ∑ i : Fin k, fullSurv T M dec t keep i n [] := hsurv
    _ = ∑ i : Fin k, passSurv T M (classPass c g t ((e i).val)) keep n [] := by
        apply Finset.sum_congr rfl
        intro i _
        exact fullSurv_eq_passSurv_seed T M (fun i => (e i).val) c g t hclass keep i n []

theorem sharp_seedset_catRisk {X C Z : Type} [DecidableEq C]
    [Fintype X] [Fintype Z] {k : ℕ}
    (S : Finset X) (e : Fin k ≃ {x // x ∈ S})
    (c : X → C) (g : Z → C)
    (hinjS : Set.InjOn c (S : Set X))
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z)
    (hkpos : 0 < k) (n : ℕ)
    (hacc : refSurv T M keep n [] = 1)
    (cat : Fin k → ℝ) (hcat : ∀ i, t ≤ cat i) :
    (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
      (1 / (k : ℝ)) * ∑ i : Fin k,
        passSurv T M (classPass c g t ((e i).val)) keep n [] * cat i := by
  let surv : Fin k → ℝ := fun i => passSurv T M (classPass c g t ((e i).val)) keep n []
  have hsum : balancedTarget k n (1-t) ≤ ∑ i : Fin k, surv i := by
    simpa [surv] using sharp_seedset_survival S e c g hinjS T M t ht0 ht1 keep hk hT hM hkpos n hacc
  have hnonneg : ∀ i, 0 ≤ surv i := by
    intro i
    have hclass : ∀ i j, c ((e i).val) = c ((e j).val) → i = j := by
      intro i j hij
      have hx : (e i).val = (e j).val :=
        hinjS (e i).property (e j).property hij
      apply e.injective
      exact Subtype.ext hx
    let dec : Z → Option (Fin k) := seedDecoder (fun i => (e i).val) c g
    have hfull := fullSurv_nonneg T M dec t ht0 ht1 keep hk hT hM n [] i
    have heq := fullSurv_eq_passSurv_seed T M (fun i => (e i).val) c g t hclass keep i n []
    simpa [surv] using heq ▸ hfull
  exact sharp_uniform_cat hkpos t ht0 n surv cat hnonneg hcat hsum

noncomputable def seedEquiv {X : Type} (S : Finset X) (k : ℕ)
    (hcard : S.card = k) : Fin k ≃ {x // x ∈ S} :=
  (S.equivFinOfCardEq hcard).symm


end ControlStack.AdaptiveGeneric
