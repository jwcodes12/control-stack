/-
F6: monitor-flag-triggered auditing with a HARD first-come budget, against attackers who may see everything that
has already happened (their own actions, every flag, every catch, hence the budget state).

Round model (the `val` kernel semantics of `Core/Leakage.lean`). Visible round output `AOut Bool`:
(attack bit, monitor flag, caught). A flagged round is audited while fewer than Bf EARLIER rounds were flagged; the
flag budget is exhausted once `flagCount ≥ Bf`. Catch is absorbing (payoffs carry `liveInd caughtFlag`).

Results.
1. `val_le_potential` / `cval_le_potential`: the generic potential (supermartingale) bound for `val` and `cval`.
   `Leakage.val_le_cval` is the instance W n g = cval c pay n g.
2. `flag_pre_bound`. Premise `hrec` (CONDITIONAL recall): at every full history at which the flag budget is not
   exhausted, P(attack now and not caught | history) ≤ (1 − ρ) · P(attack now | history).
   Conclusion: P(≥ k attacks, at least k of them made while budget remained, never caught) ≤ (1 − ρ)^k.
   No hiding assumption: the kernel is arbitrary, so the attacker may condition on the whole past.
3. `flag_exhaust_bound`. Premise `hfp`: at every pre-exhaustion history, P(flag now and not caught | history) ≤ α.
   Conclusion: P(budget exhausted, never caught) ≤ `binTail α Bf N 0` = P(Binomial(N, α) ≥ Bf).
4. `flag_total_bound`: P(≥ k attacks, never caught) ≤ (1 − ρ)^k + binTail α Bf N 0. This is the statement about ALL
   attacks; the second term is the price of exhaustion and cannot be dropped (`SplitAudit.exhaustion_witness`).

Limits (what is NOT claimed).
- `hrec` is a per-history premise. It already contains the one-round version of the conclusion; the theorem adds the
  k-fold compounding against adaptive play and the exact accounting of exhaustion. A measured average recall does
  not imply `hrec` (`SplitAudit.average_recall_witness`).
- The budget is a hard first-come cap. Threshold-ranked or paced budgets are different protocols and are not covered.
- A flagged attack round that is audited is assumed caught through `hrec` (ρ is the recall of flag-then-audit, not of
  the monitor alone).
- Classical mathematics (optional stopping for a product potential; a binomial tail by its recursion). No novelty
  is claimed.
-/
import ControlStack.Families.F6.ReservedAudit

namespace ControlStack.FlagBudget

open Finset ControlStack.Leakage ControlStack.Covert

/-! ## 1. Generic potential bounds -/

section Potential

variable {Y O : Type} [Fintype Y] [Fintype O]

/-- **Potential bound for `val`.** If W dominates the payoff at the end and is a supermartingale along the kernel
(with the hidden part summed out), the value is at most W. -/
theorem val_le_potential (K : List (Y × O) → Y × O → ℝ) (pay : List O → ℝ) (W : ℕ → List O → ℝ)
    (hK0 : ∀ h z, 0 ≤ K h z) (h0 : ∀ g, pay g ≤ W 0 g)
    (hstep : ∀ n h, ∑ o, (∑ y, K h (y, o)) * W n (h.map Prod.snd ++ [o]) ≤ W (n + 1) (h.map Prod.snd)) :
    ∀ n h, val K pay n h ≤ W n (h.map Prod.snd) := by
  intro n; induction n with
  | zero => intro h; exact h0 _
  | succ n ih =>
    intro h
    simp only [Leakage.val]
    calc ∑ y, ∑ o, K h (y, o) * val K pay n (h ++ [(y, o)])
        ≤ ∑ y, ∑ o, K h (y, o) * W n (h.map Prod.snd ++ [o]) := by
          gcongr with y _ o _
          · exact hK0 h (y, o)
          · simpa using ih (h ++ [(y, o)])
      _ = ∑ o, (∑ y, K h (y, o)) * W n (h.map Prod.snd ++ [o]) := by
          rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
      _ ≤ _ := hstep n h

/-- **Potential bound for `cval`** (the same statement for a visible-transcript certificate). -/
theorem cval_le_potential (c : List O → O → ℝ) (B : List O → ℝ) (W : ℕ → List O → ℝ)
    (hc0 : ∀ g o, 0 ≤ c g o) (h0 : ∀ g, B g ≤ W 0 g)
    (hstep : ∀ n g, ∑ o, c g o * W n (g ++ [o]) ≤ W (n + 1) g) :
    ∀ n g, cval c B n g ≤ W n g := by
  intro n; induction n with
  | zero => intro g; exact h0 g
  | succ n ih =>
    intro g
    simp only [cval]
    exact le_trans (Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (ih _) (hc0 g o)) (hstep n g)

/-- `val` is monotone in the payoff -/
theorem val_mono (K : List (Y × O) → Y × O → ℝ) (pay pay' : List O → ℝ) (hK0 : ∀ h z, 0 ≤ K h z)
    (hpp : ∀ g, pay g ≤ pay' g) : ∀ n h, val K pay n h ≤ val K pay' n h := by
  intro n; induction n with
  | zero => intro h; exact hpp _
  | succ n ih =>
    intro h
    simp only [Leakage.val]
    gcongr with y _ o _
    · exact hK0 h (y, o)
    · exact ih _

/-- `val` is additive in the payoff -/
theorem val_add (K : List (Y × O) → Y × O → ℝ) (pay pay' : List O → ℝ) :
    ∀ n h, val K (fun g => pay g + pay' g) n h = val K pay n h + val K pay' n h := by
  intro n; induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    simp only [Leakage.val, ih, mul_add, Finset.sum_add_distrib]

end Potential

/-! ## 2. Bookkeeping on visible transcripts -/

section Book

/-- number of flagged rounds so far -/
def flagCount (t : List (AOut Bool)) : ℕ := t.countP (fun o => o.2.1)

/-- number of attack rounds that began with fewer than Bf earlier flags (j = flags before the list starts) -/
def preAttAux (Bf : ℕ) : ℕ → List (AOut Bool) → ℕ
  | _, [] => 0
  | j, o :: t => (if o.1 && decide (j < Bf) then 1 else 0) + preAttAux Bf (j + (if o.2.1 then 1 else 0)) t

/-- attacks made while the flag budget was not exhausted -/
def preAtt (Bf : ℕ) (t : List (AOut Bool)) : ℕ := preAttAux Bf 0 t

theorem flagCount_snoc (t : List (AOut Bool)) (o : AOut Bool) :
    flagCount (t ++ [o]) = flagCount t + (if o.2.1 then 1 else 0) := by
  unfold flagCount
  rw [List.countP_append]
  cases h : o.2.1 <;> simp [h]

theorem flagCount_cons (j : ℕ) (o : AOut Bool) (t : List (AOut Bool)) :
    j + flagCount (o :: t) = (j + (if o.2.1 then 1 else 0)) + flagCount t := by
  unfold flagCount
  cases h : o.2.1 <;> simp [h]
  omega

theorem preAttAux_snoc (Bf : ℕ) (t : List (AOut Bool)) (o : AOut Bool) :
    ∀ j, preAttAux Bf j (t ++ [o]) =
      preAttAux Bf j t + (if o.1 && decide (j + flagCount t < Bf) then 1 else 0) := by
  induction t with
  | nil => intro j; simp [preAttAux, flagCount]
  | cons o' t ih =>
    intro j
    simp only [List.cons_append, preAttAux, ih]
    rw [flagCount_cons]
    ring

theorem preAtt_snoc (Bf : ℕ) (t : List (AOut Bool)) (o : AOut Bool) :
    preAtt Bf (t ++ [o]) = preAtt Bf t + (if o.1 && decide (flagCount t < Bf) then 1 else 0) := by
  unfold preAtt
  rw [preAttAux_snoc]
  simp

theorem live_snoc {Z : Type} (t : List (AOut Z)) (o : AOut Z) :
    liveInd caughtFlag (t ++ [o]) = liveInd caughtFlag t * (if o.2.2 then 0 else 1) := by
  simp only [liveInd, List.all_append, List.all_cons, List.all_nil, Bool.and_true, caughtFlag]
  by_cases hs : o.2.2 <;> by_cases hg : (t.all fun o => !o.2.2) = true <;> simp [hs, hg]

variable {N : ℕ} {Z : Type}

theorem attacked_snoc (t : List (AOut Z)) (o : AOut Z) (i : ℕ) :
    attacked (t ++ [o]) i = if i < t.length then attacked t i else if i = t.length then o.1 else false := by
  unfold attacked
  rcases lt_trichotomy i t.length with h | h | h
  · rw [List.getElem?_append_left h]; simp [h]
  · rw [List.getElem?_append_right (by omega), h, Nat.sub_self]; simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    have h1 : ¬ i < t.length := by omega
    have h2 : i ≠ t.length := by omega
    simp [h1, h2]

theorem attackSet_nil : attackSet (N := N) ([] : List (AOut Z)) = ∅ := by
  ext i; simp [attackSet, attacked]

/-- one more round adds at most one attack -/
theorem card_attackSet_snoc_le (t : List (AOut Z)) (o : AOut Z) :
    (attackSet (N := N) (t ++ [o])).card ≤ (attackSet (N := N) t).card + (if o.1 then 1 else 0) := by
  have hsub : attackSet (N := N) (t ++ [o]) ⊆
      attackSet (N := N) t ∪ univ.filter (fun i : Fin N => (i : ℕ) = t.length ∧ o.1 = true) := by
    intro i hi
    simp only [attackSet, mem_filter, mem_univ, true_and, mem_union] at hi ⊢
    rw [attacked_snoc] at hi
    by_cases h1 : (i : ℕ) < t.length
    · left; simpa [h1] using hi
    · by_cases h2 : (i : ℕ) = t.length
      · right; exact ⟨h2, by simpa [h1, h2] using hi⟩
      · simp [h1, h2] at hi
  have hone : (univ.filter (fun i : Fin N => (i : ℕ) = t.length ∧ o.1 = true)).card ≤ (if o.1 then 1 else 0) := by
    by_cases ho : o.1 = true
    · simp only [ho, and_true, ite_true]
      apply Finset.card_le_one.2
      intro a ha b hb
      simp only [mem_filter, mem_univ, true_and] at ha hb
      exact Fin.ext (ha.trans hb.symm)
    · simp [ho]
  calc _ ≤ (attackSet (N := N) t ∪ univ.filter (fun i : Fin N => (i : ℕ) = t.length ∧ o.1 = true)).card :=
        card_le_card hsub
    _ ≤ _ := le_trans (card_union_le _ _) (Nat.add_le_add_left hone _)

/-- while the flag budget is not exhausted, every attack so far was a pre-exhaustion attack -/
theorem card_attackSet_le_preAtt (Bf : ℕ) (t : List (AOut Bool)) (h : flagCount t < Bf) :
    (attackSet (N := N) t).card ≤ preAtt Bf t := by
  induction t using List.reverseRecOn with
  | nil => simp [attackSet_nil]
  | append_singleton t o ih =>
    rw [flagCount_snoc] at h
    have ht : flagCount t < Bf := by omega
    have h1 := card_attackSet_snoc_le (N := N) t o
    have h2 := ih ht
    rw [preAtt_snoc]
    cases ho : o.1 <;> simp [ho, ht] at h1 ⊢ <;> omega

end Book

/-! ## 3. The binomial tail -/

section Tail

/-- P(at least Bf − j further successes in n Bernoulli(α) trials), by its recursion: the probability that a flag
count now at j reaches Bf within n more rounds when each round flags with probability α. -/
noncomputable def binTail (α : ℝ) (Bf : ℕ) : ℕ → ℕ → ℝ
  | 0, j => if Bf ≤ j then 1 else 0
  | n + 1, j => if Bf ≤ j then 1 else α * binTail α Bf n (j + 1) + (1 - α) * binTail α Bf n j

theorem binTail_of_le (α : ℝ) (Bf : ℕ) (n j : ℕ) (h : Bf ≤ j) : binTail α Bf n j = 1 := by
  cases n <;> simp [binTail, h]

theorem binTail_nonneg (α : ℝ) (Bf : ℕ) (h0 : 0 ≤ α) (h1 : α ≤ 1) : ∀ n j, 0 ≤ binTail α Bf n j := by
  intro n; induction n with
  | zero => intro j; simp only [binTail]; split_ifs <;> norm_num
  | succ n ih =>
    intro j; simp only [binTail]; split_ifs
    · norm_num
    · have := ih (j + 1); have := ih j
      have : 0 ≤ 1 - α := by linarith
      positivity

theorem binTail_le_one (α : ℝ) (Bf : ℕ) (h0 : 0 ≤ α) (h1 : α ≤ 1) : ∀ n j, binTail α Bf n j ≤ 1 := by
  intro n; induction n with
  | zero => intro j; simp only [binTail]; split_ifs <;> norm_num
  | succ n ih =>
    intro j; simp only [binTail]; split_ifs
    · norm_num
    · have ha := ih (j + 1); have hb := ih j
      nlinarith

/-- the tail is monotone in the current flag count -/
theorem binTail_mono (α : ℝ) (Bf : ℕ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    ∀ n j, binTail α Bf n j ≤ binTail α Bf n (j + 1) := by
  intro n; induction n with
  | zero =>
    intro j; simp only [binTail]
    by_cases h : Bf ≤ j
    · simp [h, Nat.le_succ_of_le h]
    · simp only [h, ite_false]; split_ifs <;> norm_num
  | succ n ih =>
    intro j
    by_cases h : Bf ≤ j + 1
    · rw [binTail_of_le α Bf (n + 1) (j + 1) h]; exact binTail_le_one α Bf h0 h1 _ _
    · have hj : ¬ Bf ≤ j := by omega
      simp only [binTail, h, hj, ite_false]
      have ha := ih (j + 1); have hb := ih j
      have : 0 ≤ 1 - α := by linarith
      nlinarith

end Tail

/-! ## 4. Success events and the two potentials -/

section Events

variable {N : ℕ}

/-- ≥ k attacks and never caught -/
noncomputable def totSucc (k : ℕ) (t : List (AOut Bool)) : ℝ :=
  (if k ≤ (attackSet (N := N) t).card then 1 else 0) * liveInd caughtFlag t

/-- ≥ k attacks, at least k of them made while the flag budget remained, and never caught -/
noncomputable def preSucc (k Bf : ℕ) (t : List (AOut Bool)) : ℝ :=
  (if k ≤ (attackSet (N := N) t).card ∧ k ≤ preAtt Bf t then 1 else 0) * liveInd caughtFlag t

/-- the flag budget is exhausted and the attacker has not been caught -/
noncomputable def exhLive (Bf : ℕ) (t : List (AOut Bool)) : ℝ :=
  (if Bf ≤ flagCount t then 1 else 0) * liveInd caughtFlag t

theorem totSucc_nonneg (k : ℕ) (t : List (AOut Bool)) : 0 ≤ totSucc (N := N) k t :=
  mul_nonneg (by split_ifs <;> norm_num) (liveInd_nonneg _ _)

theorem preSucc_nonneg (k Bf : ℕ) (t : List (AOut Bool)) : 0 ≤ preSucc (N := N) k Bf t :=
  mul_nonneg (by split_ifs <;> norm_num) (liveInd_nonneg _ _)

theorem exhLive_nonneg (Bf : ℕ) (t : List (AOut Bool)) : 0 ≤ exhLive Bf t :=
  mul_nonneg (by split_ifs <;> norm_num) (liveInd_nonneg _ _)

/-- **Decomposition of the failure event.** A successful attack either made k attacks while budget remained, or
the budget was exhausted (and the attacker was not caught). -/
theorem totSucc_le (k Bf : ℕ) (t : List (AOut Bool)) :
    totSucc (N := N) k t ≤ preSucc (N := N) k Bf t + exhLive Bf t := by
  unfold totSucc preSucc exhLive
  have hl := liveInd_nonneg caughtFlag t
  by_cases hk : k ≤ (attackSet (N := N) t).card
  · by_cases he : Bf ≤ flagCount t
    · simp only [hk, he, ite_true, true_and]
      split_ifs <;> nlinarith
    · have hp : k ≤ preAtt Bf t := le_trans hk (card_attackSet_le_preAtt Bf t (by omega))
      simp [hk, hp, he]
  · simp only [hk, false_and, ite_false, zero_mul, zero_add]
    split_ifs <;> nlinarith

/-- potential for pre-exhaustion attacks: (1 − ρ) per attack still needed -/
noncomputable def W1 (k Bf : ℕ) (ρ : ℝ) (g : List (AOut Bool)) : ℝ :=
  liveInd caughtFlag g * (1 - ρ) ^ (k - preAtt Bf g)

/-- potential for exhaustion: the binomial tail from the current flag count -/
noncomputable def W2 (α : ℝ) (Bf : ℕ) (n : ℕ) (g : List (AOut Bool)) : ℝ :=
  liveInd caughtFlag g * binTail α Bf n (flagCount g)

theorem live_cases (g : List (AOut Bool)) : liveInd caughtFlag g = 0 ∨ liveInd caughtFlag g = 1 := by
  unfold liveInd; split_ifs <;> simp

theorem sum_aout (F : AOut Bool → ℝ) :
    ∑ o, F o = F (true, true, true) + F (true, true, false) + F (true, false, true) + F (true, false, false) +
      F (false, true, true) + F (false, true, false) + F (false, false, true) + F (false, false, false) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- **One round of the pre-exhaustion potential.** `q` is the visible next-output weight at history g; only its
non-catch entries matter. `A` bounds the attack mass: the uncaught attack mass is ≤ A always and ≤ (1 − ρ)·A while
budget remains, and A plus the uncaught non-attack mass is ≤ 1. -/
theorem pre_step (k Bf : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (g : List (AOut Bool)) (q : AOut Bool → ℝ) (A : ℝ)
    (hq0 : ∀ o, 0 ≤ q o)
    (hA : q (true, true, false) + q (true, false, false) ≤ A)
    (hrec : flagCount g < Bf → q (true, true, false) + q (true, false, false) ≤ (1 - ρ) * A)
    (hsum : A + q (false, true, false) + q (false, false, false) ≤ 1) :
    ∑ o, q o * W1 k Bf ρ (g ++ [o]) ≤ W1 k Bf ρ g := by
  have hx0 : 0 ≤ 1 - ρ := by linarith
  have hx1 : 1 - ρ ≤ 1 := by linarith
  have h1 := hq0 (true, true, false); have h2 := hq0 (true, false, false)
  have h3 := hq0 (false, true, false); have h4 := hq0 (false, false, false)
  rw [sum_aout]
  simp only [W1, live_snoc, preAtt_snoc, ite_true, Bool.false_eq_true, ite_false, mul_zero, mul_one, zero_mul,
    zero_add, add_zero, Bool.true_and, Bool.false_and]
  rcases live_cases g with hl | hl
  · simp [hl]
  · rw [hl]
    simp only [one_mul]
    by_cases hb : flagCount g < Bf
    · simp only [hb, decide_true, ite_true]
      by_cases hk : k ≤ preAtt Bf g
      · have e1 : k - preAtt Bf g = 0 := by omega
        have e2 : k - (preAtt Bf g + 1) = 0 := by omega
        rw [e1, e2]; simp only [pow_zero, mul_one]
        linarith
      · have e : k - preAtt Bf g = (k - (preAtt Bf g + 1)) + 1 := by omega
        rw [e, pow_succ]
        set P := (1 - ρ) ^ (k - (preAtt Bf g + 1)) with hP
        have hP0 : 0 ≤ P := pow_nonneg hx0 _
        have ha := mul_le_mul_of_nonneg_left (hrec hb) hP0
        have hb' := mul_le_mul_of_nonneg_left hsum (mul_nonneg hP0 hx0)
        nlinarith
    · simp only [hb, decide_false, Bool.false_eq_true, ite_false, add_zero]
      set P := (1 - ρ) ^ (k - preAtt Bf g) with hP
      have hP0 : 0 ≤ P := pow_nonneg hx0 _
      have hb' := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hA le_rfl) le_rfl |>.trans hsum) hP0
      nlinarith

/-- **One round of the exhaustion potential.** While budget remains, the uncaught flagged mass is ≤ α. -/
theorem tail_step (α : ℝ) (Bf : ℕ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) (g : List (AOut Bool)) (q : AOut Bool → ℝ)
    (hq0 : ∀ o, 0 ≤ q o)
    (hsum : q (true, true, false) + q (true, false, false) + q (false, true, false) + q (false, false, false) ≤ 1)
    (hfp : flagCount g < Bf → q (true, true, false) + q (false, true, false) ≤ α) :
    ∑ o, q o * W2 α Bf n (g ++ [o]) ≤ W2 α Bf (n + 1) g := by
  have h1 := hq0 (true, true, false); have h2 := hq0 (true, false, false)
  have h3 := hq0 (false, true, false); have h4 := hq0 (false, false, false)
  rw [sum_aout]
  simp only [W2, live_snoc, flagCount_snoc, ite_true, Bool.false_eq_true, ite_false, mul_zero, mul_one, zero_mul,
    zero_add, add_zero]
  rcases live_cases g with hl | hl
  · simp [hl]
  · rw [hl]
    simp only [one_mul]
    by_cases hb : Bf ≤ flagCount g
    · rw [binTail_of_le α Bf n _ (Nat.le_succ_of_le hb), binTail_of_le α Bf n _ hb,
        binTail_of_le α Bf (n + 1) _ hb]
      linarith
    · have hlt : flagCount g < Bf := by omega
      have hT0 := binTail_nonneg α Bf hα0 hα1 n (flagCount g)
      have hT1 := binTail_mono α Bf hα0 hα1 n (flagCount g)
      have hx := hfp hlt
      simp only [binTail, hb, ite_false]
      set T0 := binTail α Bf n (flagCount g)
      set T1 := binTail α Bf n (flagCount g + 1)
      nlinarith [mul_nonneg (sub_nonneg.2 hsum) hT0, mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hT1)]

end Events

/-! ## 5. Bounds for an arbitrary kernel -/

section Kernel

variable {N : ℕ} {Y : Type} [Fintype Y]

theorem vis_sum_le (K : List (Y × AOut Bool) → Y × AOut Bool → ℝ) (h : List (Y × AOut Bool))
    (hK1 : ∑ z, K h z ≤ 1) : ∑ o, ∑ y, K h (y, o) ≤ 1 := by
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]; exact hK1

/-- **Flag-triggered auditing, pre-exhaustion attacks.** Adversary class: ADAPTIVE_FEEDBACK with the whole history observable (the
kernel is arbitrary, so the attacker may condition on every earlier action, flag, catch and hidden state). Premise `hrec`: at
every full history with fewer than Bf flags, the probability of attacking now without being caught is at most
(1 − ρ) times the probability of attacking now. Then
P(≥ k attacks, ≥ k of them made while budget remained, never caught) ≤ (1 − ρ)^k. -/
theorem flag_pre_bound (k Bf : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (K : List (Y × AOut Bool) → Y × AOut Bool → ℝ)
    (hK0 : ∀ h z, 0 ≤ K h z) (hK1 : ∀ h, ∑ z, K h z ≤ 1)
    (hrec : ∀ h, flagCount (h.map Prod.snd) < Bf →
      ∑ y, ∑ f, K h (y, (true, f, false)) ≤ (1 - ρ) * ∑ y, ∑ f, ∑ c, K h (y, (true, f, c))) :
    val K (preSucc (N := N) k Bf) N [] ≤ (1 - ρ) ^ k := by
  have hx0 : 0 ≤ 1 - ρ := by linarith
  have h := val_le_potential K (preSucc (N := N) k Bf) (fun _ => W1 k Bf ρ) hK0 (by
      intro g
      unfold preSucc W1
      have hl := liveInd_nonneg caughtFlag g
      by_cases hk : k ≤ (attackSet (N := N) g).card ∧ k ≤ preAtt Bf g
      · have e : k - preAtt Bf g = 0 := by omega
        simp [hk, e]
      · simp only [hk, ite_false, zero_mul]
        exact mul_nonneg hl (pow_nonneg hx0 _)) (by
      intro n h
      set q : AOut Bool → ℝ := fun o => ∑ y, K h (y, o) with hq
      have hq0 : ∀ o, 0 ≤ q o := fun o => Finset.sum_nonneg fun y _ => hK0 h (y, o)
      have hq1 : ∑ o, q o ≤ 1 := vis_sum_le K h (hK1 h)
      rw [sum_aout] at hq1
      have h1 := hq0 (true, true, true); have h2 := hq0 (true, false, true)
      have h3 := hq0 (false, true, true); have h4 := hq0 (false, false, true)
      refine pre_step k Bf ρ hρ0 hρ1 _ q
        (q (true, true, true) + q (true, true, false) + q (true, false, true) + q (true, false, false))
        hq0 (by linarith) ?_ (by linarith)
      intro hb
      have := hrec h hb
      simp only [Fintype.sum_bool, Finset.sum_add_distrib] at this
      simp only [hq]
      linarith) N []
  simpa [W1, preAtt, preAttAux, liveInd] using h

/-- **Flag-triggered auditing, exhaustion.** Premise `hfp`: at every full history with fewer than Bf flags, the
probability that this round is flagged and the attacker is not caught is ≤ α (for the concrete policy: the monitor's
false-positive rate on non-attack rounds, since a flagged attack round is audited). Then
P(budget exhausted and never caught) ≤ binTail α Bf N 0 = P(Binomial(N, α) ≥ Bf). -/
theorem flag_exhaust_bound (Bf : ℕ) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (K : List (Y × AOut Bool) → Y × AOut Bool → ℝ)
    (hK0 : ∀ h z, 0 ≤ K h z) (hK1 : ∀ h, ∑ z, K h z ≤ 1)
    (hfp : ∀ h, flagCount (h.map Prod.snd) < Bf → ∑ y, ∑ a, K h (y, (a, true, false)) ≤ α) :
    val K (exhLive Bf) N [] ≤ binTail α Bf N 0 := by
  have h := val_le_potential K (exhLive Bf) (W2 α Bf) hK0 (by
      intro g
      unfold exhLive W2
      simp only [binTail]
      exact le_of_eq (mul_comm _ _)) (by
      intro n h
      set q : AOut Bool → ℝ := fun o => ∑ y, K h (y, o) with hq
      have hq0 : ∀ o, 0 ≤ q o := fun o => Finset.sum_nonneg fun y _ => hK0 h (y, o)
      have hq1 : ∑ o, q o ≤ 1 := vis_sum_le K h (hK1 h)
      rw [sum_aout] at hq1
      have h1 := hq0 (true, true, true); have h2 := hq0 (true, false, true)
      have h3 := hq0 (false, true, true); have h4 := hq0 (false, false, true)
      refine tail_step α Bf hα0 hα1 n _ q hq0 (by linarith) ?_
      intro hb
      have := hfp h hb
      simp only [Fintype.sum_bool, Finset.sum_add_distrib] at this
      simp only [hq]
      linarith) N []
  simpa [W2, flagCount, liveInd] using h

/-- **Flag-triggered auditing, all attacks.** Under both premises,
P(≥ k attacks, never caught) ≤ (1 − ρ)^k + P(Binomial(N, α) ≥ Bf), for every attacker (ADAPTIVE_FEEDBACK, whole history observable). -/
theorem flag_total_bound (k Bf : ℕ) (ρ α : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (K : List (Y × AOut Bool) → Y × AOut Bool → ℝ)
    (hK0 : ∀ h z, 0 ≤ K h z) (hK1 : ∀ h, ∑ z, K h z ≤ 1)
    (hrec : ∀ h, flagCount (h.map Prod.snd) < Bf →
      ∑ y, ∑ f, K h (y, (true, f, false)) ≤ (1 - ρ) * ∑ y, ∑ f, ∑ c, K h (y, (true, f, c)))
    (hfp : ∀ h, flagCount (h.map Prod.snd) < Bf → ∑ y, ∑ a, K h (y, (a, true, false)) ≤ α) :
    val K (totSucc (N := N) k) N [] ≤ (1 - ρ) ^ k + binTail α Bf N 0 := by
  calc val K (totSucc (N := N) k) N []
      ≤ val K (fun g => preSucc (N := N) k Bf g + exhLive Bf g) N [] :=
        val_mono K _ _ hK0 (totSucc_le k Bf) N []
    _ = val K (preSucc (N := N) k Bf) N [] + val K (exhLive Bf) N [] := val_add K _ _ N []
    _ ≤ _ := add_le_add (flag_pre_bound k Bf ρ hρ0 hρ1 K hK0 hK1 hrec)
        (flag_exhaust_bound Bf α hα0 hα1 K hK0 hK1 hfp)

end Kernel

end ControlStack.FlagBudget

#print axioms ControlStack.FlagBudget.val_le_potential
#print axioms ControlStack.FlagBudget.cval_le_potential
#print axioms ControlStack.FlagBudget.totSucc_le
#print axioms ControlStack.FlagBudget.pre_step
#print axioms ControlStack.FlagBudget.tail_step
#print axioms ControlStack.FlagBudget.flag_pre_bound
#print axioms ControlStack.FlagBudget.flag_exhaust_bound
#print axioms ControlStack.FlagBudget.flag_total_bound
