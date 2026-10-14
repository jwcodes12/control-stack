/-
F6: flag-triggered auditing against an attacker who chooses WHICH KIND of attack to make. This is the statement an
experiment with labelled attack types tests (preregistration `prereg/E1-FLAG-BUDGET-REPLAY-DRAFT.md`).

Model (the `val` kernel semantics; visible output `AOut Bool` = (attack, flag, caught)). In each round the attacker
either does not attack or attacks with a class c from a finite type C, with any law that is a function of the
visible history. The monitor flags an attack of class c with probability `r g c` and a non-attack with probability
`fp g`. A flagged attack is audited and caught while fewer than Bf earlier rounds were flagged. The class is the
kernel's hidden per-round state; the attacker knows it, the payoff does not need it.

Results.
1. `class_flag_bound`: if while budget remains every class has recall ≥ ρ (ρ ≤ r g c) and the false-positive rate is
   ≤ α, then for every class-choosing attacker
     P(≥ k attacks, never caught) ≤ (1 − ρ)^k + P(Binomial(N, α) ≥ Bf).
   So the ρ to use is the MINIMUM recall over the classes the attacker can choose, at every history.
2. `class_average_witness`: two classes with recall 1 and 0 (average 1/2). The attacker who always uses the second
   class is never caught, against a claimed bound of 1/2 from the average.

Limits. Recall may depend on the visible history and the class, not on hidden attacker state beyond the class.
A flagged attack with budget left is caught with certainty (audit recall is folded into `r`). Statements about the
model only. Classical mathematics; an instance of `FlagBudget.flag_total_bound`.
-/
import ControlStack.Families.F6.FlagBudget

namespace ControlStack.ClassAudit

open Finset ControlStack.Leakage ControlStack.Covert ControlStack.FlagBudget

section Kernel

variable {C : Type} [Fintype C]

/-- the flag law given the round's hidden choice: `some c` = an attack of class c, `none` = no attack -/
noncomputable def flagLaw (r : List (AOut Bool) → C → ℝ) (fp : List (AOut Bool) → ℝ) (g : List (AOut Bool)) :
    Option C → Bool → ℝ
  | some c, f => if f then r g c else 1 - r g c
  | none, f => if f then fp g else 1 - fp g

/-- the class kernel. Hidden y: the attacker's choice (no attack, or an attack class), with law σ(visible history).
Visible output: attack bit = `y.isSome`, flag ~ `flagLaw`, caught = attack ∧ flag ∧ flag budget left. -/
noncomputable def classK (Bf : ℕ) (σ : List (AOut Bool) → Option C → ℝ) (r : List (AOut Bool) → C → ℝ)
    (fp : List (AOut Bool) → ℝ) : List (Option C × AOut Bool) → Option C × AOut Bool → ℝ :=
  fun h yo => σ (h.map Prod.snd) yo.1 * (if yo.2.1 = yo.1.isSome then 1 else 0) *
    flagLaw r fp (h.map Prod.snd) yo.1 yo.2.2.1 *
    (if yo.2.2.2 = (yo.2.1 && (yo.2.2.1 && decide (flagCount (h.map Prod.snd) < Bf))) then 1 else 0)

variable (Bf : ℕ) (σ : List (AOut Bool) → Option C → ℝ) (r : List (AOut Bool) → C → ℝ)
  (fp : List (AOut Bool) → ℝ)

omit [Fintype C] in
theorem flagLaw_nonneg (hr : ∀ g c, 0 ≤ r g c ∧ r g c ≤ 1) (hfp : ∀ g, 0 ≤ fp g ∧ fp g ≤ 1)
    (g : List (AOut Bool)) (y : Option C) (f : Bool) : 0 ≤ flagLaw r fp g y f := by
  cases y with
  | none => cases f <;> simp [flagLaw] <;> linarith [(hfp g).1, (hfp g).2]
  | some c => cases f <;> simp [flagLaw] <;> linarith [(hr g c).1, (hr g c).2]

omit [Fintype C] in
theorem flagLaw_sum (g : List (AOut Bool)) (y : Option C) : ∑ f : Bool, flagLaw r fp g y f = 1 := by
  cases y <;> simp [flagLaw]

theorem classK_nonneg (hσ : ∀ g, IsDist (σ g)) (hr : ∀ g c, 0 ≤ r g c ∧ r g c ≤ 1)
    (hfp : ∀ g, 0 ≤ fp g ∧ fp g ≤ 1) (h : List (Option C × AOut Bool)) (z : Option C × AOut Bool) :
    0 ≤ classK Bf σ r fp h z := by
  unfold classK
  exact mul_nonneg (mul_nonneg (mul_nonneg ((hσ _).1 _) (by split_ifs <;> norm_num))
    (flagLaw_nonneg r fp hr hfp _ _ _)) (by split_ifs <;> norm_num)

omit [Fintype C] in
/-- the kernel at a fixed hidden choice and visible output, with the attack bit forced to match the choice -/
theorem classK_apply (h : List (Option C × AOut Bool)) (y : Option C) (a f c : Bool) :
    classK Bf σ r fp h (y, (a, f, c)) =
      if a = y.isSome ∧ c = (a && (f && decide (flagCount (h.map Prod.snd) < Bf))) then
        σ (h.map Prod.snd) y * flagLaw r fp (h.map Prod.snd) y f else 0 := by
  unfold classK
  by_cases h1 : a = y.isSome <;>
    by_cases h2 : c = (a && (f && decide (flagCount (h.map Prod.snd) < Bf))) <;> simp [h1, h2]

omit [Fintype C] in
/-- summing the visible output at a fixed hidden choice gives the attacker's weight on that choice -/
theorem classK_sum_o (h : List (Option C × AOut Bool)) (y : Option C) :
    ∑ o : AOut Bool, classK Bf σ r fp h (y, o) = σ (h.map Prod.snd) y := by
  rw [sum_aout]
  simp only [classK_apply]
  have hs := flagLaw_sum r fp (h.map Prod.snd) y
  rw [Fintype.sum_bool] at hs
  by_cases hb : flagCount (h.map Prod.snd) < Bf <;> cases hy : y.isSome <;> simp [hb] <;>
    linear_combination (σ (h.map Prod.snd) y) * hs

theorem classK_sum (hσ : ∀ g, IsDist (σ g)) (h : List (Option C × AOut Bool)) :
    ∑ z, classK Bf σ r fp h z ≤ 1 := by
  rw [Fintype.sum_prod_type]
  simp only [classK_sum_o]
  exact le_of_eq (hσ _).2

end Kernel

section Bound

variable {N : ℕ} {C : Type} [Fintype C]

/-- **Flag-triggered auditing against a class-choosing attacker.** Adversary class: ADAPTIVE_FEEDBACK (attack or
not, and which class, with any law that is a function of the visible history: own attack bits, every flag, every
catch). Premises, at every visible history with fewer than Bf flags: every class is flagged with probability ≥ ρ,
and a non-attack with probability ≤ α. Then
P(≥ k attacks, never caught) ≤ (1 − ρ)^k + P(Binomial(N, α) ≥ Bf). -/
theorem class_flag_bound (k Bf : ℕ) (ρ α : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (σ : List (AOut Bool) → Option C → ℝ) (hσ : ∀ g, IsDist (σ g))
    (r : List (AOut Bool) → C → ℝ) (hr : ∀ g c, 0 ≤ r g c ∧ r g c ≤ 1)
    (fp : List (AOut Bool) → ℝ) (hfp : ∀ g, 0 ≤ fp g ∧ fp g ≤ 1)
    (hrec : ∀ g c, flagCount g < Bf → ρ ≤ r g c)
    (hfalse : ∀ g, flagCount g < Bf → fp g ≤ α) :
    val (classK Bf σ r fp) (totSucc (N := N) k) N [] ≤ (1 - ρ) ^ k + binTail α Bf N 0 := by
  refine flag_total_bound k Bf ρ α hρ0 hρ1 hα0 hα1 (classK Bf σ r fp)
    (classK_nonneg Bf σ r fp hσ hr hfp) (classK_sum Bf σ r fp hσ) ?_ ?_
  · -- conditional recall: an uncaught attack is an unflagged one while budget remains
    intro h hb
    simp only [Fintype.sum_bool, Fintype.sum_option, classK_apply]
    simp only [hb, decide_true, Bool.and_true, Bool.and_false, Option.isSome_none, Option.isSome_some,
      Bool.true_eq_false, Bool.false_eq_true, and_false, and_true, ite_false, ite_true,
      add_zero, zero_add, flagLaw, Bool.and_self]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    have h0 := (hσ (h.map Prod.snd)).1 (some c)
    have hrc := hrec (h.map Prod.snd) c hb
    have := hr (h.map Prod.snd) c
    simp
    nlinarith
  · -- false positives: a flagged round that is not caught is a flagged non-attack while budget remains
    intro h hb
    simp only [Fintype.sum_bool, Fintype.sum_option, classK_apply]
    simp only [hb, decide_true, Bool.and_true, Option.isSome_none, Option.isSome_some,
      Bool.true_eq_false, Bool.false_eq_true, and_false, and_true, ite_false, ite_true,
      add_zero, zero_add, Finset.sum_const_zero, flagLaw, Bool.and_self]
    have h0 := (hσ (h.map Prod.snd)).1 none
    have h1 : σ (h.map Prod.snd) none ≤ 1 := by
      have hs := (hσ (h.map Prod.snd)).2
      rw [Fintype.sum_option] at hs
      have : 0 ≤ ∑ c, σ (h.map Prod.snd) (some c) := Finset.sum_nonneg fun c _ => (hσ _).1 _
      linarith
    have hf := hfalse (h.map Prod.snd) hb
    have := hfp (h.map Prod.snd)
    simp
    nlinarith

end Bound

section Witness

theorem card_attackSet_one (o : AOut Bool) :
    (attackSet (N := 1) [o]).card = if o.1 = true then 1 else 0 := by
  unfold attackSet
  rw [Finset.card_filter, Fin.sum_univ_one]
  simp [attacked]

/-- **The average over attack classes is not the premise** (one round, Bf = 1, k = 1, two classes, no false
positives). Class `true` is always flagged, class `false` never: recall averaged over the two classes is 1/2. The
attacker who always uses class `false` is never caught, against (1 − 1/2)^1 + 0 = 1/2 from the average.
`class_flag_bound` needs ρ below the recall of EVERY class, here 0. -/
theorem class_average_witness :
    val (classK (C := Bool) 1 (fun _ y => if y = some false then 1 else 0) (fun _ c => if c then 1 else 0)
      (fun _ => 0)) (totSucc (N := 1) 1) 1 [] = 1 ∧
    ((1 : ℝ) + 0) / 2 = 1 / 2 ∧ (1 - (1 / 2 : ℝ)) ^ 1 + binTail 0 1 1 0 = 1 / 2 := by
  refine ⟨?_, by norm_num, ?_⟩
  · show val _ _ (0 + 1) [] = _
    simp [Leakage.val, Fintype.sum_prod_type, Fintype.sum_option, classK_apply, flagLaw, flagCount, totSucc,
      card_attackSet_one, liveInd, caughtFlag]
  · simp [binTail]; norm_num

end Witness

end ControlStack.ClassAudit

#print axioms ControlStack.ClassAudit.classK_sum
#print axioms ControlStack.ClassAudit.class_flag_bound
#print axioms ControlStack.ClassAudit.class_average_witness
