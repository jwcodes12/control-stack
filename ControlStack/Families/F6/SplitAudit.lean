/-
F6 flagship: hidden random auditing (P1), monitor-flag-triggered auditing with a hard first-come budget (P2), and
their split, as ONE round kernel `splitK`, with one failure event `FlagBudget.totSucc` (≥ k attack rounds and never
caught). Research record: `docs/records/budgeted-audit-vs-adaptive-attacker.md`.

Model. N rounds. In round i the attacker picks the attack bit a ~ σ(visible history); the monitor emits a flag
f ~ τ(S, visible history, a); the round is caught iff a ∧ (i ∈ S ∨ (f ∧ fewer than Bf earlier flags)). The visible
history is every earlier (attack bit, flag, caught), so the attacker sees all earlier flags and hence the flag-budget
state. S is a uniformly random set of Bh rounds, drawn before play. P1 is Bf = 0, P2 is Bh = 0.

Results.
1. `split_hidden_bound` (P1's mechanism). If the flag law does not depend on S (it is a function of the visible
   history and the attack bit), then for every attacker P(≥ k attacks, never caught) ≤ C(N−k,Bh)/C(N,Bh).
   The monitor may be arbitrarily bad. Reuses `ReservedAudit.reserved_leak_bound`.
2. `split_flag_bound` (P2's mechanism). If, while budget remains, an attack is flagged with probability ≥ ρ and a
   non-attack with probability ≤ α, then FOR EVERY FIXED SCHEDULE S (so also for a schedule the attacker knows)
   P(≥ k attacks, never caught) ≤ (1−ρ)^k + P(Binomial(N, α) ≥ Bf). Reuses `FlagBudget.flag_total_bound`.
3. `split_min_bound`: both premises give the minimum of the two bounds.
4. `split_product_pre` / `split_product_bound` (composition). With an S-independent flag law and conditional
   recall ρ, the two mechanisms MULTIPLY:
   P(≥ k attacks, never caught) ≤ C(N−k,Bh)/C(N,Bh) · (1−ρ)^k + P(Binomial(N, α) ≥ Bf).
   Proof: `Leakage.seq_transfer` reduces the hidden-schedule game to a blind game against an S-independent
   certificate; the pre-exhaustion potential of `FlagBudget.pre_step` then bounds the certificate game.
5. Negative controls (Lean-checked values of concrete kernels in the same semantics):
   - `exhaustion_witness`: monitor recall 1, false-positive rate α ∈ [0,1], Bf = 1, N = 2. An attacker who simply
     attacks in the last round (it need not see any flag) succeeds with probability exactly α. So monitor recall does
     not compound unless exhaustion is accounted for; for α > 0 the bound without the exhaustion term is false.
   - `average_recall_witness`: the monitor flags attacks in round 0 and misses them in round 1. An attacker spread
     evenly over the two rounds is missed with probability 1/2 (measured recall 1/2); the attacker who picks round 1
     is never caught. Recall averaged over an attack distribution is not the per-history premise.
   - `dependence_witness`: the monitor has recall exactly 1/2 for every schedule, but its false positive in round 0
     reveals whether round 1 is reserved. The attacker avoids the reserved round and succeeds with probability
     1/2 = (1−ρ), not the product 1/3: the product needs the flag law to be S-independent.
6. Numbers: `hidden_one_step` (k = 1: the hidden-schedule bound is exactly 1 − Bh/N), `split_example`
   (N = 100, Bh = 10, k = 5, ρ = 1/2: ≈ 0.584 hidden alone, 0.03125 flags alone, ≈ 0.0182 for the product).

Limits (what is NOT claimed).
- Reserved audits catch an attacked round with certainty here. Imperfect reserved recall is proved only for the
  hidden-flag model (`ReservedRecall.adaptive_recall_bound`, `AOut Unit`); combining it with visible flags is open.
- The failure event here is "≥ k attacks and never caught by round N". "k attacks released before the first catch" is
  a larger event; `Truncation.prefix_eq_truncated` shows it has the same value against the attacker stopped after k
  attacks, so every bound in this file also holds for it (`Truncation.split_*_bound_prefix`).
- `split_hidden_bound` needs the flag law to be a function of the visible history. A flag process with hidden
  state that depends on S can leak the schedule; the hidden-flag theorem `ReservedAudit.reserved_policy_bound`
  allows any flag law only because there the attacker never sees a flag.
- Statements about the model only. That a deployment draws S uniformly and keeps it hidden, that a monitor has
  conditional recall ρ at every history, and that its false-positive rate is ≤ α are correspondence obligations.
- Classical mathematics (hypergeometric counting, leakage transfer, optional stopping). No novelty is claimed.
-/
import ControlStack.Families.F6.FlagBudget

namespace ControlStack.SplitAudit

open Finset ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.FlagBudget

/-! ## 1. The split kernel -/

section Kernel

variable {N : ℕ}

/-- the split policy's catch rule: an attack is caught iff the round is reserved, or it is flagged while fewer than
Bf earlier rounds were flagged -/
def catchRule (Bf : ℕ) (S : Finset (Fin N)) (g : List (AOut Bool)) (a f : Bool) : Bool :=
  a && (decide (memN S g.length) || (f && decide (flagCount g < Bf)))

/-- the split-policy round kernel. No hidden per-round state (Y = Unit): attack a ~ σ(visible history), flag
f ~ τ(S, visible history, a), catch by `catchRule`. -/
noncomputable def splitK (Bf : ℕ) (σ : List (AOut Bool) → Bool → ℝ)
    (τ : Finset (Fin N) → List (AOut Bool) → Bool → Bool → ℝ) :
    Finset (Fin N) → List (Unit × AOut Bool) → Unit × AOut Bool → ℝ :=
  fun S h yo => σ (h.map Prod.snd) yo.2.1 * τ S (h.map Prod.snd) yo.2.1 yo.2.2.1 *
    (if yo.2.2.2 = catchRule Bf S (h.map Prod.snd) yo.2.1 yo.2.2.1 then 1 else 0)

variable (Bf : ℕ) (σ : List (AOut Bool) → Bool → ℝ) (τ : Finset (Fin N) → List (AOut Bool) → Bool → Bool → ℝ)

theorem splitK_nonneg (hσ : ∀ g, IsDist (σ g)) (hτ : ∀ S g a, IsDist (τ S g a))
    (S : Finset (Fin N)) (h : List (Unit × AOut Bool)) (z : Unit × AOut Bool) : 0 ≤ splitK Bf σ τ S h z := by
  unfold splitK
  exact mul_nonneg (mul_nonneg ((hσ _).1 _) ((hτ _ _ _).1 _)) (by split_ifs <;> norm_num)

/-- summing out the catch flag -/
theorem splitK_sum_c (S : Finset (Fin N)) (h : List (Unit × AOut Bool)) (a f : Bool) :
    ∑ c : Bool, splitK Bf σ τ S h ((), (a, f, c)) = σ (h.map Prod.snd) a * τ S (h.map Prod.snd) a f := by
  unfold splitK
  simp only
  rw [← Finset.mul_sum, sum_ite_bool, mul_one]

theorem splitK_sum (hσ : ∀ g, IsDist (σ g)) (hτ : ∀ S g a, IsDist (τ S g a))
    (S : Finset (Fin N)) (h : List (Unit × AOut Bool)) : ∑ z, splitK Bf σ τ S h z ≤ 1 := by
  have e : ∑ z, splitK Bf σ τ S h z = ∑ a : Bool, ∑ f : Bool, ∑ c : Bool, splitK Bf σ τ S h ((), (a, f, c)) := by
    simp only [Fintype.sum_prod_type, Fintype.univ_unit, Finset.sum_singleton]
  rw [e]
  simp only [splitK_sum_c, ← Finset.mul_sum, (hτ _ _ _).2, mul_one]
  rw [(hσ _).2]

/-- one round of the split game: the catch flag is determined by the rule -/
theorem splitK_val_succ (S : Finset (Fin N)) (pay : List (AOut Bool) → ℝ) (n : ℕ) (h : List (Unit × AOut Bool)) :
    val (splitK Bf σ τ S) pay (n + 1) h = ∑ a : Bool, ∑ f : Bool,
      σ (h.map Prod.snd) a * τ S (h.map Prod.snd) a f *
        val (splitK Bf σ τ S) pay n (h ++ [((), (a, f, catchRule Bf S (h.map Prod.snd) a f))]) := by
  simp only [Leakage.val, Fintype.univ_unit, Finset.sum_singleton, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro f _
  rw [Fintype.sum_bool]
  unfold splitK
  cases catchRule Bf S (h.map Prod.snd) a f <;> simp

/-- the conditional-recall premise of `FlagBudget.flag_pre_bound` holds for the split kernel, for every schedule -/
theorem splitK_hrec (hσ : ∀ g, IsDist (σ g)) (hτ : ∀ S g a, IsDist (τ S g a)) (ρ : ℝ)
    (hrec : ∀ S g, flagCount g < Bf → ρ ≤ τ S g true true)
    (S : Finset (Fin N)) (h : List (Unit × AOut Bool)) (hb : flagCount (h.map Prod.snd) < Bf) :
    ∑ y, ∑ f, splitK Bf σ τ S h (y, (true, f, false)) ≤
      (1 - ρ) * ∑ y, ∑ f, ∑ c, splitK Bf σ τ S h (y, (true, f, c)) := by
  have hs := (hτ S (h.map Prod.snd) true).2
  rw [Fintype.sum_bool] at hs
  have h0 := (hσ (h.map Prod.snd)).1 true
  have h1 := (hτ S (h.map Prod.snd) true).1 false
  have hr := hrec S (h.map Prod.snd) hb
  simp only [Fintype.univ_unit, Finset.sum_singleton, splitK_sum_c]
  rw [← Finset.mul_sum, (hτ S (h.map Prod.snd) true).2, mul_one, Fintype.sum_bool]
  unfold splitK catchRule
  by_cases hm : memN S h.length <;> simp [hb, hm] <;> nlinarith

/-- the false-positive premise of `FlagBudget.flag_exhaust_bound` holds for the split kernel, for every schedule -/
theorem splitK_hfp (hσ : ∀ g, IsDist (σ g)) (hτ : ∀ S g a, IsDist (τ S g a)) (α : ℝ)
    (hfp : ∀ S g, flagCount g < Bf → τ S g false true ≤ α)
    (S : Finset (Fin N)) (h : List (Unit × AOut Bool)) (hb : flagCount (h.map Prod.snd) < Bf) :
    ∑ y, ∑ a, splitK Bf σ τ S h (y, (a, true, false)) ≤ α := by
  have hs := (hσ (h.map Prod.snd)).2
  rw [Fintype.sum_bool] at hs
  have h0 := (hσ (h.map Prod.snd)).1 true
  have h0' := (hσ (h.map Prod.snd)).1 false
  have h1 := (hτ S (h.map Prod.snd) false).1 true
  have hr := hfp S (h.map Prod.snd) hb
  simp only [Fintype.univ_unit, Finset.sum_singleton, Fintype.sum_bool]
  unfold splitK catchRule
  simp [hb]
  nlinarith

end Kernel

/-! ## 2. P2's mechanism: conditional recall, any schedule -/

section Flag

variable {N : ℕ}

/-- **Flag-triggered audits in the split policy, for every fixed schedule.** Adversary class: ADAPTIVE_FEEDBACK with the whole history observable, and the
schedule S may be known to the attacker (the bound holds for each S separately; the flag law may depend on S).
Premises, at every visible history with fewer than Bf flags: an attack is flagged with probability ≥ ρ, a
non-attack with probability ≤ α. Then P(≥ k attacks, never caught) ≤ (1−ρ)^k + P(Binomial(N, α) ≥ Bf). -/
theorem split_flag_bound (k Bf : ℕ) (ρ α : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ : Finset (Fin N) → List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ S g a, IsDist (τ S g a))
    (hrec : ∀ S g, flagCount g < Bf → ρ ≤ τ S g true true)
    (hfp : ∀ S g, flagCount g < Bf → τ S g false true ≤ α) (S : Finset (Fin N)) :
    val (splitK Bf σ τ S) (totSucc (N := N) k) N [] ≤ (1 - ρ) ^ k + binTail α Bf N 0 :=
  flag_total_bound k Bf ρ α hρ0 hρ1 hα0 hα1 (splitK Bf σ τ S)
    (splitK_nonneg Bf σ τ hσ hτ S) (splitK_sum Bf σ τ hσ hτ S)
    (splitK_hrec Bf σ τ hσ hτ ρ hrec S) (splitK_hfp Bf σ τ hσ hτ α hfp S)

/-- the same bound averaged over the reserved schedule -/
theorem split_flag_bound_avg (k Bh Bf : ℕ) (hB : Bh ≤ N) (ρ α : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ : Finset (Fin N) → List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ S g a, IsDist (τ S g a))
    (hrec : ∀ S g, flagCount g < Bf → ρ ≤ τ S g true true)
    (hfp : ∀ S g, flagCount g < Bf → τ S g false true ≤ α) :
    ∑ S : Finset (Fin N), pU N Bh S * val (splitK Bf σ τ S) (totSucc (N := N) k) N []
      ≤ (1 - ρ) ^ k + binTail α Bf N 0 := by
  calc ∑ S : Finset (Fin N), pU N Bh S * val (splitK Bf σ τ S) (totSucc (N := N) k) N []
      ≤ ∑ S : Finset (Fin N), pU N Bh S * ((1 - ρ) ^ k + binTail α Bf N 0) :=
        Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left
          (split_flag_bound k Bf ρ α hρ0 hρ1 hα0 hα1 σ hσ τ hτ hrec hfp S) (pU_nonneg N Bh S)
    _ = _ := by rw [← Finset.sum_mul, sum_pU Bh hB, one_mul]

end Flag

/-! ## 3. P1's mechanism: a hidden schedule, any S-independent flag law -/

section Hidden

variable {N : ℕ}

/-- every attack in a reserved round was caught -/
def SCons (S : Finset (Fin N)) (t : List (AOut Bool)) : Prop :=
  ∀ i (o : AOut Bool), t[i]? = some o → o.1 = true → memN S i → o.2.2 = true

theorem scons_nil (S : Finset (Fin N)) : SCons S [] := by
  intro i o hi; simp at hi

theorem scons_append (S : Finset (Fin N)) (g : List (AOut Bool)) (o : AOut Bool) (hg : SCons S g)
    (ho : o.1 = true → memN S g.length → o.2.2 = true) : SCons S (g ++ [o]) := by
  intro i o' hi
  rcases lt_or_ge i g.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hi; exact hg i o' hi
  · rw [List.getElem?_append_right hge] at hi
    rcases Nat.eq_or_lt_of_le hge with heq | hlt
    · subst heq; simp at hi; subst hi; exact ho
    · have : i - g.length ≠ 0 := by omega
      simp [this] at hi

/-- the split kernel only produces transcripts in which reserved-round attacks are caught -/
theorem splitK_scons (Bf : ℕ) (σ : List (AOut Bool) → Bool → ℝ)
    (τ : Finset (Fin N) → List (AOut Bool) → Bool → Bool → ℝ) (S : Finset (Fin N))
    (h : List (Unit × AOut Bool)) (y : Unit) (o : AOut Bool) (hK : splitK Bf σ τ S h (y, o) ≠ 0)
    (hg : SCons S (h.map Prod.snd)) : SCons S (h.map Prod.snd ++ [o]) := by
  apply scons_append S _ o hg
  intro ha hm
  by_contra hne
  apply hK
  obtain ⟨a, f, c⟩ := o
  simp only at ha hm hne
  subst ha
  have hc : c = false := by simpa using hne
  subst hc
  have hm' : memN S h.length := by simpa using hm
  simp [splitK, catchRule, hm']

/-- on such transcripts, "never caught" already implies "no attack in a reserved round" -/
theorem totSucc_eq_successInd (k : ℕ) (S : Finset (Fin N)) (t : List (AOut Bool)) (ht : SCons S t) :
    totSucc (N := N) k t = successInd k S t := by
  unfold totSucc successInd survInd liveInd
  by_cases hl : (t.all fun o => !caughtFlag o) = true
  · have hd : Disjoint S (attackSet (N := N) t) := by
      rw [Finset.disjoint_left]
      intro j hjS hjA
      have hatt : attacked t (j : ℕ) = true := (Finset.mem_filter.1 hjA).2
      unfold attacked at hatt
      cases hget : t[(j : ℕ)]? with
      | none => rw [hget] at hatt; simp at hatt
      | some o =>
        rw [hget] at hatt
        have hc := ht j o hget hatt ⟨j, hjS, rfl⟩
        rw [List.all_eq_true] at hl
        have := hl o (List.mem_of_getElem? hget)
        simp [caughtFlag, hc] at this
    simp [hl, hd]
  · simp [hl]

theorem preSucc_eq (k Bf : ℕ) (t : List (AOut Bool)) :
    preSucc (N := N) k Bf t = totSucc (N := N) k t * (if k ≤ preAtt Bf t then 1 else 0) := by
  unfold preSucc totSucc
  by_cases h1 : k ≤ (attackSet (N := N) t).card <;> by_cases h2 : k ≤ preAtt Bf t <;> simp [h1, h2]

/-- **Hidden reserved audits in the split policy.** Adversary class: ADAPTIVE_FEEDBACK plus all earlier flags (the
attacker's attack law is any function σ of the visible history: its own bits, every flag, every catch). The flag
law τ₀ is any function of the visible history and the current attack bit; it must not depend on S. Nothing is
assumed about the monitor's quality. Then P(≥ k attacks, never caught) ≤ C(N−k,Bh)/C(N,Bh), for every flag budget. -/
theorem split_hidden_bound (k Bh Bf : ℕ) (hB : Bh ≤ N) (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ₀ : List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ g a, IsDist (τ₀ g a)) :
    ∑ S : Finset (Fin N), pU N Bh S * val (splitK Bf σ (fun _ => τ₀) S) (totSucc (N := N) k) N []
      ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ) := by
  have hcongr : ∀ S : Finset (Fin N), val (splitK Bf σ (fun _ => τ₀) S) (totSucc (N := N) k) N []
      = val (splitK Bf σ (fun _ => τ₀) S) (successInd k S) N [] := fun S =>
    val_congr_on _ (SCons S) _ _ (splitK_scons Bf σ _ S) (totSucc_eq_successInd k S) N [] (scons_nil S)
  simp_rw [hcongr]
  have h := reserved_leak_bound k Bh hB (splitK Bf σ (fun _ => τ₀)) (fun g o => σ g o.1 * τ₀ g o.1 o.2.1)
    (fun S _ h z => splitK_nonneg Bf σ _ hσ (fun _ => hτ) S h z)
    (fun S _ h => splitK_sum Bf σ _ hσ (fun _ => hτ) S h)
    (fun S _ h o _ => by
      obtain ⟨a, f, c⟩ := o
      simp only [Fintype.univ_unit, Finset.sum_singleton, splitK]
      have := mul_nonneg ((hσ (h.map Prod.snd)).1 a) ((hτ (h.map Prod.snd) a).1 f)
      split_ifs <;> nlinarith)
    (fun g o => mul_nonneg ((hσ g).1 _) ((hτ g _).1 _))
  have hm : mass (dropStop caughtFlag (fun g (o : AOut Bool) => σ g o.1 * τ₀ g o.1 o.2.1)) N [] ≤ 1 ^ N := by
    apply mass_le_pow _ 1
    · intro g o; unfold dropStop; split_ifs
      · exact le_rfl
      · exact mul_nonneg ((hσ g).1 _) ((hτ g _).1 _)
    · exact zero_le_one
    · intro g
      rw [sum_aout]
      have h1 := (hσ g).2; rw [Fintype.sum_bool] at h1
      have h2 := (hτ g true).2; rw [Fintype.sum_bool] at h2
      have h3 := (hτ g false).2; rw [Fintype.sum_bool] at h3
      simp only [dropStop, caughtFlag, ite_true, Bool.false_eq_true, ite_false]
      have e : σ g true * τ₀ g true true + σ g true * τ₀ g true false + σ g false * τ₀ g false true +
          σ g false * τ₀ g false false = 1 := by
        linear_combination σ g true * h2 + σ g false * h3 + h1
      linarith
  rw [one_pow] at hm
  have hb : (0 : ℝ) ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ) := by positivity
  calc _ ≤ _ := h
    _ ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ) * 1 := mul_le_mul_of_nonneg_left hm hb
    _ = _ := mul_one _

/-- **Both mechanisms at once: the minimum.** -/
theorem split_min_bound (k Bh Bf : ℕ) (hB : Bh ≤ N) (ρ α : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ₀ : List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ g a, IsDist (τ₀ g a))
    (hrec : ∀ g, flagCount g < Bf → ρ ≤ τ₀ g true true)
    (hfp : ∀ g, flagCount g < Bf → τ₀ g false true ≤ α) :
    ∑ S : Finset (Fin N), pU N Bh S * val (splitK Bf σ (fun _ => τ₀) S) (totSucc (N := N) k) N []
      ≤ min ((Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ)) ((1 - ρ) ^ k + binTail α Bf N 0) :=
  le_min (split_hidden_bound k Bh Bf hB σ hσ τ₀ hτ)
    (split_flag_bound_avg k Bh Bf hB ρ α hρ0 hρ1 hα0 hα1 σ hσ (fun _ => τ₀) (fun _ => hτ)
      (fun _ => hrec) (fun _ => hfp))

end Hidden

/-! ## 4. Composition: the two mechanisms multiply when the flag law is S-independent -/

section Product

variable {N : ℕ}

/-- the S-independent certificate of the split kernel: a flagged attack with budget left is always caught, so it
has no non-catch weight -/
noncomputable def splitCert (Bf : ℕ) (σ : List (AOut Bool) → Bool → ℝ) (τ₀ : List (AOut Bool) → Bool → Bool → ℝ) :
    List (AOut Bool) → AOut Bool → ℝ :=
  fun g o => if o.2.2 then 1 else
    σ g o.1 * τ₀ g o.1 o.2.1 * (if o.1 && (o.2.1 && decide (flagCount g < Bf)) then 0 else 1)

theorem splitCert_nonneg (Bf : ℕ) (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ₀ : List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ g a, IsDist (τ₀ g a)) (g : List (AOut Bool))
    (o : AOut Bool) : 0 ≤ splitCert Bf σ τ₀ g o := by
  unfold splitCert
  split_ifs
  · exact zero_le_one
  · simp
  · simpa using mul_nonneg ((hσ g).1 _) ((hτ g _).1 _)

theorem splitK_dominated (Bf : ℕ) (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ₀ : List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ g a, IsDist (τ₀ g a)) (S : Finset (Fin N)) :
    Dominated (splitK Bf σ (fun _ => τ₀) S) (splitCert Bf σ τ₀) := by
  intro h o
  obtain ⟨a, f, c⟩ := o
  have hnn := mul_nonneg ((hσ (h.map Prod.snd)).1 a) ((hτ (h.map Prod.snd) a).1 f)
  cases c
  · simp only [Fintype.univ_unit, Finset.sum_singleton, splitK, splitCert, catchRule]
    by_cases hb : flagCount (h.map Prod.snd) < Bf <;> by_cases hm : memN S h.length <;>
      cases a <;> cases f <;> simp [hb, hm] <;> nlinarith
  · simp only [splitCert, ite_true]
    calc ∑ y, splitK Bf σ (fun _ => τ₀) S h (y, (a, f, true))
        ≤ ∑ z, splitK Bf σ (fun _ => τ₀) S h z := by
          rw [Fintype.sum_prod_type]
          exact Finset.sum_le_sum fun y _ => Finset.single_le_sum
            (f := fun o' => splitK Bf σ (fun _ => τ₀) S h (y, o'))
            (fun o' _ => splitK_nonneg Bf σ _ hσ (fun _ => hτ) S h _) (Finset.mem_univ _)
      _ ≤ 1 := splitK_sum Bf σ _ hσ (fun _ => hτ) S h

/-- **Composition, pre-exhaustion attacks.** Hidden uniform schedule of Bh rounds, S-independent flag law with
conditional recall ρ while budget remains. For every attacker (attack law any function of the visible history,
flags included): P(≥ k attacks, ≥ k of them while budget remained, never caught) ≤ C(N−k,Bh)/C(N,Bh) · (1−ρ)^k. -/
theorem split_product_pre (k Bh Bf : ℕ) (hB : Bh ≤ N) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ₀ : List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ g a, IsDist (τ₀ g a))
    (hrec : ∀ g, flagCount g < Bf → ρ ≤ τ₀ g true true) :
    ∑ S : Finset (Fin N), pU N Bh S * val (splitK Bf σ (fun _ => τ₀) S) (preSucc (N := N) k Bf) N []
      ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ) * (1 - ρ) ^ k := by
  set b := (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ) with hb
  have hb0 : 0 ≤ b := by positivity
  have hx0 : 0 ≤ 1 - ρ := by linarith
  set X : List (AOut Bool) → ℝ := fun t => (if k ≤ preAtt Bf t then 1 else 0) * liveInd caughtFlag t with hX
  have hX0 : ∀ t, 0 ≤ X t := fun t => mul_nonneg (by split_ifs <;> norm_num) (liveInd_nonneg _ _)
  set payS : Finset (Fin N) → List (AOut Bool) → ℝ :=
    fun S t => successInd k S t * (if k ≤ preAtt Bf t then 1 else 0) with hpayS
  -- step 1: on the kernel's transcripts the event is the S-dependent payoff
  have hcongr : ∀ S : Finset (Fin N), val (splitK Bf σ (fun _ => τ₀) S) (preSucc (N := N) k Bf) N []
      = val (splitK Bf σ (fun _ => τ₀) S) (payS S) N [] := fun S =>
    val_congr_on _ (SCons S) _ _ (splitK_scons Bf σ _ S)
      (fun t ht => by rw [preSucc_eq, totSucc_eq_successInd k S t ht]) N [] (scons_nil S)
  simp_rw [hcongr]
  -- step 2: leakage transfer to the S-independent certificate
  have h2 := seq_transfer (pU N Bh) (splitK Bf σ (fun _ => τ₀)) (splitCert Bf σ τ₀) payS (fun t => b * X t) N
    (pU_nonneg N Bh) (fun S h z => splitK_nonneg Bf σ _ hσ (fun _ => hτ) S h z)
    (fun S => splitK_dominated Bf σ hσ τ₀ hτ S) (splitCert_nonneg Bf σ hσ τ₀ hτ)
    (fun S t => mul_nonneg (mul_nonneg (survInd_nonneg k S t) (liveInd_nonneg _ _)) (by split_ifs <;> norm_num))
    (by
      intro t
      have hba := blind_audit (Z := Bool) k Bh hB t
      have hfac : ∀ S : Finset (Fin N), pU N Bh S * payS S t =
          ((if S ∈ AuditBudget.randomSchedules N Bh then (Nat.choose N Bh : ℝ)⁻¹ else 0) * survInd k S t) *
            X t := by
        intro S; simp only [hpayS, hX, successInd, pU]; ring
      simp_rw [hfac]
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hba (hX0 t))
  rw [cval_smul] at h2
  -- step 3: the certificate game is a flag-budget game; the pre-exhaustion potential bounds it
  have h3 : cval (splitCert Bf σ τ₀) X N [] ≤ (1 - ρ) ^ k := by
    have h := cval_le_potential (splitCert Bf σ τ₀) X (fun _ => W1 k Bf ρ) (splitCert_nonneg Bf σ hσ τ₀ hτ)
      (by
        intro g
        simp only [hX, W1]
        have hl := liveInd_nonneg caughtFlag g
        by_cases hk : k ≤ preAtt Bf g
        · have e : k - preAtt Bf g = 0 := by omega
          simp [hk, e]
        · simp only [hk, ite_false, zero_mul]
          exact mul_nonneg hl (pow_nonneg hx0 _))
      (by
        intro n g
        have hs := (hσ g).2; rw [Fintype.sum_bool] at hs
        have ht := (hτ g true).2; rw [Fintype.sum_bool] at ht
        have hf := (hτ g false).2; rw [Fintype.sum_bool] at hf
        have s1 := (hσ g).1 true; have s2 := (hσ g).1 false
        have t1 := (hτ g true).1 true; have t2 := (hτ g true).1 false
        refine pre_step k Bf ρ hρ0 hρ1 g (splitCert Bf σ τ₀ g) (σ g true)
          (splitCert_nonneg Bf σ hσ τ₀ hτ g) ?_ ?_ ?_
        · simp only [splitCert, Bool.false_eq_true, ite_false, Bool.true_and, Bool.false_and]
          split_ifs <;> nlinarith
        · intro hbf
          have hr := hrec g hbf
          simp only [splitCert, Bool.false_eq_true, ite_false, Bool.true_and, Bool.false_and, hbf, decide_true,
            ite_true]
          nlinarith
        · simp only [splitCert, Bool.false_eq_true, ite_false, Bool.false_and]
          nlinarith) N []
    simpa [W1, preAtt, preAttAux, liveInd] using h
  calc _ ≤ b * cval (splitCert Bf σ τ₀) X N [] := h2
    _ ≤ b * (1 - ρ) ^ k := mul_le_mul_of_nonneg_left h3 hb0

/-- **Composition, all attacks.** Under an S-independent flag law with conditional recall ρ and false-positive rate
≤ α while budget remains, for every attacker:
P(≥ k attacks, never caught) ≤ C(N−k,Bh)/C(N,Bh) · (1−ρ)^k + P(Binomial(N, α) ≥ Bf). -/
theorem split_product_bound (k Bh Bf : ℕ) (hB : Bh ≤ N) (ρ α : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ₀ : List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ g a, IsDist (τ₀ g a))
    (hrec : ∀ g, flagCount g < Bf → ρ ≤ τ₀ g true true)
    (hfp : ∀ g, flagCount g < Bf → τ₀ g false true ≤ α) :
    ∑ S : Finset (Fin N), pU N Bh S * val (splitK Bf σ (fun _ => τ₀) S) (totSucc (N := N) k) N []
      ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ) * (1 - ρ) ^ k + binTail α Bf N 0 := by
  have hK0 : ∀ S : Finset (Fin N), ∀ h z, 0 ≤ splitK Bf σ (fun _ => τ₀) S h z :=
    fun S h z => splitK_nonneg Bf σ _ hσ (fun _ => hτ) S h z
  have hper : ∀ S : Finset (Fin N), val (splitK Bf σ (fun _ => τ₀) S) (totSucc (N := N) k) N []
      ≤ val (splitK Bf σ (fun _ => τ₀) S) (preSucc (N := N) k Bf) N [] + binTail α Bf N 0 := by
    intro S
    calc val (splitK Bf σ (fun _ => τ₀) S) (totSucc (N := N) k) N []
        ≤ val (splitK Bf σ (fun _ => τ₀) S) (fun g => preSucc (N := N) k Bf g + exhLive Bf g) N [] :=
          val_mono _ _ _ (hK0 S) (totSucc_le k Bf) N []
      _ = val (splitK Bf σ (fun _ => τ₀) S) (preSucc (N := N) k Bf) N [] +
            val (splitK Bf σ (fun _ => τ₀) S) (exhLive Bf) N [] := val_add _ _ _ N []
      _ ≤ _ := add_le_add le_rfl (flag_exhaust_bound Bf α hα0 hα1 _ (hK0 S)
          (splitK_sum Bf σ _ hσ (fun _ => hτ) S) (splitK_hfp Bf σ _ hσ (fun _ => hτ) α (fun _ => hfp) S))
  calc ∑ S : Finset (Fin N), pU N Bh S * val (splitK Bf σ (fun _ => τ₀) S) (totSucc (N := N) k) N []
      ≤ ∑ S : Finset (Fin N), pU N Bh S *
          (val (splitK Bf σ (fun _ => τ₀) S) (preSucc (N := N) k Bf) N [] + binTail α Bf N 0) :=
        Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hper S) (pU_nonneg N Bh S)
    _ = ∑ S : Finset (Fin N), pU N Bh S * val (splitK Bf σ (fun _ => τ₀) S) (preSucc (N := N) k Bf) N [] +
          binTail α Bf N 0 := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_pU Bh hB, one_mul]
    _ ≤ _ := add_le_add (split_product_pre k Bh Bf hB ρ hρ0 hρ1 σ hσ τ₀ hτ hrec) le_rfl

end Product

/-! ## 5. Negative controls: values of concrete kernels -/

section Witnesses

theorem card_attackSet_two (o₀ o₁ : AOut Bool) :
    (attackSet (N := 2) [o₀, o₁]).card = (if o₀.1 = true then 1 else 0) + (if o₁.1 = true then 1 else 0) := by
  unfold attackSet
  rw [Finset.card_filter, Fin.sum_univ_two]
  simp [attacked]

/-- a two-round split game, written out -/
theorem splitK_val_two {N : ℕ} (Bf : ℕ) (σ : List (AOut Bool) → Bool → ℝ)
    (τ : Finset (Fin N) → List (AOut Bool) → Bool → Bool → ℝ) (S : Finset (Fin N))
    (pay : List (AOut Bool) → ℝ) :
    val (splitK Bf σ τ S) pay 2 [] = ∑ a : Bool, ∑ f : Bool, σ [] a * τ S [] a f *
      ∑ a' : Bool, ∑ f' : Bool, σ [(a, f, catchRule Bf S [] a f)] a' * τ S [(a, f, catchRule Bf S [] a f)] a' f' *
        pay [(a, f, catchRule Bf S [] a f), (a', f', catchRule Bf S [(a, f, catchRule Bf S [] a f)] a' f')] := by
  show val (splitK Bf σ τ S) pay (0 + 1 + 1) [] = _
  simp only [splitK_val_succ]
  simp [Leakage.val]

/-- the attacker that attacks exactly in round r and ignores everything it sees -/
noncomputable def attackAt (r : ℕ) : List (AOut Bool) → Bool → ℝ :=
  fun g a => if a = decide (g.length = r) then 1 else 0

/-- a monitor with recall 1 and false-positive rate α (a probability law only for 0 ≤ α ≤ 1) -/
noncomputable def fpMonitor (α : ℝ) : Finset (Fin 2) → List (AOut Bool) → Bool → Bool → ℝ :=
  fun _ _ a f => if a then (if f then 1 else 0) else (if f then α else 1 - α)

/-- **Exhaustion** (N = 2, no reserved audits, Bf = 1, k = 1). The monitor flags every attack (monitor recall 1,
so the pre-exhaustion bound is (1−1)^1 = 0) and flags a non-attack with probability α. The attacker attacks in the
last round whatever it has seen. It succeeds exactly when round 0 raised a false positive: probability α. The
identity holds for every real α; it is a statement about probabilities for 0 ≤ α ≤ 1 and a strict counterexample to
"success ≤ (1 − monitor recall)^k" for α > 0. The exhaustion term of `split_flag_bound` here is α + (1−α)·α. -/
theorem exhaustion_witness (α : ℝ) :
    val (splitK 1 (attackAt 1) (fpMonitor α) (∅ : Finset (Fin 2))) (totSucc (N := 2) 1) 2 [] = α ∧
      binTail α 1 2 0 = α + (1 - α) * α := by
  constructor
  · rw [splitK_val_two]
    simp [attackAt, fpMonitor, catchRule, memN, flagCount, totSucc,
      card_attackSet_two, liveInd, caughtFlag]
  · simp [binTail]

/-- a monitor that flags an attack in round 0 and misses an attack in any later round; no false positives -/
noncomputable def classMonitor : Finset (Fin 2) → List (AOut Bool) → Bool → Bool → ℝ :=
  fun _ g a f => if f = (a && decide (g.length = 0)) then 1 else 0

/-- the benchmark attacker: attacks in round 0 with probability 1/2, otherwise in round 1 -/
noncomputable def spreadAttacker : List (AOut Bool) → Bool → ℝ :=
  fun g a => if g.length = 0 then 1 / 2 else if a = !(g.headD (false, false, false)).1 then 1 else 0

/-- **Average recall is not conditional recall** (N = 2, no reserved audits, Bf = 2, k = 1, no false positives).
Against an attacker spread evenly over the two rounds the monitor's miss rate is 1/2, so a benchmark would report
recall 1/2. The attacker who always picks round 1 is never caught. Putting ρ = 1/2, α = 0 into
`split_flag_bound` would give 1/2 for every attacker; the premise fails because recall at round-1 histories is 0. -/
theorem average_recall_witness :
    val (splitK 2 spreadAttacker classMonitor (∅ : Finset (Fin 2))) (totSucc (N := 2) 1) 2 [] = 1 / 2 ∧
    val (splitK 2 (attackAt 1) classMonitor (∅ : Finset (Fin 2))) (totSucc (N := 2) 1) 2 [] = 1 ∧
    (1 - (1 / 2 : ℝ)) ^ 1 + binTail 0 2 2 0 = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [splitK_val_two]
    simp [spreadAttacker, classMonitor, catchRule, memN, flagCount, totSucc,
      card_attackSet_two, liveInd, caughtFlag]
  · rw [splitK_val_two]
    simp [attackAt, classMonitor, catchRule, memN, flagCount, totSucc,
      card_attackSet_two, liveInd, caughtFlag]
  · simp [binTail]; norm_num

theorem card_attackSet_three (o₀ o₁ o₂ : AOut Bool) :
    (attackSet (N := 3) [o₀, o₁, o₂]).card =
      (if o₀.1 = true then 1 else 0) + (if o₁.1 = true then 1 else 0) + (if o₂.1 = true then 1 else 0) := by
  unfold attackSet
  rw [Finset.card_filter, Fin.sum_univ_three]
  simp [attacked]

/-- a three-round split game, written out -/
theorem splitK_val_three {N : ℕ} (Bf : ℕ) (σ : List (AOut Bool) → Bool → ℝ)
    (τ : Finset (Fin N) → List (AOut Bool) → Bool → Bool → ℝ) (S : Finset (Fin N))
    (pay : List (AOut Bool) → ℝ) :
    val (splitK Bf σ τ S) pay 3 [] = ∑ a : Bool, ∑ f : Bool, σ [] a * τ S [] a f *
      ∑ a' : Bool, ∑ f' : Bool, σ [(a, f, catchRule Bf S [] a f)] a' * τ S [(a, f, catchRule Bf S [] a f)] a' f' *
        ∑ a'' : Bool, ∑ f'' : Bool,
          σ [(a, f, catchRule Bf S [] a f), (a', f', catchRule Bf S [(a, f, catchRule Bf S [] a f)] a' f')] a'' *
          τ S [(a, f, catchRule Bf S [] a f), (a', f', catchRule Bf S [(a, f, catchRule Bf S [] a f)] a' f')] a'' f'' *
          pay [(a, f, catchRule Bf S [] a f), (a', f', catchRule Bf S [(a, f, catchRule Bf S [] a f)] a' f'),
            (a'', f'', catchRule Bf S
              [(a, f, catchRule Bf S [] a f), (a', f', catchRule Bf S [(a, f, catchRule Bf S [] a f)] a' f')]
              a'' f'')] := by
  show val (splitK Bf σ τ S) pay (0 + 1 + 1 + 1) [] = _
  simp only [splitK_val_succ]
  simp [Leakage.val]

/-- a monitor whose FALSE POSITIVES depend on the schedule: it flags an attack with probability 1/2 whatever the
schedule and history (so its conditional recall is exactly 1/2 for every schedule), and it flags the non-attack
round 0 exactly when round 1 is reserved -/
noncomputable def leakMonitor : Finset (Fin 3) → List (AOut Bool) → Bool → Bool → ℝ :=
  fun S g a f => if a then 1 / 2 else (if f = (decide (g.length = 0) && decide (memN S 1)) then 1 else 0)

/-- the attacker that waits in round 0, then attacks in round 1 if round 0 was not flagged and in round 2 if it was -/
noncomputable def leakAttacker : List (AOut Bool) → Bool → ℝ :=
  fun g a => if a = (decide (g.length = 1) && !(g.headD (false, false, false)).2.1 ||
    decide (g.length = 2) && (g.headD (false, false, false)).2.1) then 1 else 0

/-- **Schedule-dependent flags break the product** (N = 3, Bh = 1, Bf = 2, k = 1). The monitor's recall is exactly
1/2 at every history and for every schedule, so the per-schedule premise of `split_flag_bound` holds with ρ = 1/2.
Its false positive in round 0 reveals whether round 1 is reserved. The attacker reads that flag and attacks in a
round it knows is not reserved; under each of the three schedules it succeeds with probability 1/2 = (1−ρ)^1, not
the product C(2,1)/C(3,1) · (1 − 1/2) = 1/3. `split_product_pre` requires an S-independent flag law for this reason. -/
theorem dependence_witness :
    val (splitK 2 leakAttacker leakMonitor ({0} : Finset (Fin 3))) (totSucc (N := 3) 1) 3 [] = 1 / 2 ∧
    val (splitK 2 leakAttacker leakMonitor ({1} : Finset (Fin 3))) (totSucc (N := 3) 1) 3 [] = 1 / 2 ∧
    val (splitK 2 leakAttacker leakMonitor ({2} : Finset (Fin 3))) (totSucc (N := 3) 1) 3 [] = 1 / 2 ∧
    (∀ (S : Finset (Fin 3)) (g : List (AOut Bool)), leakMonitor S g true true = 1 / 2) ∧
    (Nat.choose (3 - 1) 1 : ℝ) / (Nat.choose 3 1 : ℝ) * (1 - 1 / 2) ^ 1 = 1 / 3 := by
  have m00 : memN ({0} : Finset (Fin 3)) 0 := by decide
  have m01 : ¬ memN ({0} : Finset (Fin 3)) 1 := by decide
  have m02 : ¬ memN ({0} : Finset (Fin 3)) 2 := by decide
  have m10 : ¬ memN ({1} : Finset (Fin 3)) 0 := by decide
  have m11 : memN ({1} : Finset (Fin 3)) 1 := by decide
  have m12 : ¬ memN ({1} : Finset (Fin 3)) 2 := by decide
  have m20 : ¬ memN ({2} : Finset (Fin 3)) 0 := by decide
  have m21 : ¬ memN ({2} : Finset (Fin 3)) 1 := by decide
  have m22 : memN ({2} : Finset (Fin 3)) 2 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [splitK_val_three]
    simp [leakAttacker, leakMonitor, catchRule, m00, m01, m02, flagCount, totSucc, card_attackSet_three, liveInd,
      caughtFlag]
  · rw [splitK_val_three]
    simp [leakAttacker, leakMonitor, catchRule, m10, m11, m12, flagCount, totSucc, card_attackSet_three, liveInd,
      caughtFlag]
  · rw [splitK_val_three]
    simp [leakAttacker, leakMonitor, catchRule, m20, m21, m22, flagCount, totSucc, card_attackSet_three, liveInd,
      caughtFlag]
  · intro S g; simp [leakMonitor]
  · norm_num [Nat.choose]

end Witnesses

/-! ## 6. Numbers -/

section Numbers

/-- **One-step attacks.** For k = 1 the hidden-schedule bound is exactly 1 − Bh/N: with a 2% reserved budget the
reserved audits alone bound a single-step attack's success only by 0.98 (flag audits can lower the actual value).
`AuditBudget.random_subset_survival` shows 1 − Bh/N is the exact survival of a fixed one-round attack against the
schedule alone, so the hidden-schedule bound is not loose. -/
theorem hidden_one_step {N Bh : ℕ} (hN : 0 < N) (hB : Bh ≤ N) :
    (Nat.choose (N - 1) Bh : ℝ) / (Nat.choose N Bh : ℝ) = 1 - (Bh : ℝ) / N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have key := Nat.choose_mul_succ_eq n Bh
  have key' : (Nat.choose n Bh : ℝ) * ((n : ℝ) + 1) = (Nat.choose (n + 1) Bh : ℝ) * ((n : ℝ) + 1 - Bh) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) key
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hB] at this
    exact this
  have hc : (0 : ℝ) < (Nat.choose (n + 1) Bh : ℝ) := by exact_mod_cast Nat.choose_pos hB
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Nat.add_sub_cancel, div_eq_iff hc.ne']
  push_cast
  field_simp
  linarith

/-- **Numeric instance of the composition.** N = 100, Bh = 10 reserved audits, k = 5, conditional recall 1/2 while
flag budget remains: P(≥ 5 attacks, ≥ 5 of them pre-exhaustion, never caught) ≤ 10104934117421/553929902606080
≈ 0.0182, against ≈ 0.584 from the hidden schedule alone and (1/2)^5 = 0.03125 from the flags alone. -/
theorem split_example (Bf : ℕ) (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ₀ : List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ g a, IsDist (τ₀ g a))
    (hrec : ∀ g, flagCount g < Bf → (1 / 2 : ℝ) ≤ τ₀ g true true) :
    ∑ S : Finset (Fin 100), pU 100 10 S * val (splitK Bf σ (fun _ => τ₀) S) (preSucc (N := 100) 5 Bf) 100 []
      ≤ (10104934117421 : ℝ) / 553929902606080 := by
  have h := split_product_pre (N := 100) 5 10 Bf (by norm_num) (1 / 2) (by norm_num) (by norm_num) σ hσ τ₀ hτ hrec
  rw [show (100 - 5 : ℕ) = 95 from rfl, AuditBudget.choose_95_10, AuditBudget.choose_100_10] at h
  refine h.trans (le_of_eq ?_)
  norm_num

end Numbers

end ControlStack.SplitAudit

#print axioms ControlStack.SplitAudit.splitK_val_succ
#print axioms ControlStack.SplitAudit.split_flag_bound
#print axioms ControlStack.SplitAudit.split_flag_bound_avg
#print axioms ControlStack.SplitAudit.split_hidden_bound
#print axioms ControlStack.SplitAudit.split_min_bound
#print axioms ControlStack.SplitAudit.split_product_pre
#print axioms ControlStack.SplitAudit.split_product_bound
#print axioms ControlStack.SplitAudit.exhaustion_witness
#print axioms ControlStack.SplitAudit.average_recall_witness
#print axioms ControlStack.SplitAudit.dependence_witness
#print axioms ControlStack.SplitAudit.hidden_one_step
#print axioms ControlStack.SplitAudit.split_example
