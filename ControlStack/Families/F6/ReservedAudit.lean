/-
F6: a POSITIVE audit policy under false positives (the counterpart of `Necessity.exhausted_no_audit` and
`Necessity.fp_exhaustion_breaks_audit`; RUNTIME-VM-HANDOFF.md §7.2).

Policy (reserved budget). The total audit budget is B = Bh + Bf.
- Bh rounds form a hidden schedule S, drawn uniformly from the Bh-subsets of the N rounds before play, independently
  of every flag. Audits on S are never spent on, cancelled by, or refunded by flags.
- The other Bf audits are spent first-come on flagged rounds. False positives can exhaust them.

Results.
1. `reserved_leak_bound`: general transfer form. Use ANY round kernel: hidden state of any type (monitor scores,
   false-positive flags, flag-triggered audits, even ones that depend on S) and a visible output (attack bit, leak,
   catch flag) dominated on non-catch outputs by a certificate cl. Success means ≥ k attacks, no attacked round in
   S, and no catch flag ever. Its probability is ≤ C(N−k,Bh)/C(N,Bh) · mass(cl without catch outputs).
   Unlike `Leakage.audit_leak_bound`, the kernel need NOT report S-audits as catch flags: the success indicator
   includes "no catch flag", so extra (flag-triggered) catches can only help.
2. `reserved_adaptive`: adversary class ADAPTIVE_FEEDBACK, no leak. If the attacker's next attack bit has law
   σ(visible history), whatever the hidden part, then success probability ≤ C(N−k,Bh)/C(N,Bh), for EVERY flag process.
   `reserved_policy_bound` applies this to the concrete reserved policy kernel `reservedK`. Its flag law φ is
   arbitrary and may depend on S, the full hidden history and the current attack bit (adversarially chosen false
   positives). Flag-triggered audits fire on flagged rounds while fewer than Bf earlier rounds were flagged.
3. Availability: `flagRun_audits_le` and `flag_audits_le` show the flag-triggered audits never exceed Bf, and
   `reserved_total_le` gives total audits ≤ Bh + Bf for every flag sequence.
4. Imperfect recall, adversary class NON_ADAPTIVE (fixed attack set, no feedback). Each audited attack round is
   caught independently with probability rec i ≥ r. Then
   `recall_miss_le`: P(no catch) ≤ b + (1 − b)(1 − r) with b = C(N−k,B)/C(N,B).
   `missRecall_const` is the exact schedule-sum Σ_S p(S)(1−r)^{|S∩A|}.
   The hypergeometric collapse Σ_j C(k,j)C(N−k,B−j)/C(N,B)(1−r)^j is NOT proved.
5. Necessity witnesses:
   - `observable_reserved_nogo` and `observable_and_exhausted`: an observable reserved schedule plus exhausted flag
     budget leaves an attack set that is audited nowhere;
   - `recall_zero_vacuous`: with recall 0 the miss probability is exactly 1, so the r premise is load-bearing;
   - `reserved_example` and `recall_example`: non-vacuous numbers for N = 100, Bh = 10, k = 5:
     ≤ 10104934117421/17310309456440 ≈ 0.584, and ≤ (that + 1)/2 ≈ 0.792 at recall 1/2.

Limits (what is NOT claimed).
- S-audits catch attacked rounds perfectly in results 1–3. This is encoded in the success indicator: an attacked
  S-round is a failure. Results 1–3 do not cover imperfect recall on the reserved audits.
- Result 4 is non-adaptive only. An adaptive imperfect-recall bound would need a certificate that depends on S,
  because a missed S-audit is an S-dependent non-catch output. The S-independent transfer machinery
  (`Leakage.seq_transfer`) does not provide such a certificate, and none is proved here.
- The schedule is hidden: in result 2 the attacker's visible output carries no information about S beyond catch
  flags. Any timing or side leak about S belongs in result 1's certificate cl, and mass(cl) may exceed 1.
- These are statements about the model. That a deployment draws S uniformly, keeps it hidden, and audits as
  modelled is a correspondence obligation (trusted_stack/audit.py is a reference schedule only).
- Classical mathematics: optional stopping and maximal-leakage transfer are reused from `Core/Leakage.lean`. No
  novelty is claimed.
-/
import ControlStack.Core.Leakage
import ControlStack.Witnesses.Necessity

namespace ControlStack.ReservedAudit

open Finset ControlStack.Leakage ControlStack.Covert

/-! ## 1. General transfer bound for reserved hidden audits -/

section General

variable {N : ℕ} {Y Z : Type} [Fintype Y] [Fintype Z]

/-- the attack succeeds: ≥ k attacks, no attacked round in the reserved schedule S, and no catch flag at all -/
noncomputable def successInd (k : ℕ) (S : Finset (Fin N)) (t : List (AOut Z)) : ℝ :=
  survInd k S t * liveInd caughtFlag t

/-- uniform weight on size-B schedules -/
noncomputable def pU (N B : ℕ) (S : Finset (Fin N)) : ℝ :=
  if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0

theorem pU_nonneg (N B : ℕ) (S : Finset (Fin N)) : 0 ≤ pU N B S := by
  unfold pU; split_ifs <;> positivity

/-- **Reserved hidden audits, transfer form** (all-schedule hypotheses). Adversary class: ADAPTIVE_FEEDBACK
(plus SIDE_OBSERVING through the certificate `cl`). The kernel is arbitrary: the hidden state may carry monitor
scores, false-positive flags and flag-triggered audits; no consistency between catch flags and S is needed. -/
theorem reserved_leak_bound_all (k B : ℕ) (hB : B ≤ N)
    (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ)
    (hK0 : ∀ S h z, 0 ≤ K S h z)
    (hdom : ∀ S h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o)
    (hK1 : ∀ S h, ∑ z, K S h z ≤ 1)
    (hcl0 : ∀ g o, 0 ≤ cl g o) :
    ∑ S : Finset (Fin N), pU N B S * val (K S) (successInd k S) N []
      ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * mass (dropStop caughtFlag cl) N [] := by
  set b := (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
  set c : List (AOut Z) → AOut Z → ℝ := fun g o => if o.2.2 then 1 else cl g o
  have hc0 : ∀ g o, 0 ≤ c g o := fun g o => by simp only [c]; split_ifs; exact zero_le_one; exact hcl0 g o
  have hdomc : ∀ S, Dominated (K S) c := by
    intro S h o
    simp only [c]
    split_ifs with hf
    · calc ∑ y, K S h (y, o) ≤ ∑ z, K S h z := by
            rw [Fintype.sum_prod_type]
            exact Finset.sum_le_sum fun y _ => Finset.single_le_sum (f := fun o' => K S h (y, o'))
              (fun o' _ => hK0 S h _) (Finset.mem_univ o)
        _ ≤ 1 := hK1 S h
    · exact hdom S h o (by simpa using hf)
  have hpay0 : ∀ (S : Finset (Fin N)) (t : List (AOut Z)), 0 ≤ successInd k S t := fun S t =>
    mul_nonneg (survInd_nonneg k S t) (liveInd_nonneg caughtFlag t)
  have h2 := seq_transfer (pU N B) K c (fun S => successInd k S)
    (fun t => b * liveInd caughtFlag t) N (pU_nonneg N B) hK0 hdomc hc0 hpay0 (by
      intro t
      simp only [successInd]
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (blind_audit k B hB t) (liveInd_nonneg caughtFlag t))
  rw [cval_smul, cval_live] at h2
  have hl : liveInd caughtFlag ([] : List (AOut Z)) = 1 := by simp [liveInd]
  rw [hl, one_mul] at h2
  have hdrop : dropStop caughtFlag c = dropStop caughtFlag cl := by
    funext g o; by_cases hf : o.2.2 = true <;> simp [dropStop, c, caughtFlag, hf]
  rw [hdrop] at h2
  exact h2

/-- **Reserved hidden audits, transfer form** (support form: hypotheses only on schedules the protocol can draw). -/
theorem reserved_leak_bound (k B : ℕ) (hB : B ≤ N)
    (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ)
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z)
    (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1)
    (hdom : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h o, o.2.2 = false →
      ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o)
    (hcl0 : ∀ g o, 0 ≤ cl g o) :
    ∑ S : Finset (Fin N), pU N B S * val (K S) (successInd k S) N []
      ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * mass (dropStop caughtFlag cl) N [] := by
  classical
  set K' : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ :=
    fun S => if S ∈ AuditBudget.randomSchedules N B then K S else fun _ _ => 0 with hK'
  have hsame : ∀ S : Finset (Fin N), pU N B S * val (K S) (successInd k S) N []
      = pU N B S * val (K' S) (successInd k S) N [] := by
    intro S
    by_cases hS : S ∈ AuditBudget.randomSchedules N B
    · simp only [hK', if_pos hS]
    · simp only [pU, if_neg hS, zero_mul]
  rw [Finset.sum_congr rfl (fun S _ => hsame S)]
  refine reserved_leak_bound_all k B hB K' cl ?_ ?_ ?_ hcl0
  · intro S h z; by_cases hS : S ∈ AuditBudget.randomSchedules N B
    · simp only [hK', if_pos hS]; exact hK0 S hS h z
    · simp [hK', hS]
  · intro S h o hf; by_cases hS : S ∈ AuditBudget.randomSchedules N B
    · simp only [hK', if_pos hS]; exact hdom S hS h o hf
    · simp only [hK', if_neg hS, Finset.sum_const_zero]; exact hcl0 _ _
  · intro S h; by_cases hS : S ∈ AuditBudget.randomSchedules N B
    · simp only [hK', if_pos hS]; exact hK1 S hS h
    · simp [hK', hS]

end General

/-! ## 2. Adaptive attackers, any flag process -/

section Adaptive

variable {N : ℕ} {Y : Type} [Fintype Y]

/-- **Reserved hidden audits beat every flag process.** Adversary class: ADAPTIVE_FEEDBACK (the attacker sees its
own actions and every catch flag; no other leak). The kernel's hidden part is arbitrary: false-positive flags,
flag-triggered audits with any budget, monitor scores, even processes that depend on the schedule S. The only
requirement is that the attacker's next attack bit has law σ(visible history) (`hmarg`, as an upper bound). Then
the attack succeeds (≥ k attacks, none in S, never caught) with probability ≤ C(N−k,Bh)/C(N,Bh). -/
theorem reserved_adaptive (k Bh : ℕ) (hB : Bh ≤ N)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z)
    (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1)
    (hmarg : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool),
      ∑ y, ∑ c : Bool, K S h (y, (a, (), c)) ≤ σ (h.map Prod.snd) a) :
    ∑ S : Finset (Fin N), pU N Bh S * val (K S) (successInd k S) N []
      ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ) := by
  have h := reserved_leak_bound k Bh hB K (fun g o => σ g o.1) hK0 hK1
    (fun S hS h o hf => by
      obtain ⟨a, u, c⟩ := o
      cases u
      simp only at hf; subst hf
      refine le_trans ?_ (hmarg S hS h a)
      apply Finset.sum_le_sum; intro y _
      rw [Fintype.sum_bool]
      have := hK0 S hS h (y, (a, (), true))
      linarith)
    (fun g o => (hσ g).1 o.1)
  have hm : mass (dropStop caughtFlag (fun g (o : AOut Unit) => σ g o.1)) N [] ≤ 1 ^ N := by
    apply mass_le_pow _ 1
    · intro g o; unfold dropStop; split_ifs; exact le_rfl; exact (hσ g).1 o.1
    · exact zero_le_one
    · intro g
      simp only [dropStop, caughtFlag, Fintype.sum_prod_type, Fintype.univ_unit, Finset.sum_singleton,
        Fintype.sum_bool]
      have h1 := (hσ g).2
      rw [Fintype.sum_bool] at h1
      simp; linarith
  rw [one_pow] at hm
  have hb : (0 : ℝ) ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ) := by positivity
  calc _ ≤ _ := h
    _ ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ) * 1 := mul_le_mul_of_nonneg_left hm hb
    _ = _ := mul_one _

/-! ### The concrete reserved policy -/

/-- trusted flag bookkeeping: (flags so far, flag-triggered audits so far). A flagged round is audited while
fewer than Bf earlier rounds were flagged (first-come; false positives consume the budget). -/
def flagStep (Bf : ℕ) (st : ℕ × ℕ) (f : Bool) : ℕ × ℕ :=
  (st.1 + (if f then 1 else 0), st.2 + (if f && decide (st.1 < Bf) then 1 else 0))

def flagRun (Bf : ℕ) (fs : List Bool) : ℕ × ℕ := fs.foldl (flagStep Bf) (0, 0)

theorem flagRun_inv (Bf : ℕ) (fs : List Bool) (st : ℕ × ℕ) (h : st.2 = min st.1 Bf) :
    (fs.foldl (flagStep Bf) st).2 = min (fs.foldl (flagStep Bf) st).1 Bf := by
  induction fs generalizing st with
  | nil => simpa using h
  | cons f fs ih =>
    apply ih
    obtain ⟨n, a⟩ := st
    simp only at h ⊢
    subst h
    cases f <;> simp only [flagStep, Bool.false_and, Bool.true_and] <;>
      by_cases hn : n < Bf <;> simp [hn] <;> omega

/-- **Availability (flag part).** For every flag sequence, flag-triggered audits never exceed Bf. -/
theorem flagRun_audits_le (Bf : ℕ) (fs : List Bool) : (flagRun Bf fs).2 ≤ Bf := by
  have := flagRun_inv Bf fs (0, 0) (by simp)
  unfold flagRun; rw [this]; exact min_le_right _ _

/-- the reserved-policy round kernel. Hidden y: this round's flag, drawn from an ARBITRARY law φ that may depend on
the schedule S, the full hidden history and the current attack bit. Visible output: (attack bit a ~ σ, unit, catch
flag), where catch = attack ∧ (round ∈ S ∨ (flag ∧ flag budget left)). -/
noncomputable def reservedK (Bf : ℕ) (σ : List (AOut Unit) → Bool → ℝ)
    (φ : Finset (Fin N) → List (Bool × AOut Unit) → Bool → Bool → ℝ) :
    Finset (Fin N) → List (Bool × AOut Unit) → Bool × AOut Unit → ℝ :=
  fun S h yo => σ (h.map Prod.snd) yo.2.1 * φ S h yo.2.1 yo.1 *
    (if yo.2.2.2 = (yo.2.1 && (decide (memN S (h.map Prod.snd).length) ||
        (yo.1 && decide ((flagRun Bf (h.map Prod.fst)).1 < Bf)))) then 1 else 0)

theorem reservedK_nonneg (Bf : ℕ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (φ : Finset (Fin N) → List (Bool × AOut Unit) → Bool → Bool → ℝ) (hφ : ∀ S h a, IsDist (φ S h a))
    (S : Finset (Fin N)) (h : List (Bool × AOut Unit)) (z : Bool × AOut Unit) : 0 ≤ reservedK Bf σ φ S h z := by
  unfold reservedK
  exact mul_nonneg (mul_nonneg ((hσ _).1 _) ((hφ _ _ _).1 _)) (by split_ifs <;> norm_num)

theorem sum_ite_bool (e : Bool) : ∑ c : Bool, (if c = e then (1 : ℝ) else 0) = 1 := by
  cases e <;> simp

/-- summing out the catch flag of the reserved kernel -/
theorem reservedK_sum_c (Bf : ℕ) (σ : List (AOut Unit) → Bool → ℝ)
    (φ : Finset (Fin N) → List (Bool × AOut Unit) → Bool → Bool → ℝ)
    (S : Finset (Fin N)) (h : List (Bool × AOut Unit)) (y a : Bool) :
    ∑ c : Bool, reservedK Bf σ φ S h (y, (a, (), c)) = σ (h.map Prod.snd) a * φ S h a y := by
  unfold reservedK
  simp only
  rw [← Finset.mul_sum, sum_ite_bool, mul_one]

theorem reservedK_sum (Bf : ℕ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (φ : Finset (Fin N) → List (Bool × AOut Unit) → Bool → Bool → ℝ) (hφ : ∀ S h a, IsDist (φ S h a))
    (S : Finset (Fin N)) (h : List (Bool × AOut Unit)) : ∑ z, reservedK Bf σ φ S h z ≤ 1 := by
  have e : ∑ z, reservedK Bf σ φ S h z = ∑ y : Bool, ∑ a : Bool, ∑ c : Bool, reservedK Bf σ φ S h (y, (a, (), c)) := by
    simp only [Fintype.sum_prod_type, Fintype.univ_unit, Finset.sum_singleton]
  rw [e]
  simp only [reservedK_sum_c]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, (hφ _ _ _).2, mul_one]
  rw [(hσ _).2]

/-- **The reserved policy, instantiated.** Adversary class: ADAPTIVE_FEEDBACK. For every adaptive attacker σ and
EVERY flag law φ (arbitrary false-positive pattern, possibly depending on S and on the attack), the attack succeeds
with probability ≤ C(N−k,Bh)/C(N,Bh), while flag-triggered audits never exceed Bf (`flagRun_audits_le`). -/
theorem reserved_policy_bound (k Bh Bf : ℕ) (hB : Bh ≤ N) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (φ : Finset (Fin N) → List (Bool × AOut Unit) → Bool → Bool → ℝ) (hφ : ∀ S h a, IsDist (φ S h a)) :
    ∑ S : Finset (Fin N), pU N Bh S * val (reservedK Bf σ φ S) (successInd k S) N []
      ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ) := by
  refine reserved_adaptive k Bh hB (reservedK Bf σ φ) σ hσ
    (fun S _ h z => reservedK_nonneg Bf σ hσ φ hφ S h z)
    (fun S _ h => reservedK_sum Bf σ hσ φ hφ S h) ?_
  intro S _ h a
  simp only [reservedK_sum_c, ← Finset.mul_sum, (hφ _ _ _).2, mul_one, le_refl]

end Adaptive

/-! ## 3. Availability -/

section Availability

variable {N : ℕ}

/-- **Availability (first-come flag audits, `Necessity.audited`).** For every flag pattern, at most Bf rounds are
flag-audited. -/
theorem flag_audits_le (Bf : ℕ) (flags : Fin N → Bool) :
    (univ.filter (fun i => Necessity.audited Bf flags i = true)).card ≤ Bf := by
  set cnt : Fin N → ℕ := fun i => (univ.filter (fun j : Fin N => j < i ∧ flags j = true)).card
  have hmaps : ∀ i ∈ univ.filter (fun i => Necessity.audited Bf flags i = true), cnt i ∈ range Bf := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and, Necessity.audited, Bool.and_eq_true, decide_eq_true_eq] at hi
    exact mem_range.2 hi.2
  have hinj : Set.InjOn cnt (univ.filter (fun i => Necessity.audited Bf flags i = true) : Set (Fin N)) := by
    have hlt : ∀ i i', flags i = true → i < i' → cnt i < cnt i' := by
      intro i i' hf hii'
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨i, by simp [hii', hf], by simp⟩
      · intro j hj
        simp only [mem_filter, mem_univ, true_and] at hj ⊢
        exact ⟨lt_trans hj.1 hii', hj.2⟩
    intro i hi i' hi' heq
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, Necessity.audited, Bool.and_eq_true] at hi hi'
    rcases lt_trichotomy i i' with h | h | h
    · exact absurd heq (ne_of_lt (hlt i i' hi.1 h))
    · exact h
    · exact absurd heq.symm (ne_of_lt (hlt i' i hi'.1 h))
  have := Finset.card_le_card_of_injOn cnt hmaps hinj
  simpa using this

/-- **Availability (total).** Reserved schedule of size Bh plus first-come flag audits: total audited rounds ≤ Bh + Bf,
for every flag pattern. -/
theorem reserved_total_le (Bh Bf : ℕ) (S : Finset (Fin N)) (hS : S.card = Bh) (flags : Fin N → Bool) :
    (S ∪ univ.filter (fun i => Necessity.audited Bf flags i = true)).card ≤ Bh + Bf := by
  calc _ ≤ S.card + (univ.filter (fun i => Necessity.audited Bf flags i = true)).card := card_union_le _ _
    _ ≤ Bh + Bf := by rw [hS]; exact Nat.add_le_add_left (flag_audits_le Bf flags) _

end Availability

/-! ## 4. Imperfect recall (non-adaptive) -/

section Recall

variable {N : ℕ}

/-- miss probability of a FIXED attack set A against a uniform size-B schedule, when each audited attack round i is
caught independently with probability rec i -/
noncomputable def missRecall (B : ℕ) (A : Finset (Fin N)) (rec : Fin N → ℝ) : ℝ :=
  ∑ S : Finset (Fin N), pU N B S * ∏ i ∈ S ∩ A, (1 - rec i)

theorem sum_pU (B : ℕ) (hB : B ≤ N) : ∑ S : Finset (Fin N), pU N B S = 1 := by
  have hC : (Nat.choose N B : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hB).ne'
  unfold pU
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  simp [AuditBudget.randomSchedules, card_powersetCard, hC]

theorem sum_pU_disjoint (B k : ℕ) (A : Finset (Fin N)) (hA : A.card = k) :
    ∑ S : Finset (Fin N), pU N B S * (if Disjoint S A then 1 else 0)
      = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) := by
  have hterm : ∀ S : Finset (Fin N), pU N B S * (if Disjoint S A then 1 else 0)
      = if S ∈ (AuditBudget.randomSchedules N B).filter (fun S => Disjoint S A)
        then (Nat.choose N B : ℝ)⁻¹ else 0 := by
    intro S
    by_cases h1 : S ∈ AuditBudget.randomSchedules N B <;>
      by_cases h2 : Disjoint S A <;> simp [pU, h1, h2]
  simp_rw [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    (AuditBudget.random_subset_survival (B := B) A hA).1, ← div_eq_mul_inv]

/-- exact schedule-sum form with constant recall r: Σ_S p(S) (1−r)^{|S∩A|} -/
theorem missRecall_const (B : ℕ) (A : Finset (Fin N)) (r : ℝ) :
    missRecall B A (fun _ => r) = ∑ S : Finset (Fin N), pU N B S * (1 - r) ^ (S ∩ A).card := by
  unfold missRecall
  simp [Finset.prod_const]

/-- **Imperfect recall, fixed attack set.** Adversary class: NON_ADAPTIVE. Each audited attack round is caught
independently with probability rec i ∈ [r, 1]. Then P(no catch) ≤ b + (1 − b)(1 − r), b = C(N−k,B)/C(N,B):
being audited at least once (probability 1 − b) costs the attacker at least a factor (1 − r). -/
theorem recall_miss_le (B k : ℕ) (hB : B ≤ N) (A : Finset (Fin N)) (hA : A.card = k)
    (r : ℝ) (rec : Fin N → ℝ) (hr0 : 0 ≤ r) (hrec : ∀ i, r ≤ rec i ∧ rec i ≤ 1) :
    missRecall B A rec ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) +
      (1 - (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)) * (1 - r) := by
  have hr1 : ∀ i, 0 ≤ 1 - rec i ∧ 1 - rec i ≤ 1 - r := fun i => ⟨by linarith [(hrec i).2], by linarith [(hrec i).1]⟩
  have hterm : ∀ S : Finset (Fin N), pU N B S * ∏ i ∈ S ∩ A, (1 - rec i)
      ≤ pU N B S * ((1 - r) + r * (if Disjoint S A then 1 else 0)) := by
    intro S
    apply mul_le_mul_of_nonneg_left _ (pU_nonneg N B S)
    by_cases hd : Disjoint S A
    · rw [Finset.disjoint_iff_inter_eq_empty.1 hd]; simp [hd]
    · have hne : (S ∩ A).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; exact fun h => hd (Finset.disjoint_iff_inter_eq_empty.2 h)
      have hcard : 1 ≤ (S ∩ A).card := Finset.card_pos.2 hne
      have hp : ∏ i ∈ S ∩ A, (1 - rec i) ≤ ∏ _i ∈ S ∩ A, (1 - r) :=
        Finset.prod_le_prod₀ (fun i _ => (hr1 i).1) (fun i _ => (hr1 i).2)
      rw [Finset.prod_const] at hp
      have hr1' : 1 - r ≤ 1 := by linarith
      have hr0' : 0 ≤ 1 - r := le_trans (hr1 hne.choose).1 (hr1 hne.choose).2
      have hpow : (1 - r) ^ (S ∩ A).card ≤ (1 - r) ^ 1 := pow_le_pow_of_le_one hr0' hr1' hcard
      simp only [hd, ite_false, mul_zero, add_zero]
      linarith [pow_one (1 - r)]
  calc missRecall B A rec ≤ ∑ S : Finset (Fin N), pU N B S * ((1 - r) + r * (if Disjoint S A then 1 else 0)) :=
        Finset.sum_le_sum fun S _ => hterm S
    _ = (1 - r) * ∑ S : Finset (Fin N), pU N B S +
          r * ∑ S : Finset (Fin N), pU N B S * (if Disjoint S A then 1 else 0) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro S _; ring
    _ = _ := by rw [sum_pU B hB, sum_pU_disjoint B k A hA]; ring

end Recall

/-! ## 5. Necessity witnesses and numbers -/

section Witnesses

/-- **Observable reserved schedule** (necessity of hiding S). If the reserved schedule S is known, an attack of
k ≤ N − Bh rounds avoids it entirely (`AuditBudget.observable_schedule_nogo`). -/
theorem observable_reserved_nogo {N Bh k : ℕ} (S : Finset (Fin N)) (hS : S.card = Bh) (hk : k ≤ N - Bh) :
    ∃ A : Finset (Fin N), A.card = k ∧ Disjoint S A :=
  let ⟨A, hA, hd, _⟩ := AuditBudget.observable_schedule_nogo S hS hk
  ⟨A, hA, hd⟩

/-- **Observable reserved schedule + exhausted flag budget** (concrete, N = 4, Bh = 1, Bf = 1). The reserved slot
{0} is known and every round raises a (false-positive) flag, so the single flag audit goes to round 0. The 2-step
attack {2, 3} is audited by neither part of the policy. -/
theorem observable_and_exhausted :
    Disjoint ({0} : Finset (Fin 4)) {2, 3} ∧
      ∀ i ∈ ({2, 3} : Finset (Fin 4)), Necessity.audited 1 (fun _ => true) i = false := by
  decide

/-- **Recall 0 makes the guarantee vacuous** (necessity of the recall premise): the miss probability is exactly 1,
and the bound of `recall_miss_le` at r = 0 is also 1. -/
theorem recall_zero_vacuous {N : ℕ} (B k : ℕ) (hB : B ≤ N) (A : Finset (Fin N)) :
    missRecall B A (fun _ => 0) = 1 ∧
      (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) +
        (1 - (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)) * (1 - 0) = 1 := by
  refine ⟨?_, by ring⟩
  unfold missRecall
  simp only [sub_zero, Finset.prod_const_one, mul_one]
  exact sum_pU B hB

/-- **Non-vacuous instance of the reserved policy.** N = 100 rounds, Bh = 10 reserved hidden audits, k = 5 attack
steps, any flag budget Bf and any flag law: success ≤ 10104934117421/17310309456440 ≈ 0.584. With the same number of
audits spent first-come on flags, false positives can drive this to 1 (`Necessity.exhausted_no_audit`). -/
theorem reserved_example (Bf : ℕ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (φ : Finset (Fin 100) → List (Bool × AOut Unit) → Bool → Bool → ℝ) (hφ : ∀ S h a, IsDist (φ S h a)) :
    ∑ S : Finset (Fin 100), pU 100 10 S * val (reservedK Bf σ φ S) (successInd 5 S) 100 []
      ≤ (10104934117421 : ℝ) / 17310309456440 := by
  have h := reserved_policy_bound 5 10 Bf (by norm_num) σ hσ φ hφ
  rw [show (100 - 5 : ℕ) = 95 from rfl, AuditBudget.choose_95_10, AuditBudget.choose_100_10] at h
  exact_mod_cast h

/-- **Non-vacuous imperfect-recall instance.** N = 100, B = 10, a fixed 5-round attack, recall ≥ 1/2 per audited
attack round: P(no catch) ≤ (10104934117421/17310309456440 + 1)/2 ≈ 0.792. -/
theorem recall_example (A : Finset (Fin 100)) (hA : A.card = 5) (rec : Fin 100 → ℝ)
    (hrec : ∀ i, 1 / 2 ≤ rec i ∧ rec i ≤ 1) :
    missRecall 10 A rec ≤ ((10104934117421 : ℝ) / 17310309456440 + 1) / 2 := by
  have h := recall_miss_le 10 5 (by norm_num) A hA (1 / 2) rec (by norm_num) hrec
  rw [show (100 - 5 : ℕ) = 95 from rfl, AuditBudget.choose_95_10, AuditBudget.choose_100_10] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end Witnesses

end ControlStack.ReservedAudit

#print axioms ControlStack.ReservedAudit.reserved_leak_bound_all
#print axioms ControlStack.ReservedAudit.reserved_leak_bound
#print axioms ControlStack.ReservedAudit.reserved_adaptive
#print axioms ControlStack.ReservedAudit.flagRun_audits_le
#print axioms ControlStack.ReservedAudit.reserved_policy_bound
#print axioms ControlStack.ReservedAudit.flag_audits_le
#print axioms ControlStack.ReservedAudit.reserved_total_le
#print axioms ControlStack.ReservedAudit.missRecall_const
#print axioms ControlStack.ReservedAudit.recall_miss_le
#print axioms ControlStack.ReservedAudit.observable_reserved_nogo
#print axioms ControlStack.ReservedAudit.observable_and_exhausted
#print axioms ControlStack.ReservedAudit.recall_zero_vacuous
#print axioms ControlStack.ReservedAudit.reserved_example
#print axioms ControlStack.ReservedAudit.recall_example
