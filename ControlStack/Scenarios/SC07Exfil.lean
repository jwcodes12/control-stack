/-
SC-07: weight exfiltration — a quantitative bound composing the egress QUOTA (F1/F5; runtime-tested in
`scenarios/SC-07/evidence/run-1`) with AUDITS (F6) and halt-on-catch (F3).

Setting.
- A secret artifact must leave: `S` is the number of INFORMATION bits that must cross the gateway for the attacker to
  have it (its size after the best possible encoding, i.e. at most its entropy/min-entropy if the attacker can
  compress). If `S` is measured in raw bytes of the weights, compression helps the attacker, so the bound below must
  then be read with the compressed size. The quota counts bits leaving on the mediated path.
- Time is divided into windows. The gateway lets at most `q` bits leave per window (enforced: a plan's per-window
  traffic is capped, `capped`).
- Each window carrying exfiltration traffic is caught with probability `c i ≥ p·r` (audited with probability ≥ p,
  an audit detects traffic with recall ≥ r), independently across windows, and the attacker gets no audit
  information. A catch HALTs (absorbing), so traffic after a catch never happens.
- An attacker with no audit information is a mixture of fixed plans (per-window bit counts). Conditioning on "not yet
  caught" adds nothing because the halt is absorbing, so a mixture over plans is the general strategy here.

Results.
1. `windows_needed`: completing exfiltration (≥ S bits through the quota) needs at least ⌈S/q⌉ windows with traffic.
2. `sc07_plan_bound` and `sc07_mixed` (independent per-window audits): P(complete before catch) ≤ (1 − p·r)^⌈S/q⌉ for
   every plan and every mixture of plans.
   `sc07_fixed_budget`: the hidden fixed-budget variant. B of N windows audited uniformly at random, recall r,
   ADAPTIVE_FEEDBACK attacker (sees its own actions and catch flags). P(≥ ⌈S/q⌉ traffic windows, never caught) ≤
   hypMiss N B ⌈S/q⌉ r (from `ReservedRecall.adaptive_recall_bound`; by 1 the window count is necessary for
   completion).
3. Witnesses:
   - `no_quota_one_window`: with q ≥ S, one window suffices, and the bound degenerates to 1 − c₀;
   - `observable_schedule_exfil`: if the audit schedule is observable, the attacker exfiltrates only in unaudited
     windows and is never caught.
4. `datacenter_example`: S = 8·10^11 bits (100 GB), q = 8·10^9 bits per window (1 GB), p·r = 0.05 gives
   ⌈S/q⌉ = 100 and P ≤ 0.95^100 < 0.006.
   `expected_leak_le`: partial exfiltration. The expected number of bits that leave before the catch is ≤ q/(p·r)
   (bits in the catching window are counted as leaked), for every plan of any length.

Limits. Side and covert channels outside the quota path are SC-01/02/04 and not bounded here. `S` is information
content, so it is a premise that the artifact cannot be reconstructed from fewer bits plus public knowledge.
Independence of per-window catch events is a premise of results 2 and 4 (the fixed-budget variant replaces it by a
uniformly random hidden schedule). Recall is per-window worst case, not a population average. Classical
probability; no novelty.
-/
import Mathlib.Tactic
import ControlStack.Families.F6.ReservedRecall
import ControlStack.AuditBudget

namespace ControlStack.SC07Exfil

open Finset

/-- ⌈S/q⌉ in ℕ -/
def ceilDiv (S q : ℕ) : ℕ := (S + q - 1) / q

/-- windows with exfiltration traffic -/
def traffic (b : List ℕ) : ℕ := b.countP (fun x => 0 < x)

/-- the gateway quota: at most `q` bits leave per window -/
def capped (q : ℕ) (b : List ℕ) : List ℕ := b.map (fun x => min x q)

/-- probability that no traffic window from index `i` on is caught, with per-window catch probabilities `c` -/
def survive (c : ℕ → ℝ) : List ℕ → ℕ → ℝ
  | [], _ => 1
  | x :: xs, i => (if 0 < x then 1 - c i else 1) * survive c xs (i + 1)

/-- expected bits that leave before the catch (bits of the catching window counted as leaked) -/
def expLeak (c : ℕ → ℝ) : List ℕ → ℕ → ℝ
  | [], _ => 0
  | x :: xs, i => (x : ℝ) + (if 0 < x then 1 - c i else 1) * expLeak c xs (i + 1)

theorem capped_le (q : ℕ) (b : List ℕ) : ∀ x ∈ capped q b, x ≤ q := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
  exact min_le_right _ _

/-- pigeonhole: total traffic ≤ q · (windows with traffic) -/
theorem sum_le_traffic (q : ℕ) (b : List ℕ) (hb : ∀ x ∈ b, x ≤ q) : b.sum ≤ q * traffic b := by
  induction b with
  | nil => simp
  | cons x xs ih =>
    have hx := hb x List.mem_cons_self
    have ih' := ih (fun y hy => hb y (List.mem_cons_of_mem x hy))
    simp only [List.sum_cons, traffic, List.countP_cons] at ih' ⊢
    split_ifs with h
    · simp only [decide_eq_true_eq] at h
      rw [Nat.mul_add, Nat.mul_one]; omega
    · simp only [decide_eq_true_eq, not_lt, Nat.le_zero] at h
      subst h; simpa using ih'

theorem ceilDiv_le (S q m : ℕ) (hq : 0 < q) (h : S ≤ q * m) : ceilDiv S q ≤ m := by
  unfold ceilDiv
  have h1 : S + q - 1 < (m + 1) * q := by
    have : (m + 1) * q = q * m + q := by ring
    omega
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hq).2 h1)

/-- **1. Windows needed.** Completing exfiltration of `S` bits through a quota of `q` bits per window needs at least
⌈S/q⌉ windows with traffic. -/
theorem windows_needed (S q : ℕ) (hq : 0 < q) (b : List ℕ) (hb : ∀ x ∈ b, x ≤ q) (hS : S ≤ b.sum) :
    ceilDiv S q ≤ traffic b :=
  ceilDiv_le S q _ hq (hS.trans (sum_le_traffic q b hb))

theorem survive_nonneg (c : ℕ → ℝ) (hc : ∀ i, c i ≤ 1) (b : List ℕ) (i : ℕ) : 0 ≤ survive c b i := by
  induction b generalizing i with
  | nil => simp [survive]
  | cons x xs ih =>
    simp only [survive]
    apply mul_nonneg _ (ih _)
    split_ifs
    · linarith [hc i]
    · norm_num

/-- each traffic window survives with probability ≤ 1 − p·r: the plan survives with probability ≤ (1 − pr)^traffic -/
theorem survive_le (c : ℕ → ℝ) (pr : ℝ) (hc : ∀ i, pr ≤ c i ∧ c i ≤ 1) (hpr : pr ≤ 1) (b : List ℕ) (i : ℕ) :
    survive c b i ≤ (1 - pr) ^ traffic b := by
  induction b generalizing i with
  | nil => simp [survive, traffic]
  | cons x xs ih =>
    have hs := survive_nonneg c (fun j => (hc j).2) xs (i + 1)
    have ih' := ih (i + 1)
    unfold traffic at ih' ⊢
    by_cases h : 0 < x
    · simp only [survive, h, ite_true, List.countP_cons, decide_true, pow_succ]
      have h1 : 1 - c i ≤ 1 - pr := by linarith [(hc i).1]
      calc (1 - c i) * survive c xs (i + 1) ≤ (1 - pr) * (1 - pr) ^ List.countP (fun x => decide (0 < x)) xs :=
            mul_le_mul h1 ih' hs (by linarith)
        _ = _ := by ring
    · simp only [survive, h, ite_false, List.countP_cons, decide_false, one_mul]
      simpa using ih'

/-- **2a. Bound for one plan.** If the quota-capped plan completes exfiltration, it survives every traffic window with
probability ≤ (1 − p·r)^⌈S/q⌉. -/
theorem sc07_plan_bound (S q : ℕ) (hq : 0 < q) (c : ℕ → ℝ) (pr : ℝ) (hc : ∀ i, pr ≤ c i ∧ c i ≤ 1) (hpr0 : 0 ≤ pr)
    (hpr : pr ≤ 1) (b : List ℕ) (hS : S ≤ (capped q b).sum) :
    survive c (capped q b) 0 ≤ (1 - pr) ^ ceilDiv S q := by
  have hw := windows_needed S q hq (capped q b) (capped_le q b) hS
  calc survive c (capped q b) 0 ≤ (1 - pr) ^ traffic (capped q b) := survive_le c pr hc hpr _ 0
    _ ≤ (1 - pr) ^ ceilDiv S q := pow_le_pow_of_le_one (by linarith) (by linarith) hw

/-- **2b. Any attacker without audit information** (a mixture of plans with weights `w`): P(complete exfiltration
before a catch) ≤ (1 − p·r)^⌈S/q⌉. -/
theorem sc07_mixed {Ω : Type} [Fintype Ω] (S q : ℕ) (hq : 0 < q) (c : ℕ → ℝ) (pr : ℝ)
    (hc : ∀ i, pr ≤ c i ∧ c i ≤ 1) (hpr0 : 0 ≤ pr) (hpr : pr ≤ 1)
    (w : Ω → ℝ) (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1) (plan : Ω → List ℕ) :
    ∑ ω, w ω * (if S ≤ (capped q (plan ω)).sum then survive c (capped q (plan ω)) 0 else 0)
      ≤ (1 - pr) ^ ceilDiv S q := by
  calc ∑ ω, w ω * (if S ≤ (capped q (plan ω)).sum then survive c (capped q (plan ω)) 0 else 0)
      ≤ ∑ ω, w ω * (1 - pr) ^ ceilDiv S q := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hw0 ω)
        split_ifs with h
        · exact sc07_plan_bound S q hq c pr hc hpr0 hpr _ h
        · exact pow_nonneg (by linarith) _
    _ = (1 - pr) ^ ceilDiv S q := by rw [← Finset.sum_mul, hw1, one_mul]

/-- **2c. Hidden fixed audit budget, adaptive attacker.** B of N windows audited uniformly at random (hidden), recall
r. The attacker's per-window traffic bit has law σ(visible history). Then P(≥ ⌈S/q⌉ traffic windows and never
caught) ≤ hypMiss N B ⌈S/q⌉ r. By `windows_needed`, completing exfiltration requires that event. Instance of
`ReservedRecall.adaptive_recall_bound`; adversary class ADAPTIVE_FEEDBACK. -/
theorem sc07_fixed_budget {N : ℕ} {Y : Type} [Fintype Y] (S q B : ℕ) (hB : B ≤ N) (r : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1)
    (K : Finset (Fin N) → List (Y × Leakage.AOut Unit) → Y × Leakage.AOut Unit → ℝ)
    (σ : List (Leakage.AOut Unit) → Bool → ℝ) (hσ : ∀ g, Covert.IsDist (σ g))
    (hK0 : ∀ T, T ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K T h z)
    (hK1 : ∀ T, T ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K T h z ≤ 1)
    (hrec : ∀ T, T ∈ AuditBudget.randomSchedules N B → ∀ h (a : Bool),
      ∑ y, K T h (y, (a, (), false)) ≤
        σ (h.map Prod.snd) a * (if Leakage.memN T (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) :
    ∑ T : Finset (Fin N), ReservedAudit.pU N B T * Leakage.val (K T) (ReservedRecall.recallSucc (N := N) (ceilDiv S q)) N []
      ≤ ReservedRecall.hypMiss N B (ceilDiv S q) r :=
  ReservedRecall.adaptive_recall_bound (ceilDiv S q) B hB r hr0 hr1 K σ hσ hK0 hK1 hrec

/-! ## 3. Witnesses -/

/-- **No quota**: if q ≥ S > 0, one window suffices (⌈S/q⌉ = 1), and the plan [S] survives with probability 1 − c₀. -/
theorem no_quota_one_window (S q : ℕ) (hS : 0 < S) (hq : S ≤ q) (c : ℕ → ℝ) :
    ceilDiv S q = 1 ∧ (capped q [S]).sum = S ∧ traffic (capped q [S]) = 1 ∧
      survive c (capped q [S]) 0 = 1 - c 0 := by
  have hq0 : 0 < q := lt_of_lt_of_le hS hq
  have hmin : min S q = S := min_eq_left hq
  refine ⟨?_, by simp [capped, hmin], by simp [capped, hmin, traffic, hS], by simp [capped, hmin, survive, hS]⟩
  unfold ceilDiv
  apply le_antisymm
  · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hq0).2 (by omega))
  · exact (Nat.le_div_iff_mul_le hq0).2 (by omega)

/-- **Observable schedule**: if windows 0 and 2 are known to be audited (catch probability 1) and the others are not,
the plan that sends q bits only in windows 1 and 3 exfiltrates 2q bits and is never caught. -/
theorem observable_schedule_exfil (q : ℕ) (hq : 0 < q) :
    let c : ℕ → ℝ := fun i => if i = 0 ∨ i = 2 then 1 else 0
    (capped q [0, q, 0, q]).sum = 2 * q ∧ survive c (capped q [0, q, 0, q]) 0 = 1 := by
  refine ⟨by simp [capped]; ring, ?_⟩
  simp [capped, survive, hq]

/-! ## 4. Numbers and partial exfiltration -/

/-- **Datacenter instance**: 100 GB (8·10^11 bits) through a 1 GB (8·10^9 bits) per-window quota needs 100 traffic
windows; with p·r = 0.05 the attacker completes before a catch with probability ≤ 0.95^100 < 0.006. -/
theorem datacenter_example (c : ℕ → ℝ) (hc : ∀ i, (0.05 : ℝ) ≤ c i ∧ c i ≤ 1) (b : List ℕ)
    (hS : 800000000000 ≤ (capped 8000000000 b).sum) :
    ceilDiv 800000000000 8000000000 = 100 ∧ survive c (capped 8000000000 b) 0 ≤ 0.006 := by
  have h100 : ceilDiv 800000000000 8000000000 = 100 := by norm_num [ceilDiv]
  refine ⟨h100, ?_⟩
  have h := sc07_plan_bound 800000000000 8000000000 (by norm_num) c 0.05 hc (by norm_num) (by norm_num) b hS
  rw [h100] at h
  refine h.trans ?_
  norm_num

theorem expLeak_nonneg (c : ℕ → ℝ) (hc : ∀ i, c i ≤ 1) (b : List ℕ) (i : ℕ) : 0 ≤ expLeak c b i := by
  induction b generalizing i with
  | nil => simp [expLeak]
  | cons x xs ih =>
    simp only [expLeak]
    have := ih (i + 1)
    have : 0 ≤ (if 0 < x then 1 - c i else 1) := by split_ifs <;> linarith [hc i]
    positivity

/-- **Partial exfiltration.** For every quota-capped plan of any length, the expected number of bits that leave
before the catch is ≤ q/(p·r). -/
theorem expected_leak_le (q : ℕ) (c : ℕ → ℝ) (pr : ℝ) (hc : ∀ i, pr ≤ c i ∧ c i ≤ 1) (hpr : 0 < pr) (b : List ℕ) :
    expLeak c (capped q b) 0 ≤ q / pr := by
  suffices ∀ (l : List ℕ), (∀ x ∈ l, x ≤ q) → ∀ i, expLeak c l i ≤ q / pr from this _ (capped_le q b) 0
  intro l hl
  induction l with
  | nil => intro i; simp only [expLeak]; positivity
  | cons x xs ih =>
    intro i
    have hx : (x : ℝ) ≤ q := by exact_mod_cast hl x List.mem_cons_self
    have ih' := ih (fun y hy => hl y (List.mem_cons_of_mem x hy)) (i + 1)
    have hE := expLeak_nonneg c (fun j => (hc j).2) xs (i + 1)
    simp only [expLeak]
    split_ifs with h
    · have h1 : 1 - c i ≤ 1 - pr := by linarith [(hc i).1]
      have h0 : 0 ≤ 1 - c i := by linarith [(hc i).2]
      have : (1 - c i) * expLeak c xs (i + 1) ≤ (1 - pr) * (q / pr) :=
        mul_le_mul h1 ih' hE (by linarith [(hc i).2, (hc i).1])
      have heq : (q : ℝ) + (1 - pr) * (q / pr) = q / pr := by field_simp; ring
      linarith
    · have hx0 : x = 0 := by omega
      subst hx0
      simp only [Nat.cast_zero, zero_add, one_mul]
      exact ih'

end ControlStack.SC07Exfil

#print axioms ControlStack.SC07Exfil.windows_needed
#print axioms ControlStack.SC07Exfil.sc07_plan_bound
#print axioms ControlStack.SC07Exfil.sc07_mixed
#print axioms ControlStack.SC07Exfil.sc07_fixed_budget
#print axioms ControlStack.SC07Exfil.no_quota_one_window
#print axioms ControlStack.SC07Exfil.observable_schedule_exfil
#print axioms ControlStack.SC07Exfil.datacenter_example
#print axioms ControlStack.SC07Exfil.expected_leak_le
