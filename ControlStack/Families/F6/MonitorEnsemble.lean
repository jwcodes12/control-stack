/-
F6: ensembles of monitors, composed honestly. Reviews flagged that multiplying miss rates is unsound without
independence (`Necessity.shared_score_product_unsound`, `Cert.product_needs_independence`), and that untrusted
monitors can collude (`MonitorCollusion`).

Setting: one attack round, given its history. Monitor j misses the attack with probability ≤ 1 − r_j (per-history
recall r_j). The round ESCAPES iff all monitors miss.

Results:
- (1) No independence premise:
  - `escape_le_each` / `escape_le_recall`: the escape probability is ≤ 1 − r_j for every j, i.e. ≤ the best single
    monitor's miss rate min_j (1 − r_j);
  - `correlated_tight`: tight. With perfectly correlated misses, three monitors escape exactly as often as one.
- (2) `indep_escape` (premise: misses independent given the history; the law IS the product law, `indepW`): the
  escape probability equals Π_j q_j ≤ Π_j (1 − r_j). `indep_dist` checks the product law is a distribution.
- (3) Shared blind spot (`mixture`). With probability b ≤ β the round falls in a common-cause blind spot where the
  monitors' misses are ARBITRARY (any joint law ν). Otherwise misses are independent with rates q_j ≤ 1 − r_j.
  - `mixture_escape_eq`: escape = b · ν(all miss) + (1 − b) · Π q_j;
  - `blind_spot_escape`: escape ≤ β + Π_j (1 − r_j), a robust bound that degrades gracefully in β;
  - `beta_necessary`: a blind spot where every monitor misses pushes escape above the independent product Π q_j.
    The product bound alone is unsound and the β term is needed.
- (4) `ensemble_adaptive`: an ensemble whose per-history escape on audited attack rounds is ≤ e = β + Π(1 − r_j)
  acts as ONE monitor with recall r_ens = 1 − e in `ReservedRecall.adaptive_recall_bound`. Every adaptive attacker
  against reserved hidden audits escapes k attack rounds with probability ≤ hypMiss N Bh k r_ens.
  `ensemble_example`: 3 monitors at r = 0.6 with β = 0.05:
  - escape ≤ 0.114 per audited attack round, so r_ens ≥ 0.886;
  - with N = 100 and 10 reserved audits, expected attack rounds before the first catch ≤ 10.3 (one monitor at
    0.6: ≤ 15.67);
  - the β term alone (0.05) is about 44% of the per-round escape bound (0.05 of 0.114).

Limits:
- Estimating β (the probability of a shared blind spot, given the history) is a MEASUREMENT premise.
- Population-average agreement between monitors does not bound per-history correlation.
- Untrusted monitors that collude, or that share a seed or codebook with the attacker, violate the independence
  premise entirely (`MonitorCollusion`): in that case only (1) applies.
- The recalls r_j are recalls outside the blind spot.
- Classical probability; no novelty is claimed.
-/
import Mathlib.Tactic
import ControlStack.Families.F6.ReservedRecall
import ControlStack.Families.F6.DamageBound

namespace ControlStack.MonitorEnsemble

open Finset

/-- probability of an event under weights μ -/
noncomputable def P {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (E : Ω → Bool) : ℝ := ∑ ω, if E ω then μ ω else 0

theorem P_mono {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (E F : Ω → Bool)
    (h : ∀ ω, E ω = true → F ω = true) : P μ E ≤ P μ F := by
  unfold P
  apply Finset.sum_le_sum; intro ω _
  by_cases hE : E ω = true
  · rw [if_pos hE, if_pos (h ω hE)]
  · rw [if_neg hE]; split_ifs; exact hμ ω; exact le_rfl

/-- all m monitors miss -/
def allMiss {Ω : Type} {m : ℕ} (miss : Fin m → Ω → Bool) (ω : Ω) : Bool := decide (∀ j, miss j ω = true)

/-! ## (1) No independence: only the best single monitor -/

/-- **Escape ≤ any single monitor's miss probability**, for any joint law of the misses. -/
theorem escape_le_each {Ω : Type} [Fintype Ω] {m : ℕ} (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (miss : Fin m → Ω → Bool) (j : Fin m) : P μ (allMiss miss) ≤ P μ (miss j) :=
  P_mono μ hμ _ _ fun ω h => by simp only [allMiss, decide_eq_true_eq] at h; exact h j

/-- **...so escape ≤ min_j (1 − r_j)**: with per-monitor recalls r_j, escape ≤ 1 − r_j for every j. -/
theorem escape_le_recall {Ω : Type} [Fintype Ω] {m : ℕ} (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (miss : Fin m → Ω → Bool) (r : Fin m → ℝ) (hr : ∀ j, P μ (miss j) ≤ 1 - r j) :
    ∀ j, P μ (allMiss miss) ≤ 1 - r j :=
  fun j => (escape_le_each μ hμ miss j).trans (hr j)

/-- **Tightness.** Perfectly correlated misses (all three monitors miss on the same coin, probability q): the
ensemble escapes exactly as often as one monitor. -/
theorem correlated_tight (q : ℝ) :
    P (fun ω : Bool => if ω then q else 1 - q) (allMiss (fun (_ : Fin 3) ω => ω)) = q ∧
    ∀ j : Fin 3, P (fun ω : Bool => if ω then q else 1 - q) ((fun (_ : Fin 3) ω => ω) j) = q := by
  refine ⟨?_, fun j => ?_⟩ <;> simp [P, allMiss]

/-! ## (2) Independent misses -/

/-- the product law of independent misses with rates q_j -/
def indepW {m : ℕ} (q : Fin m → ℝ) (x : Fin m → Bool) : ℝ := ∏ j, (if x j then q j else 1 - q j)

/-- the product law is a probability distribution -/
theorem indep_dist {m : ℕ} (q : Fin m → ℝ) : ∑ x, indepW q x = 1 := by
  unfold indepW
  rw [← Fintype.prod_sum (fun j (b : Bool) => if b then q j else 1 - q j)]
  simp

theorem indepW_nonneg {m : ℕ} (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1) (x : Fin m → Bool) :
    0 ≤ indepW q x := by
  unfold indepW
  apply Finset.prod_nonneg; intro j _
  split_ifs <;> linarith [hq j]

/-- **Independent misses: escape = Π q_j ≤ Π (1 − r_j).** -/
theorem indep_escape {m : ℕ} (q r : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j) (hqr : ∀ j, q j ≤ 1 - r j) :
    P (indepW q) (allMiss (fun j x => x j)) = ∏ j, q j ∧ ∏ j, q j ≤ ∏ j, (1 - r j) := by
  refine ⟨?_, Finset.prod_le_prod₀ (fun j _ => hq j) (fun j _ => hqr j)⟩
  unfold P
  rw [Finset.sum_eq_single (fun _ => true)]
  · simp [allMiss, indepW]
  · intro x _ hx
    have : ¬ ∀ j, x j = true := fun h => hx (funext h)
    simp [allMiss, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## (3) A shared blind spot -/

/-- the mixture law on (blind spot?, miss pattern): with weight b a blind spot with ARBITRARY joint misses ν, with
weight 1 − b independent misses with rates q -/
noncomputable def mixture {m : ℕ} (b : ℝ) (ν : (Fin m → Bool) → ℝ) (q : Fin m → ℝ) : Bool × (Fin m → Bool) → ℝ :=
  fun ω => if ω.1 then b * ν ω.2 else (1 - b) * indepW q ω.2

def escapes {m : ℕ} (ω : Bool × (Fin m → Bool)) : Bool := decide (∀ j, ω.2 j = true)

/-- **The mixture's escape probability.** -/
theorem mixture_escape_eq {m : ℕ} (b : ℝ) (ν : (Fin m → Bool) → ℝ) (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j) :
    P (mixture b ν q) escapes = b * P ν (allMiss (fun j x => x j)) + (1 - b) * ∏ j, q j := by
  have hind := (indep_escape q (fun j => 1 - q j) hq (fun j => by linarith)).1
  unfold P at hind ⊢
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [mixture, escapes, allMiss, if_true, Bool.false_eq_true, if_false] at hind ⊢
  rw [← hind, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro x _; by_cases hx : ∀ j, x j = true <;> simp [hx]
  · apply Finset.sum_congr rfl; intro x _; by_cases hx : ∀ j, x j = true <;> simp [hx]

/-- **Shared blind spot: escape ≤ β + Π (1 − r_j).** For any blind-spot law ν (any correlation inside the blind
spot), blind-spot weight b ≤ β, and independent misses q_j ≤ 1 − r_j outside it. -/
theorem blind_spot_escape {m : ℕ} (β b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ β)
    (ν : (Fin m → Bool) → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (q r : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j) (hqr : ∀ j, q j ≤ 1 - r j) :
    P (mixture b ν q) escapes ≤ β + ∏ j, (1 - r j) := by
  rw [mixture_escape_eq b ν q hq]
  have hνall : P ν (allMiss (fun j x => x j)) ≤ 1 := by
    rw [← hν1]; unfold P; apply Finset.sum_le_sum; intro x _; split_ifs; exact le_rfl; exact hν0 x
  have hprod := (indep_escape q r hq hqr).2
  have hp0 : 0 ≤ ∏ j, q j := Finset.prod_nonneg fun j _ => hq j
  have h1 : b * P ν (allMiss (fun j x => x j)) ≤ β := by nlinarith
  have h2 : (1 - b) * ∏ j, q j ≤ ∏ j, q j := by nlinarith
  linarith

/-- **β is necessary.** Three monitors missing independently at rate 2/5 escape with probability 8/125. A blind
spot of weight 1/20 in which all three miss raises escape to 1/20 + (19/20)(8/125) = 1/20 + 38/625, above the
product 8/125. The bound β + Π = 1/20 + 8/125 still holds. -/
theorem beta_necessary :
    P (mixture (1 / 20) (fun x => if x = (fun _ => true) then 1 else 0) (fun (_ : Fin 3) => 2 / 5)) escapes =
      1 / 20 + 38 / 625 ∧ (8 : ℝ) / 125 < 1 / 20 + 38 / 625 ∧ (1 : ℝ) / 20 + 38 / 625 ≤ 1 / 20 + 8 / 125 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  rw [mixture_escape_eq _ _ _ (fun _ => by norm_num)]
  have hall : P (fun x : Fin 3 → Bool => if x = (fun _ => true) then (1 : ℝ) else 0) (allMiss (fun j x => x j)) = 1 := by
    unfold P
    rw [Finset.sum_eq_single (fun _ => true)]
    · simp [allMiss]
    · intro x _ hx; simp [hx]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hall]
  simp
  norm_num

/-! ## (4) The ensemble as one monitor against adaptive attackers -/

open ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall

/-- **Ensemble against adaptive attackers.** If, given the history, the ensemble lets an attack in a reserved
(audited) round through with probability ≤ e (e.g. e = β + Π (1 − r_j) by `blind_spot_escape`), the ensemble is a
single monitor with recall 1 − e: every adaptive attacker escapes k attack rounds with probability
≤ hypMiss N Bh k (1 − e). Adversary class: ADAPTIVE_FEEDBACK. -/
theorem ensemble_adaptive {N : ℕ} {Y : Type} [Fintype Y] (k Bh : ℕ) (hB : Bh ≤ N) (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z)
    (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1)
    (hens : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool),
      ∑ y, K S h (y, (a, (), false)) ≤
        σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then e else 1)) :
    ∑ S : Finset (Fin N), pU N Bh S * val (K S) (recallSucc (N := N) k) N [] ≤ hypMiss N Bh k (1 - e) := by
  refine adaptive_recall_bound k Bh hB (1 - e) (by linarith) (by linarith) K σ hσ hK0 hK1 ?_
  intro S hS h a
  rw [sub_sub_cancel]
  exact hens S hS h a

/-- **Numbers.** Three monitors at recall 0.6 with a shared blind spot of weight ≤ 0.05:
- per audited attack round, escape ≤ 0.05 + 0.4³ = 57/500 = 0.114, so r_ens ≥ 443/500 = 0.886;
- with N = 100 and 10 reserved hidden audits, expected attack rounds before the first catch ≤ 10.3, against
  ≤ 47/3 ≈ 15.67 for one monitor at 0.6. -/
theorem ensemble_example :
    (1 : ℝ) / 20 + ∏ _j : Fin 3, (1 - 3 / 5 : ℝ) = 57 / 500 ∧
    ∑ j ∈ range 100, hypMiss 100 10 (j + 1) (1 - 57 / 500) ≤ 103 / 10 ∧
    ∑ j ∈ range 100, hypMiss 100 10 (j + 1) (3 / 5) ≤ 47 / 3 := by
  refine ⟨by simp; norm_num, ?_, ?_⟩
  · refine (DamageBound.expected_geom (N := 100) 10 (by norm_num) (by norm_num) _ (by norm_num) (by norm_num)).trans ?_
    norm_num
  · refine (DamageBound.expected_geom (N := 100) 10 (by norm_num) (by norm_num) _ (by norm_num) (by norm_num)).trans ?_
    norm_num

end ControlStack.MonitorEnsemble

#print axioms ControlStack.MonitorEnsemble.escape_le_recall
#print axioms ControlStack.MonitorEnsemble.correlated_tight
#print axioms ControlStack.MonitorEnsemble.indep_dist
#print axioms ControlStack.MonitorEnsemble.indep_escape
#print axioms ControlStack.MonitorEnsemble.mixture_escape_eq
#print axioms ControlStack.MonitorEnsemble.blind_spot_escape
#print axioms ControlStack.MonitorEnsemble.beta_necessary
#print axioms ControlStack.MonitorEnsemble.ensemble_adaptive
#print axioms ControlStack.MonitorEnsemble.ensemble_example
