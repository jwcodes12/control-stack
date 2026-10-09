/-
F6: a concrete round kernel for a monitor ensemble. It closes the gap noted in `MonitorEnsemble`: (4) there took the
per-history escape bound as a premise; here it is DERIVED from a kernel.

The kernel `ensK` has, per round:
- hidden state y = (blind-spot flag, miss pattern of the m monitors), drawn from the `mixture` law. Its parameters
  (b, ν, q) may depend on the visible history (conditioning on everything seen so far);
- the attacker's attack bit a ~ σ(visible history);
- catch iff the round is reserved (audited), the attacker attacks, and at least one monitor flags.

Results:
- `ensK_premises`: the kernel is a sub-distribution, and its per-history non-catch mass is
  ≤ σ(a) · (β + Π (1 − r_j)) on attacked reserved rounds and ≤ σ(a) otherwise. These are exactly the premises of
  `MonitorEnsemble.ensemble_adaptive`, with e = β + Π(1 − r_j). Per-history conditions: b ≤ β, ν a distribution,
  q_j ≤ 1 − r_j.
- `ensK_adaptive`: end to end, every adaptive attacker against reserved hidden audits inspected by this ensemble
  escapes k attack rounds with probability ≤ hypMiss N Bh k (1 − (β + Π (1 − r_j))). Adversary class
  ADAPTIVE_FEEDBACK.
- `ensK_example`: 3 monitors at recall 3/5 outside a blind spot of weight ≤ 1/20 give hypMiss N Bh k (443/500).

Limits:
- The blind-spot weight and recalls must hold for every history (measurement premises).
- The monitors inspect only reserved rounds.
- The attacker sees only its own actions and catch flags. Monitors that collude with the attacker are excluded by
  the mixture's form (`MonitorCollusion`).
- No novelty is claimed.
-/
import Mathlib.Tactic
import ControlStack.Families.F6.MonitorEnsemble

namespace ControlStack.EnsembleKernel

open Finset ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
  ControlStack.MonitorEnsemble

variable {N m : ℕ}

/-- hidden per-round state: (blind spot?, miss pattern) -/
abbrev Hid (m : ℕ) := Bool × (Fin m → Bool)

/-- the ensemble round kernel -/
noncomputable def ensK (σ : List (AOut Unit) → Bool → ℝ) (b : List (AOut Unit) → ℝ)
    (ν : List (AOut Unit) → (Fin m → Bool) → ℝ) (q : List (AOut Unit) → Fin m → ℝ) :
    Finset (Fin N) → List (Hid m × AOut Unit) → Hid m × AOut Unit → ℝ :=
  fun S h z =>
    σ (h.map Prod.snd) z.2.1 * mixture (b (h.map Prod.snd)) (ν (h.map Prod.snd)) (q (h.map Prod.snd)) z.1 *
      (if z.2.2.2 = (z.2.1 && decide (memN S (h.map Prod.snd).length) && !escapes z.1) then 1 else 0)

theorem mixture_nonneg (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (ν : (Fin m → Bool) → ℝ) (hν0 : ∀ x, 0 ≤ ν x)
    (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1) (y : Hid m) : 0 ≤ mixture b ν q y := by
  unfold mixture
  split_ifs
  · exact mul_nonneg hb0 (hν0 _)
  · exact mul_nonneg (by linarith) (indepW_nonneg q hq _)

theorem mixture_total (b : ℝ) (ν : (Fin m → Bool) → ℝ) (hν1 : ∑ x, ν x = 1) (q : Fin m → ℝ) :
    ∑ y : Hid m, mixture b ν q y = 1 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [mixture, if_true, Bool.false_eq_true, if_false]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hν1, indep_dist]
  ring

/-- the per-history parameters: blind-spot weight ≤ β, ν a distribution, miss rates q_j ∈ [0, 1 − r_j] -/
structure Params (β : ℝ) (r : Fin m → ℝ) (b : List (AOut Unit) → ℝ) (ν : List (AOut Unit) → (Fin m → Bool) → ℝ)
    (q : List (AOut Unit) → Fin m → ℝ) : Prop where
  b0 : ∀ g, 0 ≤ b g
  bβ : ∀ g, b g ≤ β
  b1 : ∀ g, b g ≤ 1
  ν0 : ∀ g x, 0 ≤ ν g x
  ν1 : ∀ g, ∑ x, ν g x = 1
  q0 : ∀ g j, 0 ≤ q g j
  qr : ∀ g j, q g j ≤ 1 - r j
  q1 : ∀ g j, q g j ≤ 1

/-- **The kernel satisfies `ensemble_adaptive`'s premises** with e = β + Π (1 − r_j). -/
theorem ensK_premises (β : ℝ) (r : Fin m → ℝ) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (b : List (AOut Unit) → ℝ) (ν : List (AOut Unit) → (Fin m → Bool) → ℝ) (q : List (AOut Unit) → Fin m → ℝ)
    (hp : Params β r b ν q) (S : Finset (Fin N)) (h : List (Hid m × AOut Unit)) :
    (∀ z, 0 ≤ ensK σ b ν q S h z) ∧ (∑ z, ensK σ b ν q S h z ≤ 1) ∧
    ∀ a : Bool, ∑ y, ensK σ b ν q S h (y, (a, (), false)) ≤
      σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then β + ∏ j, (1 - r j) else 1) := by
  set g := h.map Prod.snd
  have hq : ∀ j, 0 ≤ q g j ∧ q g j ≤ 1 := fun j => ⟨hp.q0 g j, hp.q1 g j⟩
  have hM0 := mixture_nonneg (b g) (hp.b0 g) (hp.b1 g) (ν g) (hp.ν0 g) (q g) hq
  have hM1 := mixture_total (b g) (ν g) (hp.ν1 g) (q g)
  refine ⟨fun z => ?_, ?_, fun a => ?_⟩
  · unfold ensK
    exact mul_nonneg (mul_nonneg ((hσ _).1 _) (hM0 _)) (by split_ifs <;> norm_num)
  · -- Σ over (y, (a, (), c)): the catch flag is determined, so the mass is Σ_a σ a · Σ_y M y = 1
    have e : ∑ z, ensK σ b ν q S h z = ∑ y : Hid m, ∑ a : Bool, ∑ c : Bool, ensK σ b ν q S h (y, (a, (), c)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro y _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro a _
      rw [Fintype.sum_prod_type]; simp
    rw [e]
    have inner : ∀ y : Hid m, ∑ a : Bool, ∑ c : Bool, ensK σ b ν q S h (y, (a, (), c)) =
        mixture (b g) (ν g) (q g) y := by
      intro y
      have hσ1 := (hσ g).2
      rw [Fintype.sum_bool] at hσ1
      simp only [ensK, Fintype.sum_bool]
      cases hy : escapes y <;> cases hmS : decide (memN S g.length) <;> simp <;> linear_combination
        (mixture (b g) (ν g) (q g) y) * hσ1
    simp_rw [inner]
    rw [hM1]
  · have hesc := blind_spot_escape (m := m) β (b g) (hp.b0 g) (hp.bβ g) (ν g) (hp.ν0 g) (hp.ν1 g) (q g) r
      (hp.q0 g) (hp.qr g)
    have hσa := (hσ g).1 a
    by_cases hc : memN S g.length ∧ a = true
    · rw [if_pos hc]
      obtain ⟨hmS, rfl⟩ := hc
      have e : ∑ y, ensK σ b ν q S h (y, (true, (), false)) = σ g true * P (mixture (b g) (ν g) (q g)) escapes := by
        unfold ensK P
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro y _
        simp only [g] at hmS
        simp only [decide_eq_true hmS, Bool.true_and]
        cases escapes y <;> simp [g]
      rw [e]
      exact mul_le_mul_of_nonneg_left hesc hσa
    · rw [if_neg hc, mul_one]
      have e : ∑ y, ensK σ b ν q S h (y, (a, (), false)) = σ g a * ∑ y, mixture (b g) (ν g) (q g) y := by
        unfold ensK
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro y _
        have : (false = (a && decide (memN S g.length) && !escapes y)) := by
          by_cases hmS : memN S g.length
          · have ha : a = false := by
              cases a
              · rfl
              · exact absurd ⟨hmS, rfl⟩ hc
            subst ha; simp
          · simp [hmS]
        rw [if_pos this]; ring
      rw [e, hM1, mul_one]

/-- **End to end.** Every adaptive attacker against reserved hidden audits inspected by this ensemble escapes k
attack rounds with probability ≤ hypMiss N Bh k (1 − (β + Π (1 − r_j))). -/
theorem ensK_adaptive (k Bh : ℕ) (hB : Bh ≤ N) (β : ℝ) (r : Fin m → ℝ) (hβ0 : 0 ≤ β)
    (hr : ∀ j, 0 ≤ r j ∧ r j ≤ 1) (he1 : β + ∏ j, (1 - r j) ≤ 1)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (b : List (AOut Unit) → ℝ) (ν : List (AOut Unit) → (Fin m → Bool) → ℝ) (q : List (AOut Unit) → Fin m → ℝ)
    (hp : Params β r b ν q) :
    ∑ S : Finset (Fin N), pU N Bh S * val (ensK σ b ν q S) (recallSucc (N := N) k) N [] ≤
      hypMiss N Bh k (1 - (β + ∏ j, (1 - r j))) := by
  have he0 : 0 ≤ β + ∏ j, (1 - r j) :=
    add_nonneg hβ0 (Finset.prod_nonneg fun j _ => by linarith [(hr j).2])
  exact ensemble_adaptive k Bh hB _ he0 he1 (ensK σ b ν q) σ hσ
    (fun S _ h z => (ensK_premises β r σ hσ b ν q hp S h).1 z)
    (fun S _ h => (ensK_premises β r σ hσ b ν q hp S h).2.1)
    (fun S _ h a => (ensK_premises β r σ hσ b ν q hp S h).2.2 a)

/-- **Numbers.** 3 monitors at recall 3/5 outside a blind spot of weight ≤ 1/20: the end-to-end bound is
hypMiss N Bh k (443/500), i.e. per-round ensemble recall 0.886. -/
theorem ensK_example (k Bh : ℕ) (hB : Bh ≤ N) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (b : List (AOut Unit) → ℝ) (ν : List (AOut Unit) → (Fin 3 → Bool) → ℝ) (q : List (AOut Unit) → Fin 3 → ℝ)
    (hp : Params (1 / 20) (fun _ => 3 / 5) b ν q) :
    ∑ S : Finset (Fin N), pU N Bh S * val (ensK σ b ν q S) (recallSucc (N := N) k) N [] ≤
      hypMiss N Bh k (443 / 500) := by
  have h := ensK_adaptive k Bh hB (1 / 20) (fun _ => 3 / 5) (by norm_num) (fun _ => by norm_num)
    (by simp; norm_num) σ hσ b ν q hp
  have e : (1 : ℝ) - (1 / 20 + ∏ _j : Fin 3, (1 - 3 / 5)) = 443 / 500 := by
    simp; norm_num
  rwa [e] at h

end ControlStack.EnsembleKernel

#print axioms ControlStack.EnsembleKernel.ensK_premises
#print axioms ControlStack.EnsembleKernel.ensK_adaptive
#print axioms ControlStack.EnsembleKernel.ensK_example
