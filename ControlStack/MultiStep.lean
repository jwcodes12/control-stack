/-
Multi-step attacks against a (possibly stateful) monitor: conditional hazards compound, marginal rates do not.

Model. A catastrophe needs k bad steps. Histories are lists of past actions h : List A (A finite). Red's policy
π : List A → A → ℝ is a probability distribution over the next action for every history (adaptive, history-dependent).
A possibly stateful monitor catches the step with action a after history h with probability κ h a ∈ [0,1]. The
probability that Red completes k further steps uncaught from history h is
  V 0 h = 1,   V (k+1) h = Σ_a π h a · (1 − κ h a) · V k (h ++ [a]).

Results.
1. `survival_bounds` / `survival_le`: if the CONDITIONAL catch rate is uniformly ≥ c (κ h a ≥ c for every history h
   and action a), then V k h ≤ (1 − c)^k for every Red policy and history. `survival_const` shows this is tight
   (κ ≡ c gives exactly (1 − c)^k).
2. `correlated_nogo`: marginal catch rates are not enough. A seeded monitor draws θ ∈ Bool once, P(θ = true) = c; if
   θ = true it catches every step (κ ≡ 1), otherwise none (κ ≡ 0). Its per-step marginal catch rate is c at every
   step and history (`seeded_marginal`), but its survival over k ≥ 1 steps is 1 − c (`seeded_survival`), strictly
   above (1 − c)^k for 0 < c < 1 and k ≥ 2. The conditional catch rate given survival of the first step is 0.
3. `survival_avg`: the positive result in between. For a finite seed space Θ with prior ρ and seed-indexed monitors
   κ θ, carry the unnormalised posterior weight w θ = ρ θ · Π (1 − κ θ ·) along the history. If at every reachable
   (history, weight) the posterior-averaged catch rate is ≥ c (Σ_θ w θ κ θ h a ≥ c · Σ_θ w θ), the seed-averaged
   survival Σ_θ ρ θ · V^{κ θ} k [] is ≤ (1 − c)^k · Σ_θ ρ θ. The seeded monitor of (2) violates this hypothesis.
4. `survival_example`: c = 1/10, k = 5 gives survival ≤ 0.59049.

Assumptions carried by the deployment, not by these theorems: the catch events are as modelled (catching any step
ends the attack); κ really is a conditional rate given the full history (and, in (3), given the posterior over the
monitor's hidden state); Red gains nothing from steps that are not part of the k-step attack.
-/
import Mathlib.Tactic

namespace ControlStack.MultiStep

open Finset

/-- `p` is a probability distribution on a finite type -/
def IsDist {A : Type} [Fintype A] (p : A → ℝ) : Prop := (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- Red policy: a distribution over next actions for every history -/
def IsPolicy {A : Type} [Fintype A] (π : List A → A → ℝ) : Prop := ∀ h, IsDist (π h)

/-- monitor: catch probabilities in [0,1] for every history and action -/
def IsMonitor {A : Type} (κ : List A → A → ℝ) : Prop := ∀ h a, 0 ≤ κ h a ∧ κ h a ≤ 1

/-- probability of completing `k` further steps uncaught from history `h` -/
noncomputable def V {A : Type} [Fintype A] (π : List A → A → ℝ) (κ : List A → A → ℝ) : ℕ → List A → ℝ
  | 0, _ => 1
  | k + 1, h => ∑ a, π h a * (1 - κ h a) * V π κ k (h ++ [a])

@[simp] theorem V_zero {A : Type} [Fintype A] (π κ : List A → A → ℝ) (h : List A) : V π κ 0 h = 1 := rfl

theorem V_succ {A : Type} [Fintype A] (π κ : List A → A → ℝ) (k : ℕ) (h : List A) :
    V π κ (k + 1) h = ∑ a, π h a * (1 - κ h a) * V π κ k (h ++ [a]) := rfl

/-- survival is a probability: 0 ≤ V k h ≤ 1 -/
theorem survival_bounds {A : Type} [Fintype A] (π κ : List A → A → ℝ) (hπ : IsPolicy π) (hκ : IsMonitor κ)
    (k : ℕ) (h : List A) : 0 ≤ V π κ k h ∧ V π κ k h ≤ 1 := by
  induction k generalizing h with
  | zero => simp
  | succ k ih =>
    rw [V_succ]
    constructor
    · exact Finset.sum_nonneg fun a _ =>
        mul_nonneg (mul_nonneg ((hπ h).1 a) (by linarith [(hκ h a).1, (hκ h a).2])) (ih _).1
    · calc ∑ a, π h a * (1 - κ h a) * V π κ k (h ++ [a]) ≤ ∑ a, π h a := by
            apply Finset.sum_le_sum; intro a _
            have h1 : (1 - κ h a) * V π κ k (h ++ [a]) ≤ 1 := by
              have := (ih (h ++ [a]))
              nlinarith [(hκ h a).1, (hκ h a).2]
            have := mul_le_mul_of_nonneg_left h1 ((hπ h).1 a)
            linarith
        _ = 1 := (hπ h).2

/-- Conditional-hazard bound: a uniform conditional catch rate c gives survival ≤ (1 − c)^k against every adaptive
Red policy, from every history. -/
theorem survival_le {A : Type} [Fintype A] (π κ : List A → A → ℝ) (hπ : IsPolicy π) (hκ : IsMonitor κ)
    (c : ℝ) (hc1 : c ≤ 1) (hcκ : ∀ h a, c ≤ κ h a) (k : ℕ) (h : List A) :
    V π κ k h ≤ (1 - c) ^ k := by
  induction k generalizing h with
  | zero => simp
  | succ k ih =>
    rw [V_succ]
    calc ∑ a, π h a * (1 - κ h a) * V π κ k (h ++ [a]) ≤ ∑ a, π h a * ((1 - c) ^ (k + 1)) := by
          apply Finset.sum_le_sum; intro a _
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ ((hπ h).1 a)
          have hV := survival_bounds π κ hπ hκ k (h ++ [a])
          have e1 : (1 - κ h a) * V π κ k (h ++ [a]) ≤ (1 - c) * V π κ k (h ++ [a]) :=
            mul_le_mul_of_nonneg_right (by linarith [hcκ h a]) hV.1
          have e2 : (1 - c) * V π κ k (h ++ [a]) ≤ (1 - c) * (1 - c) ^ k :=
            mul_le_mul_of_nonneg_left (ih _) (by linarith)
          rw [pow_succ]; linarith
      _ = (1 - c) ^ (k + 1) := by rw [← Finset.sum_mul, (hπ h).2, one_mul]

/-- Tightness: the memoryless monitor κ ≡ c gives survival exactly (1 − c)^k. -/
theorem survival_const {A : Type} [Fintype A] (π : List A → A → ℝ) (hπ : IsPolicy π) (c : ℝ) (k : ℕ)
    (h : List A) : V π (fun _ _ => c) k h = (1 - c) ^ k := by
  induction k generalizing h with
  | zero => simp
  | succ k ih =>
    rw [V_succ]
    simp only [ih]
    rw [← Finset.sum_mul, ← Finset.sum_mul, (hπ h).2, pow_succ]; ring

/-- the monitor that never catches: survival 1 -/
theorem V_never {A : Type} [Fintype A] (π : List A → A → ℝ) (hπ : IsPolicy π) (k : ℕ) (h : List A) :
    V π (fun _ _ => 0) k h = 1 := by
  simpa using survival_const π hπ 0 k h

/-- the monitor that always catches: survival 0 for k ≥ 1 -/
theorem V_always {A : Type} [Fintype A] (π : List A → A → ℝ) (k : ℕ) (h : List A) :
    V π (fun _ _ => 1) (k + 1) h = 0 := by
  rw [V_succ]; simp

/-- the seeded monitor for seed θ: catch everything if θ = true, nothing if θ = false -/
def seededκ {A : Type} (θ : Bool) : List A → A → ℝ := fun _ _ => if θ then 1 else 0

/-- survival against the seeded monitor, θ ~ Bernoulli(c) drawn once:
c · (survival given θ = true) + (1 − c) · (survival given θ = false) -/
noncomputable def seededSurvival {A : Type} [Fintype A] (c : ℝ) (π : List A → A → ℝ) (k : ℕ) (h : List A) : ℝ :=
  c * V π (seededκ true) k h + (1 - c) * V π (seededκ false) k h

/-- per-step marginal catch rate of the seeded monitor (averaged over the seed) -/
noncomputable def seededMarginal {A : Type} (c : ℝ) (h : List A) (a : A) : ℝ :=
  c * seededκ true h a + (1 - c) * seededκ false h a

theorem seeded_marginal {A : Type} (c : ℝ) (h : List A) (a : A) : seededMarginal c h a = c := by
  simp [seededMarginal, seededκ]

/-- survival over k ≥ 1 steps against the seeded monitor is c · 0 + (1 − c) · 1 = 1 − c -/
theorem seeded_survival {A : Type} [Fintype A] (c : ℝ) (π : List A → A → ℝ) (hπ : IsPolicy π) (k : ℕ)
    (hk : 1 ≤ k) (h : List A) :
    V π (seededκ true) k h = 0 ∧ V π (seededκ false) k h = 1 ∧ seededSurvival c π k h = 1 - c := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : V π (seededκ true) (j + 1) h = 0 := V_always π j h
  have h0 : V π (seededκ false) (j + 1) h = 1 := V_never π hπ (j + 1) h
  refine ⟨h1, h0, ?_⟩
  rw [seededSurvival, h1, h0]; ring

/-- the product bound fails for marginal rates: (1 − c)^k < 1 − c for 0 < c < 1, k ≥ 2 -/
theorem pow_lt_self_of_two_le (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (k : ℕ) (hk : 2 ≤ k) :
    (1 - c) ^ k < 1 - c := by
  have h0 : 0 < 1 - c := by linarith
  have h1 : 1 - c < 1 := by linarith
  calc (1 - c) ^ k < (1 - c) ^ 1 := pow_lt_pow_right_of_lt_one₀ h0 h1 (by omega)
    _ = 1 - c := pow_one _

/-- Correlated no-go: the seeded monitor has per-step marginal catch rate c at every step, yet against every Red
policy its k-step survival is 1 − c, strictly above the product bound (1 − c)^k (which the memoryless monitor with
the same marginal rate attains). -/
theorem correlated_nogo {A : Type} [Fintype A] (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (π : List A → A → ℝ) (hπ : IsPolicy π) (k : ℕ) (hk : 2 ≤ k) (h : List A) :
    (∀ (h' : List A) (a : A), seededMarginal c h' a = c) ∧
    seededSurvival c π k h = 1 - c ∧
    V π (fun _ _ => c) k h = (1 - c) ^ k ∧
    (1 - c) ^ k < seededSurvival c π k h := by
  have hs := (seeded_survival c π hπ k (by omega) h).2.2
  refine ⟨fun h' a => seeded_marginal c h' a, hs, survival_const π hπ c k h, ?_⟩
  rw [hs]; exact pow_lt_self_of_two_le c hc0 hc1 k hk

/-! ### Posterior-averaged hazard (seed-indexed monitors) -/

/-- seed-averaged survival carrying the unnormalised posterior weight `w` on seeds -/
noncomputable def Vs {A Θ : Type} [Fintype A] [Fintype Θ] (π : List A → A → ℝ) (κ : Θ → List A → A → ℝ) :
    ℕ → List A → (Θ → ℝ) → ℝ
  | 0, _, w => ∑ θ, w θ
  | k + 1, h, w => ∑ a, π h a * Vs π κ k (h ++ [a]) (fun θ => w θ * (1 - κ θ h a))

/-- reachable (history, posterior weight) pairs from prior ρ at the empty history -/
inductive Reachable {A Θ : Type} (ρ : Θ → ℝ) (κ : Θ → List A → A → ℝ) : List A → (Θ → ℝ) → Prop
  | nil : Reachable ρ κ [] ρ
  | snoc {h w} (a : A) : Reachable ρ κ h w → Reachable ρ κ (h ++ [a]) (fun θ => w θ * (1 - κ θ h a))

/-- the weighted value is the seed mixture of the per-seed survival values -/
theorem Vs_eq {A Θ : Type} [Fintype A] [Fintype Θ] (π : List A → A → ℝ) (κ : Θ → List A → A → ℝ)
    (k : ℕ) (h : List A) (w : Θ → ℝ) : Vs π κ k h w = ∑ θ, w θ * V π (κ θ) k h := by
  induction k generalizing h w with
  | zero => simp [Vs]
  | succ k ih =>
    simp only [Vs, ih, V_succ, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro θ _
    apply Finset.sum_congr rfl; intro a _
    ring

theorem reachable_nonneg {A Θ : Type} (ρ : Θ → ℝ) (κ : Θ → List A → A → ℝ) (hρ : ∀ θ, 0 ≤ ρ θ)
    (hκ : ∀ θ, IsMonitor (κ θ)) {h : List A} {w : Θ → ℝ} (hr : Reachable ρ κ h w) : ∀ θ, 0 ≤ w θ := by
  induction hr with
  | nil => exact hρ
  | @snoc h' w' a _ ih =>
    intro θ; exact mul_nonneg (ih θ) (by linarith [(hκ θ h' a).2])

/-- Posterior-averaged hazard bound: if at every reachable (history, posterior weight) the posterior-averaged catch
rate is ≥ c, then the seed-averaged survival is ≤ (1 − c)^k times the prior mass. (No range hypotheses on κ or ρ are
needed: `hpost` already carries them; in the intended use ρ is a prior and each κ θ a monitor, so the weights are
nonnegative posteriors, `reachable_nonneg`.) -/
theorem survival_avg {A Θ : Type} [Fintype A] [Fintype Θ] (π : List A → A → ℝ) (hπ : IsPolicy π)
    (κ : Θ → List A → A → ℝ) (ρ : Θ → ℝ) (c : ℝ) (hc1 : c ≤ 1)
    (hpost : ∀ h w, Reachable ρ κ h w → ∀ a, c * ∑ θ, w θ ≤ ∑ θ, w θ * κ θ h a) (k : ℕ) :
    ∑ θ, ρ θ * V π (κ θ) k [] ≤ (1 - c) ^ k * ∑ θ, ρ θ := by
  rw [← Vs_eq]
  suffices H : ∀ k h w, Reachable ρ κ h w → Vs π κ k h w ≤ (1 - c) ^ k * ∑ θ, w θ from H k [] ρ .nil
  intro k
  induction k with
  | zero => intro h w _; simp [Vs]
  | succ k ih =>
    intro h w hr
    simp only [Vs]
    calc ∑ a, π h a * Vs π κ k (h ++ [a]) (fun θ => w θ * (1 - κ θ h a))
        ≤ ∑ a, π h a * ((1 - c) ^ (k + 1) * ∑ θ, w θ) := by
          apply Finset.sum_le_sum; intro a _
          apply mul_le_mul_of_nonneg_left _ ((hπ h).1 a)
          have h1 := ih (h ++ [a]) _ (Reachable.snoc a hr)
          have hsum : ∑ θ, w θ * (1 - κ θ h a) = ∑ θ, w θ - ∑ θ, w θ * κ θ h a := by
            rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro θ _; ring
          have hp := hpost h w hr a
          have h2 : ∑ θ, w θ * (1 - κ θ h a) ≤ (1 - c) * ∑ θ, w θ := by rw [hsum]; linarith
          have h3 : 0 ≤ (1 - c) ^ k := pow_nonneg (by linarith) k
          calc Vs π κ k (h ++ [a]) (fun θ => w θ * (1 - κ θ h a))
              ≤ (1 - c) ^ k * ∑ θ, w θ * (1 - κ θ h a) := h1
            _ ≤ (1 - c) ^ k * ((1 - c) * ∑ θ, w θ) := mul_le_mul_of_nonneg_left h2 h3
            _ = (1 - c) ^ (k + 1) * ∑ θ, w θ := by rw [pow_succ]; ring
      _ = (1 - c) ^ (k + 1) * ∑ θ, w θ := by rw [← Finset.sum_mul, (hπ h).2, one_mul]

/-- the seeded monitor violates the posterior hypothesis of `survival_avg`: after one surviving step the posterior
weight sits entirely on θ = false, whose catch rate is 0 -/
theorem seeded_violates_posterior {A : Type} (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (a b : A) :
    let ρ : Bool → ℝ := fun θ => if θ then c else 1 - c
    let κ : Bool → List A → A → ℝ := fun θ => seededκ θ
    ∃ w, Reachable ρ κ [a] w ∧ ¬ (c * ∑ θ, w θ ≤ ∑ θ, w θ * κ θ [a] b) := by
  intro ρ κ
  refine ⟨_, Reachable.snoc (h := []) a Reachable.nil, ?_⟩
  simp [ρ, κ, seededκ]
  nlinarith

/-- numbers: conditional catch rate 1/10 per step, 5 steps ⇒ survival ≤ 0.59049 -/
theorem survival_example {A : Type} [Fintype A] (π κ : List A → A → ℝ) (hπ : IsPolicy π) (hκ : IsMonitor κ)
    (hcκ : ∀ h a, (1 / 10 : ℝ) ≤ κ h a) (h : List A) : V π κ 5 h ≤ 0.59049 := by
  have := survival_le π κ hπ hκ (1 / 10) (by norm_num) hcκ 5 h
  norm_num at this ⊢; linarith

#print axioms survival_bounds
#print axioms survival_le
#print axioms survival_const
#print axioms seeded_marginal
#print axioms seeded_survival
#print axioms correlated_nogo
#print axioms Vs_eq
#print axioms reachable_nonneg
#print axioms survival_avg
#print axioms seeded_violates_posterior
#print axioms survival_example

end ControlStack.MultiStep
