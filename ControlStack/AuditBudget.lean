/-
A shared, fixed audit budget against a multi-step attack: random audit schedules compound, observable ones do not.

Model. There are N rounds, indexed by `Fin N`. The blue team audits exactly B of them; an attack step taken in an
audited round is caught, and catching any step ends the game. Red's attack needs k steps in k distinct rounds, i.e.
an attack is a set `A : Finset (Fin N)` with `#A = k`. An audit schedule is a set `S : Finset (Fin N)` with `#S = B`.
Red survives iff `Disjoint S A`. Blue's schedule is drawn uniformly from a finite family `𝒮` of schedules, and
  `survival 𝒮 A = #{S ∈ 𝒮 | Disjoint S A} / #𝒮`.
Two families matter: the uniformly random schedule `𝒮 = powersetCard B univ`, and a fixed schedule `𝒮 = {S}`.

Modelling remark (adaptivity, not formalised). In the random-schedule game Red cannot observe which rounds are
audited; the only feedback it ever receives is "caught", which ends the game. So along every surviving play Red's
observation sequence is the constant "not caught yet", and an adaptive Red strategy is determined by the single
sequence of rounds it would act in on that play, i.e. by a set A fixed in advance. Hence the survival probability of
an adaptive Red equals that of the non-adaptive Red choosing that A, and maximising over A is without loss.

Results.
1. `filter_disjoint_eq` / `random_subset_survival`: under the uniform schedule over `powersetCard B univ`, the
   number of schedules missing A is `choose (N - k) B`, so `survival = choose (N - k) B / choose N B` for every A
   with `#A = k` (and B ≤ N). It does not depend on which A Red picks.
2. `survival_le_pow`: for 0 < N, k ≤ N, B ≤ N, `choose (N - k) B / choose N B ≤ ((N - B) / N)^k`, i.e. sampling
   the audit rounds without replacement is at least as good for Blue as auditing each round independently with
   probability B/N. (`choose_mul_le` is the one-step inequality behind it.) Hence `random_survival_le_pow`.
3. `observable_schedule_nogo`: if the schedule is a fixed S known to Red, with `#S = B` and `k ≤ N - B`, then Red
   has an attack A with `#A = k` disjoint from S, and its survival is exactly 1.
4. `budget_example`: N = 100, B = 10, k = 5. Random-schedule survival is exactly
   `choose 95 10 / choose 100 10 = 10104934117421 / 17310309456440 ≈ 0.5838`; it is ≥ 0.58 and ≤ 0.59049 = 0.9^5.
   With the same budget but an observable schedule, survival is 1 (`budget_example_observable`).

Assumptions carried by the deployment, not by these theorems: an audit of an attack step catches it with
certainty; catching ends the game; Red needs its k steps in k distinct rounds and learns nothing about the
schedule beyond "not caught yet" (no side channel on which rounds are audited); the schedule really is uniform.
-/
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast

namespace ControlStack.AuditBudget

open Finset

/-- survival probability of attack `A` when the audit schedule is uniform over the family `𝒮` -/
noncomputable def survival {N : ℕ} (𝒮 : Finset (Finset (Fin N))) (A : Finset (Fin N)) : ℝ :=
  ((𝒮.filter (fun S => Disjoint S A)).card : ℝ) / (𝒮.card : ℝ)

/-- the uniformly random schedule: all B-subsets of the N rounds -/
def randomSchedules (N B : ℕ) : Finset (Finset (Fin N)) := powersetCard B (univ : Finset (Fin N))

/-- schedules of size B that miss A are exactly the B-subsets of the complement of A -/
theorem filter_disjoint_eq {N : ℕ} (B : ℕ) (A : Finset (Fin N)) :
    (randomSchedules N B).filter (fun S => Disjoint S A) = powersetCard B Aᶜ := by
  ext S
  simp [randomSchedules, mem_powersetCard, subset_compl_iff_disjoint_right, and_comm]

/-- (1) counting form and probability form of survival under a uniformly random size-B schedule -/
theorem random_subset_survival {N B k : ℕ} (A : Finset (Fin N)) (hA : A.card = k) :
    ((randomSchedules N B).filter (fun S => Disjoint S A)).card = Nat.choose (N - k) B ∧
    survival (randomSchedules N B) A = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) := by
  have hcount : ((randomSchedules N B).filter (fun S => Disjoint S A)).card = Nat.choose (N - k) B := by
    rw [filter_disjoint_eq, card_powersetCard, card_compl, Fintype.card_fin, hA]
  refine ⟨hcount, ?_⟩
  unfold survival
  rw [hcount]
  congr 1
  simp [randomSchedules, card_powersetCard]

/-- one step of sampling without replacement: `choose n B · N ≤ choose (n+1) B · (N - B)` when `n + 1 ≤ N` -/
theorem choose_mul_le {N B n : ℕ} (hB : B ≤ N) (hn : n + 1 ≤ N) :
    (Nat.choose n B : ℝ) * N ≤ (Nat.choose (n + 1) B : ℝ) * ((N : ℝ) - B) := by
  have hNB : (0 : ℝ) ≤ (N : ℝ) - B := by
    have : (B : ℝ) ≤ N := by exact_mod_cast hB
    linarith
  rcases lt_or_ge n B with h | h
  · rw [Nat.choose_eq_zero_of_lt h]
    simp only [Nat.cast_zero, zero_mul]
    exact mul_nonneg (Nat.cast_nonneg _) hNB
  · have key := Nat.choose_mul_succ_eq n B
    have hle : B ≤ n + 1 := by omega
    have key' : (Nat.choose n B : ℝ) * ((n : ℝ) + 1) =
        (Nat.choose (n + 1) B : ℝ) * ((n : ℝ) + 1 - B) := by
      have := congrArg (fun x : ℕ => (x : ℝ)) key
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hle] at this
      exact this
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnN : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
    have hc : (0 : ℝ) ≤ (Nat.choose (n + 1) B : ℝ) := Nat.cast_nonneg _
    have hBnn : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
    -- multiply the goal by n + 1 > 0
    refine le_of_mul_le_mul_right ?_ hpos
    calc (Nat.choose n B : ℝ) * N * ((n : ℝ) + 1)
        = (Nat.choose (n + 1) B : ℝ) * (((n : ℝ) + 1 - B) * N) := by rw [mul_right_comm, key']; ring
      _ ≤ (Nat.choose (n + 1) B : ℝ) * (((N : ℝ) - B) * ((n : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hc
          nlinarith
      _ = (Nat.choose (n + 1) B : ℝ) * ((N : ℝ) - B) * ((n : ℝ) + 1) := by ring

/-- cross-multiplied form of (2): `choose (N - k) B · N^k ≤ choose N B · (N - B)^k` -/
theorem choose_mul_pow_le {N B : ℕ} (hB : B ≤ N) :
    ∀ k : ℕ, k ≤ N → (Nat.choose (N - k) B : ℝ) * (N : ℝ) ^ k ≤ (Nat.choose N B : ℝ) * ((N : ℝ) - B) ^ k := by
  have hNB : (0 : ℝ) ≤ (N : ℝ) - B := by
    have : (B : ℝ) ≤ N := by exact_mod_cast hB
    linarith
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    have hsplit : N - k = (N - (k + 1)) + 1 := by omega
    have step := choose_mul_le (n := N - (k + 1)) hB (by omega)
    rw [← hsplit] at step
    have hNk : (0 : ℝ) ≤ (N : ℝ) ^ k := by positivity
    calc (Nat.choose (N - (k + 1)) B : ℝ) * (N : ℝ) ^ (k + 1)
        = ((Nat.choose (N - (k + 1)) B : ℝ) * N) * (N : ℝ) ^ k := by ring
      _ ≤ ((Nat.choose (N - k) B : ℝ) * ((N : ℝ) - B)) * (N : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right step hNk
      _ = ((N : ℝ) - B) * ((Nat.choose (N - k) B : ℝ) * (N : ℝ) ^ k) := by ring
      _ ≤ ((N : ℝ) - B) * ((Nat.choose N B : ℝ) * ((N : ℝ) - B) ^ k) :=
          mul_le_mul_of_nonneg_left ih' hNB
      _ = (Nat.choose N B : ℝ) * ((N : ℝ) - B) ^ (k + 1) := by ring

/-- (2) sampling audit rounds without replacement beats independent per-round auditing at rate B/N -/
theorem survival_le_pow {N B k : ℕ} (hN : 0 < N) (hk : k ≤ N) (hB : B ≤ N) :
    (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) ≤ (((N : ℝ) - B) / N) ^ k := by
  have hc : (0 : ℝ) < (Nat.choose N B : ℝ) := by exact_mod_cast Nat.choose_pos hB
  have hNpos : (0 : ℝ) < (N : ℝ) ^ k := by positivity
  rw [div_pow, div_le_div_iff₀ hc hNpos]
  rw [mul_comm ((((N : ℝ) - B)) ^ k)]
  exact choose_mul_pow_le hB k hk

/-- (1)+(2): every k-step attack survives a uniformly random size-B schedule with probability ≤ ((N-B)/N)^k -/
theorem random_survival_le_pow {N B k : ℕ} (hN : 0 < N) (hk : k ≤ N) (hB : B ≤ N)
    (A : Finset (Fin N)) (hA : A.card = k) :
    survival (randomSchedules N B) A ≤ (((N : ℝ) - B) / N) ^ k := by
  rw [(random_subset_survival (B := B) A hA).2]
  exact survival_le_pow hN hk hB

/-- (3) an observable fixed schedule is useless against a k-step attack when k ≤ N - B -/
theorem observable_schedule_nogo {N B k : ℕ} (S : Finset (Fin N)) (hS : S.card = B) (hk : k ≤ N - B) :
    ∃ A : Finset (Fin N), A.card = k ∧ Disjoint S A ∧ survival {S} A = 1 := by
  have hcard : k ≤ (Sᶜ).card := by rw [card_compl, Fintype.card_fin, hS]; exact hk
  obtain ⟨A, hAsub, hAcard⟩ := exists_subset_card_eq hcard
  have hdisj : Disjoint S A := by
    rw [subset_compl_iff_disjoint_right] at hAsub
    exact hAsub.symm
  refine ⟨A, hAcard, hdisj, ?_⟩
  unfold survival
  rw [filter_singleton, ite_eq_left_of_eq_true _ _ (eq_true hdisj)]
  simp

/-- exact values used in the numeric example -/
theorem choose_100_10 : Nat.choose 100 10 = 17310309456440 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

theorem choose_95_10 : Nat.choose 95 10 = 10104934117421 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

/-- (4) N = 100 rounds, budget B = 10, k = 5 steps: random-schedule survival ≈ 0.5838 ∈ [0.58, 0.59049] -/
theorem budget_example (A : Finset (Fin 100)) (hA : A.card = 5) :
    survival (randomSchedules 100 10) A = (10104934117421 : ℝ) / 17310309456440 ∧
    survival (randomSchedules 100 10) A ≤ 0.59049 ∧
    (0.58 : ℝ) ≤ survival (randomSchedules 100 10) A := by
  have h1 := (random_subset_survival (B := 10) A hA).2
  have h2 := random_survival_le_pow (B := 10) (by norm_num) (by norm_num) (by norm_num) A hA
  have hval : survival (randomSchedules 100 10) A = (10104934117421 : ℝ) / 17310309456440 := by
    rw [h1]
    norm_num [choose_100_10, choose_95_10]
  refine ⟨hval, ?_, ?_⟩
  · norm_num at h2 ⊢; linarith
  · rw [hval]; norm_num

/-- (4') same budget, observable schedule: a 5-step attack survives with probability 1 -/
theorem budget_example_observable (S : Finset (Fin 100)) (hS : S.card = 10) :
    ∃ A : Finset (Fin 100), A.card = 5 ∧ survival {S} A = 1 := by
  obtain ⟨A, hA, -, h⟩ := observable_schedule_nogo S hS (by norm_num : 5 ≤ 100 - 10)
  exact ⟨A, hA, h⟩

#print axioms filter_disjoint_eq
#print axioms random_subset_survival
#print axioms choose_mul_le
#print axioms choose_mul_pow_le
#print axioms survival_le_pow
#print axioms random_survival_le_pow
#print axioms observable_schedule_nogo
#print axioms choose_100_10
#print axioms choose_95_10
#print axioms budget_example
#print axioms budget_example_observable

end ControlStack.AuditBudget
