/-
Interface level (VCVio): the honeypot test as a `ProbComp` game.
An arbitrary monitor `D : Z → ProbComp Bool` (true = PASS) is automatically stateless with fresh coins per call;
the honeypot law `H`, the mediator `M` are arbitrary `ProbComp`s. Statement to prove (bridge to the core's
PL_UMSURVF1): the number of PASSes among `n` honeypots is binomial with parameter
h = Pr[= true | H >>= M >>= D].
-/
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.ProbComp

open OracleComp

namespace ControlStack.Bridge

/-- run `n` honeypots and count the monitor's PASSes -/
def honeypotPasses {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) :
    ℕ → ProbComp ℕ
  | 0 => pure 0
  | n + 1 => do
      let b ← (H >>= M >>= D)
      let k ← honeypotPasses H M D n
      pure (if b then k + 1 else k)

/-- binomial CDF (same text as PL_UMSURVF1.binCDF) -/
def binCDF (n s : ℕ) (h : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (s + 1), (n.choose j : ℝ) * h ^ j * (1 - h) ^ (n - j)

/-- the bridge statement (to be proved): survival of the hard-slack honeypot test -/
def BridgeClaim : Prop :=
  ∀ (X Z : Type) (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (n s : ℕ),
    (Pr[fun k => k ≤ s | honeypotPasses H M D n]).toReal =
      binCDF n s (Pr[= true | H >>= M >>= D]).toReal

theorem honeypotPasses_step {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z)
    (D : Z → ProbComp Bool) (n k : ℕ) :
    Pr[= k | honeypotPasses H M D (n + 1)] =
      Pr[= true | H >>= M >>= D] * Pr[= k | (fun a => a + 1) <$> honeypotPasses H M D n] +
      Pr[= false | H >>= M >>= D] * Pr[= k | honeypotPasses H M D n] := by
  rw [honeypotPasses, probOutput_bind_eq_tsum, tsum_fintype, Fintype.sum_bool]
  simp

theorem honeypotPasses_probOutput {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z)
    (D : Z → ProbComp Bool) (n k : ℕ) :
    Pr[= k | honeypotPasses H M D n] =
      (n.choose k : ENNReal) * Pr[= true | H >>= M >>= D] ^ k *
        Pr[= false | H >>= M >>= D] ^ (n - k) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [honeypotPasses]
    | succ k => simp [honeypotPasses]
  | succ n ih =>
    rw [honeypotPasses_step]
    cases k with
    | zero =>
      have h0 : Pr[= 0 | (fun a => a + 1) <$> honeypotPasses H M D n] = 0 := by simp
      rw [h0, ih]
      simp [pow_succ]
      ring
    | succ j =>
      have h1 : Pr[= j + 1 | (fun a => a + 1) <$> honeypotPasses H M D n] =
          Pr[= j | honeypotPasses H M D n] :=
        probOutput_map_injective _ (fun a b h => by simpa using h) j
      rw [h1, ih, ih, Nat.choose_succ_succ', Nat.add_sub_add_right]
      push_cast
      rcases Nat.lt_or_ge j n with hjn | hjn
      · obtain ⟨r, rfl⟩ : ∃ r, n = j + 1 + r := ⟨n - (j + 1), by omega⟩
        have e1 : j + 1 + r - j = r + 1 := by omega
        have e2 : j + 1 + r - (j + 1) = r := by omega
        rw [e1, e2]
        ring
      · rw [Nat.choose_eq_zero_of_lt (by omega : n < j + 1)]
        simp
        ring

theorem bridge : BridgeClaim := by
  intro X Z H M D n s
  have key : ∀ c : ProbComp Bool, Pr[= true | c] + Pr[= false | c] = 1 := fun c => by
    have h := sum_probOutput_eq_sub c
    rw [Fintype.sum_bool] at h
    rw [h]
    simp
  have hpq : Pr[= true | H >>= M >>= D] + Pr[= false | H >>= M >>= D] = 1 := key _
  have hq : Pr[= false | H >>= M >>= D] = 1 - Pr[= true | H >>= M >>= D] := by
    rw [← hpq, ENNReal.add_sub_cancel_left probOutput_ne_top]
  have hp1 : Pr[= true | H >>= M >>= D] ≤ 1 := probOutput_le_one
  rw [probEvent_eq_tsum_ite, tsum_eq_sum (s := Finset.range (s + 1)), ENNReal.toReal_sum]
  · unfold binCDF
    refine Finset.sum_congr rfl fun k hk => ?_
    have hks : k ≤ s := by simpa [Nat.lt_succ_iff] using hk
    rw [if_pos hks, honeypotPasses_probOutput, hq, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hp1 ENNReal.one_ne_top]
    simp
  · intro k _
    split_ifs
    · exact probOutput_ne_top
    · exact ENNReal.zero_ne_top
  · intro k hk
    rw [if_neg]
    simpa [Nat.lt_succ_iff] using hk

end ControlStack.Bridge
