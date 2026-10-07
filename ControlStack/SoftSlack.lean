/-
VCVio interface for the constant-hazard soft-slack honeypot test.

Each honeypot is sampled and monitored freshly. A PASS then triggers an independent
rejection coin with probability `1/(d+1)`; a rejection ends the test. Setting
`ns = d+1` gives the UMSURV soft-slack hazard `1/ns`, with survival `(1 - h/ns)^n`.
-/
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.ProbComp
import ControlStack.RefinementProof

open OracleComp

namespace ControlStack.SoftSlack

def rejectionCoin (d : ℕ) : ProbComp Bool := do
  let j ← $[0..d]
  pure (j.val = 0)

def survives {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (d : ℕ) : ℕ → ProbComp Bool
  | 0 => pure true
  | n + 1 => do
      let pass ← H >>= M >>= D
      if pass then do
        let reject ← rejectionCoin d
        if reject then pure false else survives H M D d n
      else
        survives H M D d n

theorem rejection_rate (d : ℕ) :
  (Pr[= true | rejectionCoin d]).toReal = 1 / ((d + 1 : ℕ) : ℝ) := by
  simp [rejectionCoin, probOutput_map_eq_sum_finSupport_ite, ProbComp.finSupport_uniformFin,
    ProbComp.probOutput_uniformFin, Finset.sum_ite_eq']
  rw [ENNReal.toReal_add (by simp) (by simp)]
  norm_num

theorem survives_step {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z)
    (D : Z → ProbComp Bool) (d n : ℕ) :
    Pr[= true | survives H M D d (n + 1)] =
      Pr[= true | H >>= M >>= D] * Pr[= false | rejectionCoin d] *
          Pr[= true | survives H M D d n] +
        Pr[= false | H >>= M >>= D] * Pr[= true | survives H M D d n] := by
  rw [survives]
  simp only [probOutput_bind_eq_tsum, tsum_fintype, Fintype.sum_bool]
  have hbranch :
      Pr[= true | do
        let reject ← rejectionCoin d
        if reject then pure false else survives H M D d n] =
        Pr[= false | rejectionCoin d] * Pr[= true | survives H M D d n] := by
    rw [probOutput_bind_eq_tsum, tsum_fintype, Fintype.sum_bool]
    simp
  simp
  rw [hbranch]
  ring

theorem survives_step_real {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z)
    (D : Z → ProbComp Bool) (d n : ℕ) :
    (Pr[= true | survives H M D d (n + 1)]).toReal =
      (1 - (Pr[= true | H >>= M >>= D]).toReal / ((d + 1 : ℕ) : ℝ)) *
        (Pr[= true | survives H M D d n]).toReal := by
  rw [survives_step, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ControlStack.Refine.probOutput_false_toReal, rejection_rate,
    ControlStack.Refine.probOutput_false_toReal]
  ring

def BridgeClaim : Prop :=
  ∀ (X Z : Type) (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (d n : ℕ),
    (Pr[= true | survives H M D d n]).toReal =
      (1 - (Pr[= true | H >>= M >>= D]).toReal / ((d + 1 : ℕ) : ℝ)) ^ n

theorem bridge : BridgeClaim := by
  intro X Z H M D d n
  induction n with
  | zero => simp [survives]
  | succ n ih =>
      rw [survives_step_real, ih]
      ring

#print axioms bridge

end ControlStack.SoftSlack
