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

end ControlStack.Bridge
