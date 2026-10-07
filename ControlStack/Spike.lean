/-
Phase-0 integration spike: one tiny adversary / probability example on VCVio.
T1 (distinguishing bound) in crypto-game form: an ARBITRARY randomised distinguisher `D`
(the untrusted monitor), applied to the mediated real attack vs the mediated honeypot, has
advantage at most the TV distance of the mediated laws.  Uses VCVio's
`abs_probOutput_toReal_sub_le_tvDist` and `tvDist_bind_right_le` (Apache-2.0).
-/
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.ProbComp

open OracleComp

namespace ControlStack.Spike

/-- Mediator `M`, attack law `PA` (chosen by the untrusted generator), honeypot law `PH`
(trusted), arbitrary distinguisher `D`. -/
theorem distinguish_le_tv {X Z : Type} (M : X → ProbComp Z) (PA PH : ProbComp X)
    (D : Z → ProbComp Bool) :
    |Pr[= true | PA >>= M >>= D].toReal - Pr[= true | PH >>= M >>= D].toReal|
      ≤ tvDist (PA >>= M) (PH >>= M) :=
  (abs_probOutput_toReal_sub_le_tvDist _ _).trans (tvDist_bind_right_le _ _ _)

/-- Data processing through the mediator. -/
theorem mediated_tv_le {X Z : Type} (M : X → ProbComp Z) (PA PH : ProbComp X) :
    tvDist (PA >>= M) (PH >>= M) ≤ tvDist PA PH :=
  tvDist_bind_right_le _ _ _

end ControlStack.Spike
