"""Emit a UseQ certificate for the current LASR interval-game fixture.

The certificate is conditional on the bundled interval model. The source scores
are not established as predeclared, held-out deployment samples; see DESIGN-A2.md.
"""
from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


def q(text: str) -> Fraction:
    return Fraction(text)


def lean_q(x: Fraction) -> str:
    return f"(({x.numerator} : ℚ) / {x.denominator})"


def emit(data: dict) -> str:
    bands = data["uncertainty"]
    vertices = [tuple(map(q, row)) for row in bands["vertices_q_audit_tpr_defer_tpr"]]
    n = data["dimensions"]["N"]
    m = data["dimensions"]["states"]
    t = len(vertices)
    qd_hi = q(bands["defer_fpr"][1])
    reward_floor = 1 - qd_hi

    rewards = []
    kernels = []
    for th, (qa, _ta, _td) in enumerate(vertices):
        for s in range(m):
            rew = reward_floor + (qa if s > 0 else 0)
            rewards.append(f"  | {th}, {s} => {lean_q(rew)}")
            for sp in range(m):
                mass = Fraction(0)
                if s == 0:
                    mass = Fraction(1) if sp == 0 else Fraction(0)
                elif sp == s - 1:
                    mass = qa
                elif sp == s:
                    mass = 1 - qa
                kernels.append(f"  | {th}, {s}, {sp} => {lean_q(mass)}")

    floor = n * reward_floor
    return f'''/- Generated from lasr_design_a2_certificate.json; conditional interval-model result. -/
import ControlStack.UseQ

set_option maxHeartbeats 5000000

namespace LasrUsefulnessCertificate
open ControlStack.UseQ

def reward : Fin {t} → Fin {n} → Fin {m} → ℚ := fun th _i s =>
  match th.val, s.val with
{chr(10).join(rewards)}
  | _, _ => 0

def kernel : Fin {t} → Fin {n} → Fin {m} → Fin {m} → ℚ := fun th _i s sp =>
  match th.val, s.val, sp.val with
{chr(10).join(kernels)}
  | _, _, _ => 0

def admissible : Fin {t} → Fin {n} → Fin {m} → Bool := fun _ _ _ => true

def value : Fin ({n} + 1) → Fin {m} → ℚ := fun i _ =>
  (i.val : ℚ) * {lean_q(reward_floor)}

def initial : Fin {m} := ⟨{m - 1}, by omega⟩
def floor : ℚ := {lean_q(floor)}

theorem checker_passes :
    checkUseQ {n} {m} {t} reward kernel admissible value initial floor = true := by
  decide +kernel

/-- Every full-history-dependent admissible model selector earns the certified floor. -/
theorem adaptive_usefulness
    (θ : ℕ → List (Fin {m}) → Fin {m} → Fin {t})
    (hθ : ∀ i (hi : i < {n}) hist s, admissible (θ i hist s) ⟨i, hi⟩ s = true) :
    (floor : ℝ) ≤ honestValue reward kernel θ {n} initial [] := by
  apply checkUseQ_sound reward kernel admissible value initial floor θ checker_passes
  · intro th i s _ sp
    fin_cases th <;> fin_cases s <;> fin_cases sp <;> norm_num [kernel]
  · exact hθ

#print axioms checker_passes
#print axioms adaptive_usefulness

end LasrUsefulnessCertificate
'''


def main() -> None:
    here = Path(__file__).resolve().parent
    data = json.loads((here / "lasr_design_a2_certificate.json").read_text())
    out = here / "lasr_usefulness_certificate.lean"
    out.write_text(emit(data))
    print(out)
    print("floor:", data["dimensions"]["N"] *
          (1 - q(data["uncertainty"]["defer_fpr"][1])))


if __name__ == "__main__":
    main()
