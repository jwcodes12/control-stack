"""Emit a standalone Lean kernel check for the empirical A2 certificate table."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
STATEMENT = Path(__file__).resolve().parent.parent / "ledger" / "TMCERT.lean"
PROOF = Path(__file__).resolve().parent.parent / "proofs" / "TMCERTF1.lean"


def frac(text: str) -> str:
    n, d = text.split("/", 1)
    return f"(({n} : ℚ) / {d})"


def emit(data: dict, statement_text: str, proof_text: str) -> str:
    payload = data["checkRiskQ_input"]
    cats, kernels, values = payload["cat"], payload["K"], payload["V"]
    t = data["dimensions"]["models"]
    n = data["dimensions"]["N"]
    m = data["dimensions"]["states"]
    k = data["dimensions"]["actions"]
    coins = m - 1
    if not (t == len(cats) == len(kernels) and n == len(cats[0]) == len(kernels[0])):
        raise ValueError("certificate dimensions do not match arrays")
    # All model rows are time-homogeneous in this concrete fixture.
    if any(model[i] != model[0] for model in cats for i in range(1, n)):
        raise ValueError("catastrophe table unexpectedly varies by horizon row")
    if any(model[i] != model[0] for model in kernels for i in range(1, n)):
        raise ValueError("transition table unexpectedly varies by horizon row")

    cat_cases = []
    for th in range(t):
        for s in range(m):
            for a in range(k):
                cat_cases.append(f"  | {th}, {s}, {a} => {frac(cats[th][0][s][a])}")
    k_cases = []
    for th in range(t):
        for s in range(m):
            for a in range(k):
                for sp in range(m):
                    k_cases.append(f"  | {th}, {s}, {a}, {sp} => {frac(kernels[th][0][s][a][sp])}")
    v_cases = []
    for i in range(n + 1):
        for s in range(m):
            v_cases.append(f"  | {i}, {s} => {frac(values[i][s])}")
    statement_hash = hashlib.sha256(statement_text.encode()).hexdigest()
    proof_hash = hashlib.sha256(proof_text.encode()).hexdigest()
    body = f'''\n/- Frozen TMCERTF1 statement SHA256: {statement_hash}; proof SHA256: {proof_hash} -/
namespace TMCERTProof
open PL_TMCERTF1
{proof_text}
end TMCERTProof

namespace LasrA2Certificate
open PL_TMCERTF1

def cat : Fin {t} → Fin {n} → Fin {m} → Fin {k} → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
{chr(10).join(cat_cases)}
  | _, _, _ => 0

def kernel : Fin {t} → Fin {n} → Fin {m} → Fin {k} → Fin {m} → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
{chr(10).join(k_cases)}
  | _, _, _, _ => 0

def value : Fin ({n} + 1) → Fin {m} → ℚ := fun i s =>
  match i.val, s.val with
{chr(10).join(v_cases)}
  | _, _ => 0

theorem risk_table_passes : checkRiskQ {n} {m} {k} {t} cat kernel value = true := by
  decide +kernel

theorem lawful_rows_pass : checkLawfulQ {n} {m} {k} {t} cat kernel = true := by
  decide +kernel

#print axioms risk_table_passes
#print axioms lawful_rows_pass

theorem full_information_risk_bound
    (σ : RHist (Fin {m}) (Fin {k}) → Fin {m} → Fin {k} → ℝ)
    (θ : ℕ → RHist (Fin {m}) (Fin {k}) → Fin {m} → Fin {k} → Fin {t})
    (hσ : IsPolicy σ)
    (hθ : SelectorUpTo {n} (fun _ _ _ _ => True) θ) :
    risk (gameOfQ {n} {m} {k} {t} cat kernel) θ σ {n} {coins} [] ≤
      valOfQ {n} {m} value {n} {coins} := by
  have hRisk := (TMCERTProof.claimQ {n} {m} {k} {t} cat kernel value).1 risk_table_passes
  have hLawful := (TMCERTProof.claimQ {n} {m} {k} {t} cat kernel value).2 lawful_rows_pass
  have hK : AdmKNonneg {n} (gameOfQ {n} {m} {k} {t} cat kernel)
      (fun _ _ _ _ => True) := by
    intro i hi s a th _ s'
    exact ((hLawful th {n} i hi s a).2.1 s')
  exact TMCERTProof.claimS (Fin {m}) (Fin {k}) (Fin {t}) {n}
    (gameOfQ {n} {m} {k} {t} cat kernel) (fun _ _ _ _ => True)
    (valOfQ {n} {m} value) σ θ hK hRisk.1 hσ hθ {n} le_rfl {coins} []

#print axioms full_information_risk_bound

end LasrA2Certificate
'''
    return "import Mathlib\n\n" + statement_text + "\n" + body


def main() -> int:
    data_path = HERE / "lasr_design_a2_certificate.json"
    output = HERE / "lasr_design_a2_certificate.lean"
    if not STATEMENT.exists() or not PROOF.exists():
        raise FileNotFoundError(f"frozen TMCERTF1 statement or proof missing: {STATEMENT} {PROOF}")
    output.write_text(emit(json.loads(data_path.read_text()), STATEMENT.read_text(), PROOF.read_text()))
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
