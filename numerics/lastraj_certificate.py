"""Preregistered LaStraj certificate (PREREG-LASTRAJ.md): DESIGN-A2 game at audit score_ge_7, defer score_ge_3."""
import json
from pathlib import Path

import emit_lasr_design_a2_lean as emit
from lasr_design_a2_certificate import calculate

HERE = Path(__file__).resolve().parent
data = calculate(HERE / "lastraj_roc_bands.json", "score_ge_7", "score_ge_3")
data["description"] = "LaStraj 2.0 preregistered ROC-band interval game (see PREREG-LASTRAJ.md)"
(HERE / "lastraj_certificate.json").write_text(json.dumps(data, indent=2) + "\n")
lean = emit.emit(data, emit.STATEMENT.read_text(), emit.PROOF.read_text()).replace(
    "namespace LasrA2Certificate", "namespace LaStrajCertificate").replace(
    "end LasrA2Certificate", "end LaStrajCertificate")
(HERE / "lastraj_certificate.lean").write_text(lean)
print({k: data[k] for k in ("thresholds", "dimensions", "full_information_rectangular_risk_upper",
                            "honest_used_solutions_lower_simple", "checker_inequalities")})
print({k: v for k, v in data["uncertainty"].items() if k != "vertices_q_audit_tpr_defer_tpr"})
