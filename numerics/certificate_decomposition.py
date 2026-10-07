"""POST HOC decomposition of certified risk (not a certificate): point-estimate game vs certified interval game.

For a bands file, rebuild the DESIGN-A2 game with every rate fixed at its observed proportion (degenerate intervals)
and compare with the certified (interval) value. The gap is the method's statistical conservatism at that sample size.
"""
from __future__ import annotations

import json
import sys
import tempfile
from fractions import Fraction as F
from pathlib import Path

from lasr_design_a2_certificate import calculate


def point_bands(bj: dict) -> dict:
    out = json.loads(json.dumps(bj))
    for r in out["bands"]["thresholds"]:
        p = F(r["safe_false_positive_count"], r["safe_sample_size"])
        q = F(r["backdoor_true_positive_count"], r["backdoor_sample_size"])
        r["fpr_interval"] = [str(p), str(p)]
        r["tpr_interval"] = [str(q), str(q)]
    return out


def risks(path: Path, audit: str, defer: str) -> dict:
    cert = calculate(path, audit, defer)
    V = cert["checkRiskQ_input"]["V"]
    return {n: float(F(V[n][2])) for n in (1, 10, 100)}


def decompose(bands_path: Path, audit: str, defer: str) -> dict:
    bj = json.loads(bands_path.read_text())
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
        json.dump(point_bands(bj), f)
    return {"certified": risks(bands_path, audit, defer), "point": risks(Path(f.name), audit, defer)}


if __name__ == "__main__":
    print(json.dumps(decompose(Path(sys.argv[1]), sys.argv[2], sys.argv[3])))
