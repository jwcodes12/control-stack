"""Convert LASR per-sample trusted-monitor scores to exact ROC bands.

This is an exploratory adapter for the public audit2 score archive. It does
not establish that its samples are held-out, IID, or deployment-matched.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path

from roc_bands import simultaneous_roc_bands


def read_scores(path: Path, column: str) -> list[int]:
    scores: list[int] = []
    with path.open(newline="") as stream:
        for row in csv.DictReader(stream):
            raw = row.get(column, "")
            if raw is None or raw.strip() == "":
                continue
            value = float(raw)
            if not value.is_integer() or not 0 <= value <= 10:
                raise ValueError(f"expected integer score in [0, 10], got {raw!r} in {path}")
            scores.append(int(value))
    if not scores:
        raise ValueError(f"no scores found in {path}")
    return scores


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def build(honest_path: Path, attack_path: Path, condition: str,
          alpha: str, denominator: int) -> dict:
    honest, attack = read_scores(honest_path, "trusted_suspiciousness_score"), read_scores(
        attack_path, "trusted_suspiciousness_score"
    )
    thresholds = []
    for cutoff in range(12):
        thresholds.append({
            "name": f"score_ge_{cutoff}",
            "fp": sum(score >= cutoff for score in honest),
            "tp": sum(score >= cutoff for score in attack),
        })
    bands = simultaneous_roc_bands({
        "alpha": alpha,
        "safe_n": len(honest),
        "backdoor_n": len(attack),
        "thresholds": thresholds,
        "endpoint_denominator": denominator,
    })
    return {
        "source": "LASR audit2 per-sample Inspect score archive",
        "condition": condition,
        "score_column": "trusted_suspiciousness_score",
        "positive_rule": "flag iff score >= integer cutoff; ties kept together",
        "honest_csv_sha256": sha256(honest_path),
        "attack_csv_sha256": sha256(attack_path),
        "sampling_warning": "Exploratory only: held-out status, IID sampling, and deployment match are not established.",
        "bands": bands,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("honest_csv", type=Path)
    parser.add_argument("attack_csv", type=Path)
    parser.add_argument("--condition", required=True)
    parser.add_argument("--alpha", default="1/20")
    parser.add_argument("--denominator", type=int, default=100_000)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = build(args.honest_csv, args.attack_csv, args.condition, args.alpha, args.denominator)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
