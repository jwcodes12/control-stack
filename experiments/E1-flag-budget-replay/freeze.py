#!/usr/bin/env python3
"""Compute the hashes that pin experiment E1, and (with --write, after the owner authorises the run) freeze it.

  python3 experiments/E1-flag-budget-replay/freeze.py            # print what would be frozen; changes nothing
  python3 experiments/E1-flag-budget-replay/freeze.py --write    # write freeze.json with status FROZEN

After --write, commit freeze.json before the confirmatory run. PREREG.md, analyze.py, numerics/budgeted_audit.py and
the data files must not change afterwards; analyze.py --confirm re-checks every hash.
"""
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DATA = "data/linuxarena-public/compact"


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main(argv):
    data = ROOT / DATA
    files = sorted(p.relative_to(data).as_posix() for d in ("meta", "sealed") for p in (data / d).glob("*.jsonl.gz"))
    assert len(files) == 20, files
    freeze = {
        "status": "FROZEN" if "--write" in argv else "DRAFT",
        "experiment": "E1-FLAG-BUDGET-REPLAY",
        "prereg_sha256": sha(HERE / "PREREG.md"),
        "analysis_sha256": sha(HERE / "analyze.py"),
        "model_sha256": sha(ROOT / "numerics" / "budgeted_audit.py"),
        "data_dir": DATA,
        "data_sha256": {f: sha(data / f) for f in files},
        "development_run_ids": json.loads((HERE / "development_run_ids.json").read_text()),
    }
    text = json.dumps(freeze, indent=1, sort_keys=True) + "\n"
    if "--write" in argv:
        assert not (HERE / "results" / "confirmatory.json").exists(), "already run"
        (HERE / "freeze.json").write_text(text)
        print("freeze.json written with status FROZEN. Commit it, then run:")
        print(f"  E1_PREREG_SHA256={freeze['prereg_sha256']} python3 experiments/E1-flag-budget-replay/analyze.py --confirm")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
