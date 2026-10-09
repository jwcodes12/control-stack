# SC-26 tests

The harness lives in `scenarios/SC-26/harness/`. Its README describes how to run it and what it trusts.

- **Unit tests:**
  - `python3 scenarios/SC-26/harness/test_model.py` covers the model mirror, every Lean witness, and random traces
    that keep `Inv`.
  - `python3 scenarios/SC-26/harness/test_bank.py` covers bank idempotency and conflict detection.
- **Lean link:** `python3 scenarios/SC-26/harness/lean_difftest.py` compares 200 random traces with Lean `#eval`.
- **Live run** (needs root and separate UIDs): `sudo -n /bin/python3 -B scenarios/SC-26/harness/run_sc26.py --label dry --out <scratch>`.
  It runs the attacks, the controls, the usefulness test and the baseline.
- **Evidence:** `scenarios/SC-26/evidence/run-1`, under `PREREG-SC26-TXGATE-v2`.
- **Recheck everything:** `python3 tools/check_sc26_case.py`.
