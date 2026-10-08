# SC-27 tests / falsifiers

Existing test/evidence artifacts are linked through `scenario.json`; this folder does **not** contain new passing experiments.

- `assurance/check_manifests.py`

Suggested negative case: Alter a hash and its manifest together, or substitute a forged CI attestation.

Do not use `--lint` as an endorsement; see `scenarios/README.md`.
