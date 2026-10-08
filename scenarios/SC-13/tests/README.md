# SC-13 tests / falsifiers

Existing test/evidence artifacts are linked through `scenario.json`; this folder does **not** contain new passing experiments.

- `auditgate/outcome_matrix.json`
- `auditgate/FIDELITY.md`

Suggested negative case: Trigger a workflow effect through a path bypassing the dispatcher, or forge/drop the trusted audit record.

Do not use `--lint` as an endorsement; see `scenarios/README.md`.
