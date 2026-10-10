# Linux reference-harness dry-run adversarial regression

CI `reference-harness-dry-regression` runs the **existing** SC-06, SC-08 and SC-25 userland reference harnesses, each `--kind dry --reps 1` in distinct, fresh runner scratch outputs; then runs SC-26 deterministic Python model/bank negative tests. This exercises real separate processes, Unix sockets, script/interpreter policies and audit-queue actor behavior, and detects regressions across the predefined normal and check-removal cases.

This **does not** run an experiment in evidence mode, append to preregistered receipts, replace historical evidence, or establish that the action model matches all live Linux execution paths. A one-repetition smoke check is not the preregistered sample or a valid usefulness measurement. SC-06's current stored (agent, tool, value) confirmation contract is different from the new SC06OneUse exact handle/one-use alternative Lean model; no refinement is claimed between them. SC-08's launcher process has an explicit exclusive-entry-path premise. SC-25's executor models abstract log append effects, not arbitrary irreversible host operations. SC-26's live distinct-UID end-to-end verification requires an authorized root-capable ephemeral Linux host; this source PR doesn't provide such privileges.

Reproduce on a trusted Linux host as a **nonroot** user (without altering evidence):

```sh
python3 -B scenarios/SC-06/harness/run_sc06.py --kind dry --reps 1 --out /tmp/new-sc06-dry
python3 -B scenarios/SC-08/harness/run_sc08.py --kind dry --reps 1 --out /tmp/new-sc08-dry
python3 -B scenarios/SC-25/harness/run_sc25.py --kind dry --reps 1 --out /tmp/new-sc25-dry
python3 scenarios/SC-26/harness/test_model.py
python3 scenarios/SC-26/harness/test_bank.py
```

Output directories must not exist beforehand. Review the full job steps and always compare the actual latest PR head SHA. Never count `dry` as recorded experimental evidence.
