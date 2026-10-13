`SC90TrustedMonitorAudit.lean` is the file produced by the flexibility test (docs/FLEXIBILITY-TEST.md): trusted monitoring with a finite audit budget as a
gate-shaped scenario, generated from `sc90.json` by `tools/new_scenario.py` and then filled in. It lives here, NOT in `ControlStack/Scenarios/`, on purpose:
it is not yet part of the library, so it is not imported by `ControlStack.lean`, not in THEOREM-REGISTRY or the 187-claim indexes, and has no Python mirror,
scenario bundle or preregistration. Check it with `lake env lean docs/flexibility-test/SC90TrustedMonitorAudit.lean` (about 5 s; standard axioms only, no `sorry`).
To promote it: move it to `ControlStack/Scenarios/`, add the import, write the harness and bundle, regenerate the registry on the pinned runner.
