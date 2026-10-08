# SC-01 current status — 2026-10-08

## Completed and published

Private branch `sc01-repair-viability`, commit `9a7e3a6`, contains the bounded
repair experiment, durable lifetime accounting, proofs and saved evidence.
Baseline and mediated agents each completed 320/320 repairs across 64 lifetimes;
the preregistered simultaneous lower completion bound is 93.382%.
The shared-file-cache experiment decoded one synthetic secret bit in 64/64 trials
with a constant NULL gateway view. This falsifies the sole-transcript premise in
that harness; it does not demonstrate full-secret recovery. Runtime secrecy
remains uncertified; overall verdict is CONDITIONAL. Auditgate is untouched.

All three publication workflows completed successfully:

- [scenario-a-repair](https://github.com/jwcodes12/control-stack/actions/runs/37815790500)
- [fast-checks](https://github.com/jwcodes12/control-stack/actions/runs/37815790901)
- [egress-boundary](https://github.com/jwcodes12/control-stack/actions/runs/37815790502)

See `README.md`, `results/local-full.json`, and `results/local-cache.json` for
scope, commands and original source-bound evidence.

## Current experiment: separate runtime files

Purpose: test whether separate runtime-file copies remove the observed cache
signal while preserving repair usefulness. This is local, authorized sandbox
research using synthetic secrets, not a deployment or a complete isolation proof.
The host has no `/dev/kvm` or installed VM runner. Separate files leave shared
kernel state, CPU caches, clocks and scheduling unresolved.

The prospective protocol is committed as `8b96430` in
`PREREG-SC01-PRIVATE-RUNTIME.md`. Draft implementation files exist locally:

- `private_runtime.py`: independent file copies and trusted role assignment.
- `private_run.py`: positive-control cache experiment and private-runtime replay.
- `check_private_receipt.py`: source bindings and conditional evidence checks.
- `test_private_runtime.py`: alias/content/promotion rejection controls.
- `agents/private_preflight.py`: namespace, capability and backing-file checks.

Verification so far: `/usr/bin/python3 gateway/scenario/test_private_runtime.py`
passed three tests; `git diff --check` passed. These controls do not establish
that the new runtime works.

The first smoke invocation failed with `AttributeError: __enter__` because
`PrivateRuntime` is used as a context manager without implementing that interface.
No `/tmp/sc01-private-smoke.json` was produced. No new cache comparison or repair
measurement is complete, and no improvement in isolation is claimed. Draft
implementation files have not been committed or published.

## Next steps

1. Fix context-manager lifecycle and complete actual private-runtime preflights.
2. Run and preserve the positive-control/shared-versus-private cache measurements.
3. Replay all 64 paired repair lifetimes under the private runtime and verify receipts.
4. Show meaningful measured results and source provenance to Opus at xhigh and
   Astra at high; apply findings and retain explicit unresolved assumptions.
5. Update the conditional case and CI after the experiment is validated.

The newly requested reviews have not been run yet. Earlier roadmap reviews were
Opus xhigh and Astra xhigh; they do not count as reviews of this new experiment.
App cybersecurity warnings were reported by the user; their exact triggers are
unknown. The smoke failure above is a directly observed implementation error.
