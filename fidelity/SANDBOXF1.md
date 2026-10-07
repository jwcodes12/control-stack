# Fidelity audit (orchestrator): SANDBOXF1, action layer step 1 (the proofledger sandbox policy)

Statement: `ledger/SANDBOX.lean`. Source policy: `~/research/proofledger/harness/dispatch.py::sandbox()` as of
2026-10-07, before any fix.

## Correspondence to the real code
| code | model |
|---|---|
| `--dev-bind / /` | `.bind [] [] .rw` (dev-bind and bind are both read-write binds; device-node semantics are not modelled) |
| `--tmpfs /var/tmp` | `.tmpfs ["var","tmp"]` |
| `--bind W /var/tmp/work` | `.bind W ["var","tmp","work"] .rw` |
| `--tmpfs d` for d ∈ HIDE_DIRS (if it exists) | `hiddenDirs.map .tmpfs`. All are assumed to exist; a missing dir only removes a mount, and the property shapes are unaffected for paths under it, since there is nothing to hide |
| `--bind W/.empty ~/.codex/history.jsonl` (HIDE_FILES) | **omitted**. A read-only empty file over one path; it does not affect (a) or (b), and (c) is stated for hidden *directories* |
| `--ro-bind MATHLIB MATHLIB` | `.bind mathlibProj mathlibProj .ro` |
| mount order = argument order; the later covering mount wins | `effective = (filter (tgt is an initial segment of p)).getLast?` |
| host permission (uid opc) | `canWrite` predicate. In (a) it is instantiated as "inside home or /var/tmp"; in (b) it is universally quantified |

## Conjuncts
- **(a)** For every scratch W under /var/tmp, a sandboxed process can write the host path `~/.elan/bin/lake`.
  - This is a **counterexample to the docstring's "writable scratch only"**. The unsandboxed gate runs
    `lake env lean` with `PATH=~/.elan/bin:…`, so a sandboxed model could replace the toolchain the gate trusts.
  - Faithful as a model fact. Whether real bwrap allows it also depends on the host permission bits; ~/.elan is owned
    by opc, consistent with canWrite.
  - Not tested on the live system: a read-only probe of the related /proc escape was blocked by the session's
    permission classifier, and no write test was attempted.
- **(b)** A read-only-root policy with only scratch and declared state directories writable confines host writes to
  those, for every path and every permission predicate. Faithful.
  - The fix is a proposal. It has not been deployed: the CLIs' actual state-directory needs (e.g. `~/.codex/auth.json`
    token refresh) must be tested first.
- **(c)** The current policy's hiding works as intended at the mount level. Faithful, under the named boundary
  assumption.

## Boundary assumptions (stated in the statement's docstring)
- No `/proc/<pid>/root` alias: there is no PID namespace (the scout's G5, unverified). If the alias works, (c) fails in
  reality, outside the model.
- No network or other side channels.
- Hidden files omitted.

**Novelty.** None as mathematics. The value is a machine-checked model of a real policy that pins down a real defect
and its fix: the first action-layer row of the stack.
