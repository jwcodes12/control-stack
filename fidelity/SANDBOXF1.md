# Fidelity audit (orchestrator): SANDBOXF1, action layer step 1 (a bubblewrap sandbox policy for untrusted provers)

Statement: `ledger/SANDBOX.lean`. Source policy: a research harness's bubblewrap invocation for untrusted provers, as
of 2026-10-07, before any fix. The concrete path lists in the Lean model (hidden directories, the Mathlib project, the
toolchain path) are instances; the theorems' content is the mount-order lesson, not the particular paths.

## Correspondence to the policy
| policy | model |
|---|---|
| `--dev-bind / /` | `.bind [] [] .rw` (dev-bind and bind are both read-write binds; device-node semantics are not modelled) |
| `--tmpfs /var/tmp` | `.tmpfs ["var","tmp"]` (the scratch tmpfs root) |
| `--bind W <temporary path>` | `.bind W ["var","tmp","work"] .rw` |
| `--tmpfs d` for each hidden directory d (if it exists) | `hiddenDirs.map .tmpfs`. All are assumed to exist; a missing dir only removes a mount, and the property shapes are unaffected for paths under it, since there is nothing to hide |
| `--bind W/.empty F` for each hidden file F | **omitted**. A read-only empty file over one path; it does not affect (a) or (b), and (c) is stated for hidden *directories* |
| `--ro-bind MATHLIB MATHLIB` | `.bind mathlibProj mathlibProj .ro` |
| mount order = argument order; the later covering mount wins | `effective = (filter (tgt is an initial segment of p)).getLast?` |
| host permission of the invoking user | `canWrite` predicate. In (a) it is instantiated as "inside home or the scratch tmpfs root"; in (b) it is universally quantified |

## Conjuncts
- **(a)** For every scratch W under the scratch tmpfs root, a sandboxed process can write a host path inside the
  toolchain directory (a fixed toolchain path under the modelled home directory).
  - This is a **counterexample to the policy's intent "writable scratch only"**. If an unsandboxed checker later runs
    the toolchain from that directory, a sandboxed process could replace the toolchain the checker trusts.
  - Faithful as a model fact. Whether a real bwrap invocation allows it also depends on host permission bits, which
    the model represents only through `canWrite`. The theorem is about the model, not a test of any running system.
- **(b)** A read-only-root policy with only scratch and declared state directories writable confines host writes to
  those, for every path and every permission predicate. Faithful.
  - Which state directories a given tool needs (for example for credential refresh) is outside the theorem.
- **(c)** The writable-root policy's hiding works as intended at the mount level. Faithful, under the named boundary
  assumption.

## Boundary assumptions (stated in the statement's docstring)
- No `/proc/<pid>/root` alias: without a PID namespace such an alias may exist. If it does, (c) fails in reality,
  outside the model.
- No network or other side channels.
- Hidden files omitted.

**Novelty.** None as mathematics. The value is a machine-checked model of a concrete policy that pins down a defect
class (a writable host root under a hiding mask) and its fix: the first action-layer row of the stack.
