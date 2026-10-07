# Fidelity audit (orchestrator): SANDBOX2F1, action layer step 1b (the corrected sandbox fix)

Statement: `ledger/SANDBOX2.lean` (frozen 094db3d3379a). Model: the PL_SANDBOXF1 mount table (`effective` = the last
covering mount wins; `WritesHost`, `ReadsHost`, `hiddenDirs`, `mathlibProj`), unchanged. Source: the writable-root
policy modelled in SANDBOXF1, and the SANDBOXF1 proposed fix.

## Correspondence
| object | model | note |
|---|---|---|
| SANDBOXF1's proposed fix | `fixedPolicy W stateDirs`: ro root, tmpfs scratch root, scratch bind, **hiding tmpfs, then state binds**, ro Mathlib | as frozen in SANDBOXF1 |
| corrected fix (this CID) | `fixedPolicy2 W stateDirs`: ro root, tmpfs scratch root, scratch bind, **state binds, then hiding tmpfs**, ro Mathlib | in bwrap terms: `--ro-bind / / --tmpfs /var/tmp --bind W <temporary path>`, then `--bind d d` for each state dir, then `--tmpfs H` for each hidden dir, then `--ro-bind MATHLIB MATHLIB` |
| `hiddenDirs` | the 11 modelled hidden directories (several are subdirectories of CLI state directories, e.g. session logs) | hidden FILES are still omitted, as in SANDBOXF1 |
| state directories | universally quantified `stateDirs` in (b) and (c) | which directories a given CLI needs is not fixed by the theorem; the Witness instantiates one CLI state directory |

## Conjuncts
- **(a)** With a CLI state directory declared that is an ancestor of a hidden subdirectory (its session logs),
  SANDBOXF1's fixed policy lets a sandboxed read of a file in that subdirectory resolve to the host path, although the
  writable-root policy hides it.
  - This formalises Reviewer B's final-review finding. It is a **regression of the proposed fix**: the writable-root
    policy has no state binds.
  - Faithful: a CLI's own state directory is the natural one to declare, and its session-log subdirectory is among the
    hidden directories.
- **(b)** Under `fixedPolicy2`, for every scratch W, every list of state directories, every host-permission predicate
  and every path, a host write lands inside W or inside a declared state directory. Faithful. The ordering change does
  not affect it (it held for `fixedPolicy` too).
- **(c)** Under `fixedPolicy2`, for every W under the scratch tmpfs root and **every** list of state directories, a
  sandbox read that resolves to a host path inside a hidden directory lands inside the read-only Mathlib re-bind.
  - The order is load-bearing: (a) shows the conclusion fails for the old order.
  - The `["var","tmp"] <+: W` hypothesis is needed and realistic: the harness creates scratch directories under the
    scratch tmpfs root.
  - The Mathlib exception is intentional (provers compile against it read-only). It lies inside a hidden directory,
    so it is an explicit, read-only hole.
  - Side effect, not stated as a theorem: a hidden subdirectory of a declared state directory becomes a tmpfs, so the
    CLI's writes there are discarded, exactly as under the writable-root policy.
- **Witness.** With one CLI state directory declared, the corrected policy still lets the CLI write a credential file
  in it and the prover write scratch, and still lets Mathlib be read. So (b) and (c) are not bought by blocking the uses
  the harness needs. The Witness does not show that any real CLI works under the fix; that is outside the model.

## Boundary assumptions (stated in the docstring, inherited from SANDBOXF1)
- These are statements about modelled pathname resolution.
- Out of model: hard links, symlinks and other aliases; `/proc/<pid>/root` (needs `--unshare-pid`); network and
  other side channels.
- Hidden files are omitted.

**Novelty.** None as mathematics: list-prefix reasoning about mount order. The value is that the proposed fix from the
previous step is corrected, and the corrected version is machine-checked for every choice of state directories.
General lesson: in a read-only-root policy, writable state-directory binds must come BEFORE the hiding tmpfs mounts,
otherwise a state directory that is an ancestor of a hidden directory re-exposes it.
