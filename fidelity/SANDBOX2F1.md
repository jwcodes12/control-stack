# Fidelity audit (orchestrator): SANDBOX2F1, action layer step 1b (the corrected sandbox fix)

Statement: `ledger/SANDBOX2.lean` (frozen 094db3d3379a). Model: the PL_SANDBOXF1 mount table (`effective` = the last
covering mount wins; `WritesHost`, `ReadsHost`, `hiddenDirs`, `mathlibProj`), unchanged. Source policy:
`~/research/proofledger/harness/dispatch.py::sandbox()` as of 2026-10-07 (still the current, unfixed policy), and the
SANDBOXF1 proposed fix.

## Correspondence
| object | model | note |
|---|---|---|
| SANDBOXF1's proposed fix | `fixedPolicy W stateDirs`: ro root, tmpfs /var/tmp, scratch bind, **hiding tmpfs, then state binds**, ro Mathlib | as frozen in SANDBOXF1 |
| corrected fix (this CID) | `fixedPolicy2 W stateDirs`: ro root, tmpfs /var/tmp, scratch bind, **state binds, then hiding tmpfs**, ro Mathlib | bwrap would be `--ro-bind / / --tmpfs /var/tmp --bind W /var/tmp/work` then `--bind d d` for each state dir, then `--tmpfs H` for each hidden dir, then `--ro-bind MATHLIB MATHLIB` |
| `hiddenDirs` | the 11 entries of `HIDE_DIRS` | checked against dispatch.py today: identical list. `HIDE_FILES` (~/.codex/history.jsonl) is still omitted, as in SANDBOXF1 |
| state directories | universally quantified `stateDirs` in (b) and (c) | the actual CLI needs (e.g. ~/.codex for auth.json refresh, ~/.gemini) are not fixed by the theorem; the Witness instantiates ~/.codex |

## Conjuncts
- **(a)** With ~/.codex declared as a state directory, SANDBOXF1's fixed policy lets a sandboxed read of
  `~/.codex/sessions/s.jsonl` resolve to that host path, which is hidden under the current policy.
  - This formalises Sonnet's final-review finding. It is a **regression of the proposal, not of the deployed policy**:
    the deployed policy has no state binds.
  - Faithful: ~/.codex is the natural state directory to declare, and ~/.codex/sessions is in `HIDE_DIRS`.
- **(b)** Under `fixedPolicy2`, for every scratch W, every list of state directories, every host-permission predicate
  and every path, a host write lands inside W or inside a declared state directory. Faithful. The ordering change does
  not affect it (it held for `fixedPolicy` too).
- **(c)** Under `fixedPolicy2`, for every W under /var/tmp and **every** list of state directories, a sandbox read that
  resolves to a host path inside a hidden directory lands inside the read-only Mathlib re-bind.
  - The order is load-bearing: (a) shows the conclusion fails for the old order.
  - The `["var","tmp"] <+: W` hypothesis is needed and realistic: `dispatch.py` puts scratch under /var/tmp/pl-*.
  - The Mathlib exception is intentional (provers compile against it read-only). It is inside the hidden
    ~/research, so it is an explicit, read-only hole.
  - Side effect, not stated as a theorem: a hidden subdirectory of a declared state directory (e.g.
    ~/.codex/sessions) becomes a tmpfs, so the CLI's writes there are discarded. This is the same as today.
- **Witness.** With ~/.codex declared, the corrected policy still lets the CLI write ~/.codex/auth.json and the
  prover write scratch, and still lets Mathlib be read. So (b) and (c) are not bought by blocking the uses the
  harness needs. The Witness does not show that the CLIs work under the fix; that needs the live compatibility test.

## Boundary assumptions (stated in the docstring, inherited from SANDBOXF1)
- These are statements about modelled pathname resolution.
- Out of model: hard links, symlinks and other aliases; `/proc/<pid>/root` (needs `--unshare-pid`); network and
  other side channels.
- Hidden files are omitted.

## Status of the system claim
- Not deployed, and no canary test has been run. Deploying `fixedPolicy2` needs John's OK, plus a CLI
  compatibility test that establishes which state directories codex/agy/claude actually need, plus `--unshare-pid`.

**Novelty.** None as mathematics: list-prefix reasoning about mount order. The value is that the proposed fix from the
previous step is corrected before anyone deploys it, and the corrected version is machine-checked for every choice of
state directories.
