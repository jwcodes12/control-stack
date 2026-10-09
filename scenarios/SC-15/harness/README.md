# SC-15 harness: merge gate

This is a defensive reference test on one Linux host. A disposable bare git repository holds `main`, and a benign
scripted agent pushes single-commit change branches. Separate processes:
- a reviewer and a security reviewer, which review **exact tree hashes**;
- a trusted CI, which materialises exactly that tree and runs a fixed check script kept in this harness.

The merge gate computes the **trusted** diff with git and fast-forwards `main` only when the exact tree has a
non-author review and a CI pass. If the diff touches `auth/` or `ci/`, it also needs a non-author security review.

**Nothing here says whether reviewed, tested code contains a backdoor**: that is semantic and outside this test.

The preregistration is [`prereg/SC15-MERGE-GATE.md`](../../../prereg/SC15-MERGE-GATE.md) (`PREREG-SC15-MERGE-v1`). It
holds the decision rules, the calibration, the re-run policy and the mapping to `SC15Review.lean` and
`AuthInstancesB.sc15_safe_authenticated`.

## Files

| file | role |
|---|---|
| `gitutil.py` | System `/usr/bin/git` with an isolated environment (`HOME` inside the run directory, `GIT_CONFIG_NOSYSTEM=1`), plus the trusted diff, tree, ancestry and archive helpers. |
| `ci_check.py` | The fixed CI script: every `.py` compiles, README exists, and there is no `FAIL-TESTS` marker. It never executes repository code. |
| `principal.py` | `--role reviewer`, `security` or `ci`. Each fetches the change's current commit and tree from the gate, logs its decision (fsync), and reports for exactly that tree. |
| `gate.py` | The merge gate. Reviews are accepted only from registered pids, and never from the author. Merge uses a compare-and-swap `update-ref`. Controls: `--any-review`, `--declared-paths`, `--any-ci`, `--no-distinct`. |
| `reconcile.py` | Starts from git (main's first-parent chain and reflog), recomputes each diff, and checks the principals' own logs. It also has mutation self-tests. |
| `run_sc15.py` | The agent (clone, branch, commit, push, amend), the H1–H6 checks and the receipt. |

## Hypotheses

Short form; the preregistration is authoritative.

| | condition | pass | Lean |
|---|---|---|---|
| H1 | 6 honest changes (2 sensitive), plus refusals: no security review, failing CI, self-review, no review | every commit on main has an exact-tree review, CI pass and, if sensitive, security review, all by non-authors | `sc15_safe`, `sc15_safe_authenticated`, `honest_merge` |
| H2 | amend after review and CI | refused until the new tree is reviewed and tested | `stale_review_breaks`, `ci_other_content_breaks` (deployed halves) |
| H3 | an `auth/` change declared as `app/` | still needs a security review | `declared_paths_breaks` (deployed half) |
| H4 | 10 honest changes | all merge within L_MERGE | usefulness |
| H5 | admin HALT | no merge; main does not move | `halt_freezes`, `no_halt_check_breaks` |
| H6 | **NEGATIVE_CONTROL**: stale review, declared paths, CI on other content, self-review | merged and flagged | the four `…_breaks` witnesses |

## Run

No root is needed, and the runner refuses to run as root.

```
/bin/python3 -B scenarios/SC-15/harness/run_sc15.py --kind dry --reps 5 --out /path/to/new-dir

# the single evidence run (committed, unmodified harness and prereg; CALIBRATION-STATUS: FIXED)
/bin/python3 -B scenarios/SC-15/harness/run_sc15.py --kind evidence --reps 5 --out /path/to/new-dir
```

## Host safety

- **Privileges and network:** unprivileged, with no accounts, no sudo and no network. Git uses local paths only.
- **Files:** Unix sockets (mode 0600) and the repositories live in a fresh `/var/tmp/sc15-run-*` directory (mode
  0700), which is removed at the end.
- **CI:** the CI only compiles the checked-out files; it never runs them.
- **Self-exit and wall limit:** every child exits by itself after 30 s, and the run has a 115 s limit. A full run
  takes about 60 s.
- **Cleanup:** children are killed in `finally` blocks. After every repetition, an independent `/proc` scan must find
  nothing, or the run aborts.
