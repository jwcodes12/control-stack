# SC-08 harness: application allowlisting (launcher)

This is a **defensive** reference test on one Linux host. A trusted launcher is the **only** interface through which
a benign scripted agent runs programs. It works as follows:
1. **Hash what was read:** it hashes the bytes it read from the opened program and from the opened script.
2. **Check the allowlists:** an allowlisted interpreter must come with an allowlisted script; a REPL is refused.
3. **Pin the script:** it copies the hashed bytes into a launcher-owned 0700 directory, named by their digest.
4. **Pin the interpreter:** it runs the interpreter **from the fd it hashed** (fexecve, via `os.execve(fd, …)`).

Every program is a benign script that prints a line and appends the SHA-256 of its own code to a sentinel file.

**This does not test kernel-level enforcement.** An agent with a shell could exec directly. Here the launcher is the
only interface; that is the complete-mediation premise.

The preregistration is [`prereg/SC08-EXEC-ALLOWLIST.md`](../../../prereg/SC08-EXEC-ALLOWLIST.md)
(`PREREG-SC08-EXEC-v1`). It holds the decision rules, the calibration, the re-run policy and the mapping to
`SC08Exec.lean`.

## Files

| file | role |
|---|---|
| `launcher.py` | The launcher. It hashes by fd, checks digests, pins the script copy and fexecve's the interpreter. `--check-exec-delay` is a test hook for the swap window. Controls: `--by-path`, `--no-script-check`. |
| `reconcile.py` | Checks the programs' own sentinel records (the code that actually ran) and the launcher log against the allowlist. It also has mutation self-tests. |
| `run_sc08.py` | Installs the benign scripts, runs the agent requests and the swaps, performs the H1–H5 checks and writes the receipt. |

## Hypotheses

Short form; the preregistration is authoritative.

| | condition | pass | Lean |
|---|---|---|---|
| H1 | installed scripts, an allowlisted copy in staging, a non-allowlisted script, `/bin/sh` | only allowlisted digests run, wherever they are stored | `safe_of_sound`, `sc08_safe`, `digest_design_needs_no_noexec` |
| H2 | file swapped between check and exec | the swapped content never runs | `path_allowlist_toctou_breaks` (deployed half) |
| H3 | interpreter with a non-allowlisted script, and with no script | both refused | `interpreter_loophole_breaks`, `interpreter_repl_breaks` (deployed halves) |
| H4 | 30 allowlisted runs | all succeed within L_RUN | usefulness |
| H5 | **NEGATIVE_CONTROL**: path allowlist; unchecked script and REPL | swapped or unchecked code runs and is flagged | the three `…_breaks` witnesses |

## Run

No root is needed, and the runner refuses to run as root.

```
/bin/python3 -B scenarios/SC-08/harness/run_sc08.py --kind dry --reps 5 --out /path/to/new-dir

# the single evidence run (committed, unmodified harness and prereg; CALIBRATION-STATUS: FIXED)
/bin/python3 -B scenarios/SC-08/harness/run_sc08.py --kind evidence --reps 5 --out /path/to/new-dir
```

## Host safety

- **Privileges and network:** unprivileged, with no accounts, no sudo and no TCP. Only Unix sockets (mode 0600) are
  used, in a fresh `/var/tmp/sc08-run-*` directory (mode 0700). That directory is removed at the end.
- **Programs:** every program only prints a line and appends to the sentinel file; each is killed after 10 s.
- **Self-exit and wall limit:** the launcher exits by itself after 30 s, and the run has a 115 s limit. A full run
  takes about 45 s on a loaded host.
- **Cleanup:** after every repetition, an independent `/proc` scan must find nothing, or the run aborts.
