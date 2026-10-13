# Phase A (blind back-translation), 2026-10-13

Run by Sol (`codex exec -m gpt-6.1-sol`, effort high, workspace-write sandbox) in a directory that contained ONLY `input/batch.md` (the English of the 8
stale G0 claims, Says / Under / Does NOT say / Kind fields) and `defs/*.lean` (definition-only excerpts of the project's Lean files, theorems removed, the
declarations that define `Accepted` and its component checks redacted, not compilable). No originals, no compiled objects, no toolchain, no earlier results.
`back/` holds the 8 statements it wrote and `BACK-HASHES.json` (written 03:30:41 UTC before any later step). `COMMANDS.txt` is every command it ran (3: it read
the two inputs and wrote the files); `AUDIT.txt` is `tools/audit_blind_phase.py` over the full event log (0 flagged). `PROMPT.md` is the exact instruction.
Limits: the blindness of the *statements* is enforced by the directory, not by trust; the model had prior general knowledge of Lean and of this kind of project
but no memory of this repository (a fresh session). The excerpts were produced by a script (`defs/` header says what was removed) and could omit context a
reader would want; a model that sees only those cannot be said to have seen the original claims.
