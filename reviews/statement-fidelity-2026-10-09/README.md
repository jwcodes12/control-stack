# Statement-fidelity raw outputs (2026-10-09)

These are the inputs to [REVIEW-PACKET-2026-10-09.md](../../REVIEW-PACKET-2026-10-09.md). The packet was prepared by
a same-family model (Opus 5.5). It is **not** an independent review.

- **Commit:** `aa26511b3f18193132a6a92bb3384a1f598d3cad`
- **Toolchain:** `leanprover/lean4:v4.34.0`
- **Target source hashes:** `raw/source-sha256.txt`. They match the commit; at review time only
  `ControlStack/Core/Cert.lean`, which is not a target, was modified in the tree.

| file | what it contains |
|---|---|
| `raw/01-statements.lean` → `.out.txt` | `#check @Name` (elaborated type) and `#print axioms` for each headline theorem and its non-vacuity witness, plus `#print` of `Good`, `legal`, `full`, `Sound`, `Checks`, `init`, roles and state |
| `raw/02-definitions.lean` → `.out.txt` | `#print` of every scenario `step` and of the auxiliary predicates (`DepOk`, `ExecOk`, `ActOk`, `RelOk`, `AppOk`, `DestroyOk`, …), and the F3/F6/F2/F8 definitions |
| `raw/03-aux.lean` → `.out.txt` | the remaining auxiliaries (`survInd`, `liveInd`, `ReviewOk`, …) and the numerical example statements |
| `raw/04-witnesses.lean` → `.out.txt` | four reviewer witnesses (W1 SC-23, W2 SC-17, W3 SC-25, W4 SC-16). An **empty** `.out.txt` means everything compiled with no errors and no warnings. |

Reproduce from the repository root, one Lean process at a time:

```sh
lake env lean reviews/statement-fidelity-2026-10-09/raw/01-statements.lean
```

The files import the individual modules rather than `ControlStack`, because the root `ControlStack.olean` predated
the newest imports at review time.
