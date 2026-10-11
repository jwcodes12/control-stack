# Plain-English statements: template (one block per theorem)

### `<fully qualified Lean name>`  — `<file>:<line>`
- **Says (plain English):** 1–3 sentences a careful non-Lean reader can check. Name every notion used (what is a "gate", a "lease", a "budget"). No symbols.
- **Under these hypotheses:** every hypothesis of the theorem, in English, including ones hidden inside definitions the statement unfolds (structure fields, `Valid`/`Coherent`/`Wf` predicates). Say which are assumptions about the *world* (not provable in Lean) versus just conditions on the model.
- **Does NOT say:** the 1–3 most likely over-readings (what a reader might think it shows but it does not).
- **Kind:** one of `general theorem` | `finite computation (decide/native)` | `witness / non-vacuity example` | `negative control (shows a weakened model fails)` | `refinement/bridge` | `definitional/trivial`.
- **Non-vacuity:** how you know the hypotheses can all hold at once (name the Lean witness/example if there is one, else say `NOT SHOWN`).
- **Read depth:** `full` (read the statement and every definition it depends on) or `partial` (say which definitions you did not read).
