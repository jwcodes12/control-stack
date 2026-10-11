# One-to-one check: does each English statement say exactly what its Lean theorem says?

The English blocks in `part-g0.md` .. `part-g7.md` were written by Sonnet from the Lean source. A translation can be fluent and still
say something stronger, weaker or different. This protocol makes the English earn its place: each statement is **formalised again
from the English alone** and the result is **proved equivalent (or not) to the original theorem in Lean**, under the deterministic
Lean gate of `~/research/proofledger` (no `sorry`, no extra axioms, statement fixed before the proof).

## Per claim

1. **Blind back-translation.** From the English block only (the *Says*, *Under these hypotheses* and *Kind* fields), write a Lean 4
   statement `Back_<claim>` using the repository's definitions (structures, predicates, models such as `TrustedBroker.State`,
   `Deployment.IR`). Looking definitions up by name is allowed. **Do not read the original theorem's statement before the
   back-translation is written and saved.** If the English uses a notion with no Lean counterpart, record `NOT_FORMALISABLE` and say which.
2. **Equivalence.** State `Back_<claim> ↔ Orig` and try to prove it. If it fails, prove each direction separately where possible:
   - `Back → Orig` only: the English is **stronger** than the theorem (it claims more than Lean proves).
   - `Orig → Back` only: the English is **weaker** (the theorem says more than the English admits).
   - neither: **different**; give a counterexample instance or the precise difference.
   - cannot decide: `UNDECIDED` with what was tried.
3. **Gate it.** Run each equivalence proof through the proofledger gate (`harness/leangate.py`) so the verdict is derived from a
   gate pass on a frozen statement, not asserted. The gate's header is `import Mathlib` only; our theorems live in the `ControlStack`
   Lake project, so the gate needs the project root and module imports. Prefer environment configuration (`PL_LEAN_PROJ=/var/tmp/sol-deployment-slice-20261010`
   plus a small `PL_IMPORTS` list). A minimal change to the gate that adds that option is allowed; record it, keep the banned-token
   and axiom checks unchanged, and do not weaken them.
4. **Canaries.** The input set may contain statements that were deliberately made wrong. Do not look for a key; treat every block alike.

## Verdicts

`EQUIVALENT` | `ENGLISH_STRONGER` | `ENGLISH_WEAKER` | `DIFFERENT` | `NOT_FORMALISABLE` | `UNDECIDED`, each with the proof or counterexample file.
`EQUIVALENT` is only valid when the equivalence was proved through the gate.

## Output

- `docs/lean-english/one-to-one/<n>-<claim>.lean`: back-translation and proofs, one file per claim.
- `docs/lean-english/one-to-one/RESULTS.md`: table (claim, verdict, file, one-line note), and a section "Corrections to the English" (proposed replacement sentences, never edits to the part files).
- `docs/lean-english/one-to-one/PROGRESS.md`: what is done, what is not.
