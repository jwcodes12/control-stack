# Phase B progress

Done: **10/10 claims; 10/10 claim gates; 10/10 separate witness gates.**

- All ten original Phase A hashes verified, all ten back files compiled unchanged, and typed copies hashed before opening originals. No compile fixes were needed.
- Original declarations inspected, pointwise conclusions compared under shared hypotheses, and hypothesis conversions checked. No comparison uses the truth of two closed theorems to manufacture an iff.
- Verdicts: nine `EQUIVALENT`; claim 7 `ENGLISH_WEAKER` in theorem coverage, with a gated strict premise-domain certificate and pointwise conclusion iff on the common domain.
- Saved statement/proof files frozen in `PROOF-HASHES.json`; all 20 final receipt hashes match the saved files and current deterministic gate helper.
- `RESULTS.md` includes the verdict/receipt table, all ten “Does NOT say” audits, replacement English sentences, and exposed ambiguities.
- `regate.py` successfully regenerated all 20 passing receipts with exit code 0 after deleting all receipts and removing the gate directory. It uses only saved statement/proof files and the deterministic gate; it does not regenerate those source files. No temporary Lean files remain.

Not done: no requested claim is unfinished; no failed final gate remains. Initial development proof failures are retained under `development-gate-logs/` and are superseded by final receipts.

Time: started 2026-10-13 approximately 05:11 UTC; typed hashes frozen at 05:12:39 UTC; completed 2026-10-13 05:24:49 UTC (approximately 13.8 minutes).

What could not be established: no comparison certifies a real deployment's hiddenness, honest digest, truthful semantic provenance, or credential separation. Infinite hidden alphabets in claims 6/7 are outside both actual declarations. The reverse claim-7 premise conversion is false; the saved strictness certificate establishes this. No counterexample to its shared numerical conclusion is claimed.

Scope: all authored files are under `docs/lean-english/one-to-one/blind-g5n1/`; no `ControlStack/` edits, no git commands, no downloads, and no other English/comparison material was read. The wrapper relocation changed the project-root parent index and helper path as recorded in `run_gate_blind.diff`; the gate's token bans and axiom checks are unchanged.
