# Conservative theorem-scope annotations (2026-10-08)

**These are human-readable source-level candidate scopes, not independent reviews.** Source-level review added 30 manually inspected headline declarations while retaining `SOURCE_ONLY` status. Existing ten historically recorded entries were not rewritten. All remaining unclassified entries retain `UNKNOWN` rather than a guessed adversary model or vague assumption presented as proof.

This repository has 860 lexical declaration entries, including numerous technical/math support lemmas, which need not independently define a security adversary. An `UNKNOWN` adversary means **not reviewed for composition**, not that the Lean kernel rejected the proof. The new entries preserve concrete premises, intended F1–F8 family and relevant SC identifiers where explicitly documented. Scenario links are candidates for review, not a guarantee of concrete runtime refinement.

**Review gate:** before composing any theorem into a security claim, a separate reviewer must compare the fully elaborated statement and quantifier order with (1) the concrete threat, (2) the stated adversary taxonomy, (3) model-to-runtime correspondence, (4) the actual observation interface and (5) the claimed usage. Record independent review evidence rather than promoting `SOURCE_ONLY` based on this mapping. Proof compilation is distinct from statement fidelity and independent applicability.

The registry is still mechanically source-derived; `python3 tools/build_registry.py --check` must pass after annotation edits. Annotation values do not change executable proofs, frozen preregistrations or evidence receipts.
