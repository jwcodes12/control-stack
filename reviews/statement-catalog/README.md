# Lean statement catalog review guide

The root file LEAN-STATEMENTS-NORMAL-FORM.md contains all source-indexed Lean theorem/lemma statements, excluding proof bodies. To regenerate, run python3 tools/build_statement_catalog.py; to check drift, append --check.

This is source-normalized syntax, NOT the elaborated kernel theorem type. Reviewers must inspect namespace/section parameters, definitions, coercions, adversarial capabilities, the exact observation boundary and intended real-world correspondence.

Focus first on F1/F3 full mediation, F4 hash contents, F5 trusted metering, F7 nonce and signers, F2 complete receiver observations, F6 monitoring premises and F8 global composition.
