# Theorem registry

Generate the current declaration-level table using:

    python3 tools/theorem_registry.py > scenarios/THEOREM-REGISTRY.md

For JSON: pass --json. Use --require-complete to fail if any field is UNCLASSIFIED. The generator reads checked-in Lean sources and bundle manifests only, and will NOT compile proofs or change axiom statuses. It identifies currently registered SC-01/03/13 theorem links and explicitly marks unknown family, adversary class, premises, status and necessity witnesses elsewhere. Source declarations can be missed by regex if they use unexpected syntax; this is a review inventory, not an AST parser or Lean kernel proof.
