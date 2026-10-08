# Scenario architecture

The original Lean/gateway/egress/auditgate code and historical assurance manifests remain at their current paths. Scenario folders are *indexed contracts*, not duplicate binaries or additional proofs. The 24 draft folders express proposed narrow properties; they do not certify deployment.

Commands:

```bash
python3 tools/check_scenario.py --all --lint
python3 -m unittest discover -s tests -p 'test_scenarios.py'
python3 tools/check_scenario.py SC-01 --verify
```

**Exit 0 for --lint means schema-valid only, never safety-verified.** --verify checks pinned hashes and optionally the original SC-01 Lean/runtime checker; exit 2 is an invalid bundle, and exit 3 is conservative incomplete assurance. No automatic deployment promotion is implemented. The SC-01 specialized checker can return zero while its measured side-channel hypothesis is refuted. The generic checker distinguishes those findings.

Proof, evidence, applicability, and usefulness are independently reported. Every scenario declares adversary class labels, explicit assumptions, a falsification route, and an unresolved correspondence boundary. Labels are not Lean theorems or a compositional subtype lattice. Preserve SC-01's failed VM usefulness gate; see [VM status](../gateway/vm/STATUS.md).
