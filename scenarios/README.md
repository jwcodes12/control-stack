# Scenario bundles (non-deployment artifacts)

Machine-readable active bundles:

- [SC-01](SC-01/) — exact-message recovery in a fixed five-episode repair task; historical single-host side-channel hypothesis refuted and VM usefulness gate failed.
- [SC-03](SC-03/) — immediate-peer egress confinement in the test fixture, not confidentiality.
- [SC-13](SC-13/) — narrow trusted-dispatch audit preservation, not universal logging protection.
- [SC-27](SC-27/) — narrow evidence/audit integrity reuse of SC-13; manifest tamper resistance remains an open requirement.

Other `SC-XX/draft.md` files are SPECIFICATIONS ONLY; no theorem
verification, runtime boundary, or assurance status is implied.

Each active bundle holds a JSON-subset YAML `scenario.yaml`, a Lean import/axiom
replay `claim.lean`, policy reference, correspondence table, pinned evidence
manifest, result note, and negative-test index. Original source implementations
and receipts stay in their legacy paths to avoid breaking imports, CI and
historical SHA references.

```sh
python3 tools/check_scenario.py --all                 # static only
python3 tools/check_scenario.py scenarios/SC-01       # static only
python3 tools/check_scenario.py scenarios/SC-03 --verify-proofs # Lean only; requires built .olean imports
python3 tools/build_registry.py                       # generated inventory
python3 tools/build_status.py                         # generated synopsis
```

The checker never starts scenario experiments. A zero exit code means
**schema and pinned evidence consistency** (plus optional Lean replay), NOT
that its claim is applicable or deployment-assured. Failure includes missing
required fields, symlinks, digest changes, absent named assumptions, incomplete
axes and unsupported status promotions. Use the printed blockers and separate
assurance review. `--require-assured` intentionally fails: this tool is not
authorized to approve its own case.

A future v2 may add signed verifier attestations with exact CI provenance and a
distinct trusted promotion authority. Do not label recorded proof results as
replayed in the current invocation.
