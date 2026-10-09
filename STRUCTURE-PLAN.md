# Remaining structure and assurance work (updated 2026-10-08)

The architecture from the previous structure plan is integrated on `structure-merge-20261008`. This is **not** a new proof or deployment certification. Canonical links: [ROADMAP.md](ROADMAP.md), [THEOREM-REGISTRY.md](THEOREM-REGISTRY.md), [scenarios/INDEX.md](scenarios/INDEX.md), [comparison.md](reviews/structure-merge/comparison.md).

## Integration acceptance performed (2026-10-08)

GitHub Actions [#37870787641](https://github.com/jwcodes12/control-stack/actions/runs/37870787641) passed the pinned Lean root build (3,743 jobs), all 28 scenario Lean claim elaborations (8 standard-only axiom reports), registry/status drift checks (860 indexed declarations), 18 checker mutation tests and 4 certifier tests. The unchanged SC-01 case replay passed steps 1–4; its old-host OpenSSL binding mismatch was correctly isolated at step 5. This closes the *build/structural verification* work items, not the experimental or deployment-proof obligations. See [validation report](reviews/structure-merge/hardening-validation.md).

## Still missing before deployment assurance

1. **CLOSED for this CI revision:** clean Lean build and scenario-claim elaboration / printed standard-axiom replay. Historical receipts remained frozen. No unknown/unprinted theorem was silently upgraded.
2. **CLOSED for this CI revision:** unchanged SC-01 phases 1–4 and `test_ctrlcert.py`. Host-bound OpenSSL cache receipt at phase 5 remains a documented, expected non-portable binding.
3. **CLOSED for this CI revision:** checker, negative tests, registry and scenario index passed; CI run logs provide provenance for these checks.
4. The inventory is lexical and most declarations have `UNKNOWN` adversary and `UNMAPPED` premises. Review and classify all meaningful theorem statements against [ADVERSARY-CLASSES.md](ADVERSARY-CLASSES.md) before composing results. Lexical registration is not namespace-resolved proof checking.
5. The hardening branch now has an explicit usefulness field per premise and six required scope axes in all 28 manifests. Still needed: independently attested provenance, stronger links between each premise, its falsifier, an executed negative test, and explicit reviewer decisions. Never elevate self-declared receipts to `RUNTIME_VALIDATED` or `DEPLOYMENT_ASSURED`.
6. SC-01: decide hardware isolation vs separately preregistered deadline amendment; repeat only after the owner decision. SC-03: assess permitted deputies and all-destination process attribution; SC-13: check universal mediation and dispatch control; SC-27: build independently rooted evidence/attestation rather than treating an audit theorem as an attestation proof.
7. Fill 25 draft scenarios with narrow falsifiable theorems, credible test fixtures, and honest-task baselines before promoting them from DRAFT. No runtime or negative experiment was performed by the structure merge.

## Still missing theory

- **Partially closed by CI #37877045361:** Lean now proves HALT is absorbing and freezes effects *if a trusted HALT is delivered within an explicit finite bound*, plus a no-delivery counterexample. Still missing: an independent scheduler fairness guarantee, real runtime halt delivery and refinement/correspondence.
- General audit-bound prefix/truncation lemma and a positive false-positive-budget policy.
- Tightness of the leaky audit instance `LeakWitness` (the original text explicitly says the equality is unproved).
- Actual shared-state runtime correspondence and confused-deputy prevention; C's `GateComposition` counterexample shows a gap, not a full enforcement mechanism.
- Policy integrity enforcement outside the Lean transition model; `PolicyTamper` makes the write-authority assumption explicit but cannot attest the OS.

Original preregistrations `PREREG-*.md` and evidence receipts are frozen and were not edited. New *editable* templates and drafts are consolidated under [prereg/](prereg/). The immutable historical root files remain an archival exception.
