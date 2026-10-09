# Independent kernel replay and specification-fidelity witness report

**Date:** 2026-10-09. **Repository:** `jwcodes12/control-stack`.
**Source under review:** `083874048518b68d754f0c392ad0cb84f01174ba` (original `main` source).
**Audit branch:** `fidelity-kernel-20261009`. This is supplemental evidence for
[`english-lean-fidelity-audit.md`](english-lean-fidelity-audit.md), not a new deployment assurance claim.

## What was checked

All original source modules under `ControlStack/`, `proofs/`, `ledger/`,
`ControlStack.lean`, and pinned build definitions are unchanged from the source
commit. The GitHub Actions replay performs this file-by-file diff verification
against the pinned commit before running.

- **Interface-level toolchain:** `leanprover/lean4:v4.34.0`. `lake exe cache get`,
  `lake build`, and `lake env lean reviews/fidelity-repro/Elaboration.lean`.
  The elaboration probe prints actual theorem declarations with implicit
  binders exposed and their axiom dependencies. **Source build and elaboration
  probe passed** in [interface CI run 37887000889](https://github.com/jwcodes12/control-stack/actions/runs/37887000889);
  that run's overall status is failure solely because the separate reproduction
  file had one unresolved finite proof obligation.
- **Ledger toolchain:** `leanprover/lean4:v4.35.0-rc3`. The repository's
  `ledger-check/check.py --emit` assembles original statements, transitive
  proof dependencies, claim proofs, and witness proofs for UMPROTF1, UMADAPTF1,
  UMADAPTF2, UMCERTF1, and TMCERTF1. Their fully elaborated `Claim` and
  `Witness` records and `#print axioms` outputs were printed using pinned
  Mathlib. **All five claims and five witnesses passed**, with only
  `propext`, `Classical.choice`, `Quot.sound` as reported axioms.
  [Successful ledger CI run 37887000866](https://github.com/jwcodes12/control-stack/actions/runs/37887000866).

The first attempts failed due to unsupported pretty-printer settings in our
new probe files, not due to source theorem errors. Those settings were removed
and the interface elaboration and ledger jobs were rerun successfully. This
distinction matters: a failed harness is not evidence of a bad theorem.

## Selected elaborated theorem interpretation

| Lean declaration | Consequential elaborated premise / conclusion | Fidelity implication |
|---|---|---|
| `ControlStack.Gate.Spec.trace_safe` | Takes `S : Spec G` and proof `S.Inv s`; `Spec` itself includes `step_inv`, `log_prefix`, `inv_ok`. | It preserves a supplied log invariant, not a universal external-effect guarantee. |
| `ControlStack.GatewayCore.core_bound` | Finite seed/secret/event/view spaces, `IsDist` encoder/decoder/seed, decoder receives only `finalView (runG ...)`. | Extra receiver observations require a separate full-observation proof. |
| `ControlStack.SafetyCaseSC01.sc01_case` | A conjunction: conditional side-mass security; binomial threshold; endpoint inequalities; view cardinalities; restore-free charge bound. | It is not yet a common instantiated runtime process theorem. |
| `ControlStack.Leakage.audit_leak_bound` | Uses `survInd` on a finite attack/audit transcript with schedule support, consistency and dominating leak kernel. | Surviving all audits is not synonymous with preventing harm before detection. |
| `ControlStack.GateComposition.shared_invariants` | Assumes `∀ x a, P x → Q x → P (step x a) ∧ Q (step x a)`. | A joint-step invariant must be separately established for actual combined operations. |
| `ControlStack.Compose.composedEndToEnd` | The conclusion concerns `composedGame`, defined with independent sampled `jointView M T`, under per-bad `hrec`, `htm`, `hdom`. | Arbitrary correlated joint monitors do not inherit its factorization. |
| `PL_UMADAPTF2.Claim` | Premise `PL_UMLOWERF1.Setup`; then existence of a decoder/classifier with advertised properties. | Not universal over mediators violating Setup. |
| `PL_TMCERTF1.Claim` | Premises `AdmKNonneg`, `RiskCertUpTo`, `IsPolicy`, `SelectorUpTo` (and in abstraction forms, coverage premises). | Finite-game certificate, not proof that deployed transitions satisfy the certificate. |

The `#print axioms` output for the selected interface statements likewise
contained no nonstandard axiom. Notably, `GateComposition.shared_invariants`
was reported as using **no axioms**. These outcomes verify proof dependencies;
they do not automatically verify the English specification or deployment mapping.

## Explicit model-theoretic witnesses

The isolated `reviews/fidelity-repro/Countermodels.lean` is designed to compile
against the original `ControlStack` modules without changing them. These are
**counterexamples to over-strong interpretations**, not to the Lean theorems.

- **F01 unlogged harm:** `St = Bool`, `Op = Bool`, `Eff = Unit`;
  `step s a = a`, `effects s = []`, `Inv = True`, `ok = True`.
  All `Spec` requirements hold, and `Spec.trace_safe` applies, while a trace
  from `false` with action `true` reaches a hazardous state unrepresented
  in the logged effects.
- **F06 harm before catch:** one round, `N = B = k = 1`,
  schedule `{0}`, and one transcript event `(attack = true, leak = (), caught = true)`.
  `survInd = 0`, since the one attack is audited. An independent
  irreversible-effect indicator can nevertheless be `true` when attacks
  commit before verdict delivery.
- **F12 joint sampling:** independent fair Boolean monitor outcomes give
  `P(both pass) = 1/4`; coupling the same fair marginals by a common coin gives
  `P(both pass) = 1/2`. Thus the product-law factorization is not valid
  from marginals alone. The repository theorem explicitly specifies product
  sampling and is not contradicted.

The first two witnesses compiled and emitted only standard axioms in
[interface CI run 37887723710](https://github.com/jwcodes12/control-stack/actions/runs/37887723710).
The third had one remaining decidable finite-cardinality proof obligation in
that run; the corrected source is in the later branch commit. **Do not call the
combined countermodel suite PASS until a green CI run establishes it.**

## What remains unestablished

This replay is **not** an exhaustive re-review of 865 declarations, a
complete formal extraction of implicit binders for every primitive, an
attestation of actual receiver observations, a proof of exclusive mediation
of real effects, or a proof of F1–F8 end-to-end refinement. No practical
catastrophe bound is promoted by these checks.

**Top assurance repairs remain:** (1) OS-level and deputy-inclusive exclusive
mediation plus causal commit ordering; (2) full receiver observation refinement
for SC-01; (3) a harm-before-catch, pre-effect audit theorem; (4) a single
shared-state F1–F8 semantics with checked joint invariants; (5) durable,
trusted clock/usage/identity anchors. The original audit's corrected English
claims remain the appropriately limited assurance statements.

## Reproduction commands

```sh
git fetch origin
git switch fidelity-kernel-20261009
git diff --name-only 083874048518b68d754f0c392ad0cb84f01174ba HEAD -- ControlStack ControlStack.lean proofs ledger lakefile.lean lean-toolchain
# expect empty output: original source unchanged

lake exe cache get
lake build
lake env lean reviews/fidelity-repro/Elaboration.lean
lake env lean reviews/fidelity-repro/Countermodels.lean

cd ledger-check
lake exe cache get
python3 check.py --emit /tmp/fidelity-ledger UMPROTF1 UMADAPTF1 UMADAPTF2 UMCERTF1 TMCERTF1
# append #print PL_<CID>.Claim, #print PL_<CID>.Witness,
# and #print axioms gate_claim/gate_witness; run each with lake env lean
```

Proof types and axiom output can be retrieved from the linked GitHub Actions
job logs; the workflow stores the plain probe output as build artifacts.
