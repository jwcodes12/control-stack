# ROADMAP: control-stack status (kept current; last updated 2026-10-07, session 3)

What is done, what is in flight, and what is left. Per-result detail (assumptions, scope, review history) is in
[STACK.md](STACK.md); this file is the one-page plan.

Status legend:
- ✅ **verified**: a frozen ledger statement whose proof passed the Lean gate (standard axioms only), after a red team
  by two foreign model families and an orchestrator fidelity audit;
- ✅ **proved**: a VCVio-level file checked with `lake env lean` and `#print axioms` (not ledger-gated);
- 🔄 in progress;
- ⏳ planned;
- 🔒 blocked on a decision by John.

## 1. Completed

### Layer 1: collusion (untrusted monitoring with honeypots and a mediator)
| item | what it gives | status |
|---|---|---|
| UMHSF1 | testing core: hockey-stick/TV bounds, data processing, decoder floors, maximal leakage | ✅ verified |
| UMSURVF1 | honeypot-test survival = binomial CDF; first-moment bounds | ✅ verified |
| UMPROTF1 | main protocol bound for every colluding pair: (1 − r) + r·L·(n_s+1)/(n_h+1) | ✅ verified |
| UMSTRATF1 | stratified per-class honeypots: no class-count factor at fixed per-class budget | ✅ verified |
| UMNOGOF1 | rich decodable mediators lose against every iid honeypot law | ✅ verified |
| UMLOWERF1 | converse for nonadaptive test designs: budget ∝ number of decodable classes | ✅ verified |
| UMADAPTF1 | converse for ADAPTIVE testers, t(1 − tn/k); the nonadaptive formula provably fails for adaptive testers | ✅ verified (session 3) |
| UMUSEF1 | honest availability identities; mimicry constraint; Cantelli slack costs | ✅ verified |
| UMDEFERF1 | audit-then-defer: needs a uniform stopping hazard; no-go without one | ✅ verified |
| UMCERTF1 | certificate form: exact one-shot reduction, Lean-checkable grid certificates (0.154 → 0.07 certified), exactness results | ✅ verified (session 3) |
| CANONF1 | a verified canonicaliser (toy language) as a concrete trusted mediator | ✅ verified |

### Interface level (VCVio operational games)
| item | what it gives | status |
|---|---|---|
| `Spike` | TV bound for arbitrary `ProbComp` distinguishers | ✅ proved |
| `HoneypotBridgeProof` | the honeypot test as a crypto-style game is exactly binomial | ✅ proved |
| `RefinementProof` | trace-level protocol game = the core recursion; end-to-end bound | ✅ proved |
| `OutcomeProof` | five-outcome game; honest-completion bridge to UMUSEF1; Pareto identity | ✅ proved (session 3) |

### Layer 2: actions (first step)
| item | what it gives | status |
|---|---|---|
| SANDBOXF1, SANDBOX2F1 | mount-table model of a bubblewrap sandbox: the writable-root weakness and the corrected bind order | ✅ verified (model theorems; nothing deployed) |

## 2. In flight (direction A: trusted monitoring with a certificate checker)
| item | what it gives | status |
|---|---|---|
| TMCERTF1 | certificate checker for finite stateful control games: sound against every history-dependent Red and rectangular model uncertainty; tightness; usefulness; a proved rational checker (`decide +kernel`); hull lemma; deployment through an abstraction | 🔄 two design-review rounds done; red team: one family passed, second pending; proof written (448 lines, passes a dry-run gate) |
| TMGACF1 | Games for AI Control (2409.07985) as a certified instance: exact bridges to its safety and usefulness recurrences; fixed-rate bounds; exact separation: constant-rate Red 13/50 vs round-index-only Red 11/32 (= full information) vs coin-count-only Red 9/32 | 🔄 red team pending; prover running |
| GitHub export | private repo `jwcodes12/control-stack` | ✅ first snapshot pushed; 🔄 refresh after TMCERT/TMGAC |

## 3. Next (ranked)
1. ⏳ **Certify a realistic trusted-monitoring configuration.** Rational ROC enclosures from finite samples
   (simultaneous confidence bands), discretised thresholds and ties, an interval uncertainty set for TMCERT, and a
   GAC-scale certificate (100 problems, 2 coins) run through the checker. Output: certified risk against a memoryless,
   a clocked and a full-information Red for the same Blue policy. This is the step a lab could actually use.
2. ⏳ **Parameter-Lipschitz lemma**: from a finite grid of models to a whole confidence box.
3. ⏳ **Composition of trusted and untrusted monitoring** (the earlier N1 results with UMPROTF1): a min, not a product,
   absent conditional independence.
4. ⏳ **Game-level (VCVio) versions** of soft slack, the hockey-stick form, the stratified design and the defer variant.
5. ⏳ **Sharper adaptive converse**: the balanced bound (t/k)[(k − a)(1 − t)^q + a(1 − t)^{q+1}], numerically equal to the
   optimal adaptive tester under the acceptance contract.
6. ⏳ **Usefulness checker**: a rational `checkUseQ` with a soundness bridge, mirroring the risk checker.

## 4. Open assumptions (what the stack does NOT give)
Every guarantee is conditional on these. None is discharged by anything here:
- the mediator's domination constant L (or δ), and honeypot constructibility and coverage (A9);
- worst-case audit recall r (A6);
- the scaffold properties: fresh stateless monitor calls, complete views, test before deployment, absorbing shutdown
  (A1–A4, A11);
- for TMCERT, row coverage of the concrete deployment (Abs). An average ROC estimate does not discharge it.

## 5. Needs John 🔒
- **Scaffold enforcement**: turn A1–A4/A11 into runtime checks or verified code (stateless calls, no clock exposure,
  test before deploy, absorbing shutdown). It touches deployment.
- **Sandbox fix**: deploying the corrected bind order (SANDBOX2F1) in the research harness.
- **Human expert review**: one control researcher reading STACK.md. All review so far has been model-based.
- **Visibility**: the GitHub repo is private; making it public is a separate decision.

## Maintenance
Update this file whenever a row changes status: verified, frozen, started, or dropped. Also update the matching row in
STACK.md, and note the change in HISTORY.md when a new snapshot is exported.
