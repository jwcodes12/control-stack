# ROADMAP: control-stack status (kept current; last updated 2026-10-07, session 6)

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
| TMCERTF1 | finite-horizon trusted-monitoring certificate checker with rectangular uncertainty, usefulness, rational checker and abstraction interface | ✅ verified (frozen 53a3bc12f43c; session 3) |
| TMGACF1 | GAC safety/usefulness bridges and exact separation of constant-rate, coin-count and clocked Red | ✅ verified (frozen 89331ac41986; session 3) |
| CANONF1 | a verified canonicaliser (toy language) as a concrete trusted mediator | ✅ verified |

### Interface level (VCVio operational games)
| item | what it gives | status |
|---|---|---|
| `Spike` | TV bound for arbitrary `ProbComp` distinguishers | ✅ proved |
| `HoneypotBridgeProof` | the honeypot test as a crypto-style game is exactly binomial | ✅ proved |
| `RefinementProof` | trace-level protocol game = the core recursion; end-to-end bound | ✅ proved |
| `OutcomeProof` | five-outcome game; honest-completion bridge to UMUSEF1; Pareto identity | ✅ proved (session 3) |
| `SoftSlack` | soft-slack honeypot game: exact survival, seed factorisation, end-to-end bound (1−r)+r·L·n_s/(n_h+1) | ✅ proved |
| `SoftHockey` | hockey-stick form of the soft-slack bound: (1−r)+r·(δ+e^η·n_s/(n_h+1)) | ✅ proved |
| `StratifiedGame` | per-class binomial survival; end-to-end (1−r)+r·L·(s_c+1)/(m+1) under classwise domination and coverage | ✅ proved |
| `DeferGame` | audit-then-defer game equals the exact `ENNReal` recursion, and under calibrated kernels equals the UMDEFERF1 `catV` | ✅ proved (calibration is an equality on recall, halt and service rates) |
| `DeferMono` | **monotone defer bound** (`defer_mono`): recall ≥ r, halt hazard ≥ η and service catch ≥ a imply operational catastrophe ≤ ledger `catV`; with `defer_bridge` the bound is exact under calibration | ✅ proved |

### Layer 2: actions (first step)
| item | what it gives | status |
|---|---|---|
| SANDBOXF1, SANDBOX2F1 | mount-table model of a bubblewrap sandbox: the writable-root weakness and the corrected bind order | ✅ verified (model theorems; nothing deployed) |

## 2. In flight
| item | what it gives | status |
|---|---|---|
| GitHub export | private repo `jwcodes12/control-stack` | ✅ refreshed with the adaptive sharp proofport and pushed; reviewer identities anonymised |

## 3. Next (ranked)
1. 🔄 **Certify a realistic trusted-monitoring configuration.** (session 4/5: design note, synthetic fixture, exact-rational ROC-band generator, and LASR archive pipeline demonstration complete; the 100-step/two-coin interval table passes `checkRiskQ`/`checkLawfulQ`, and a 100-step, three-state, eight-model `checkUseQ` certificate gives the conditional honest-reward floor `22873/250 = 91.492` for every full-history selector. A deployment-matched, predeclared held-out sample remains.) Rational ROC enclosures from finite samples
   (simultaneous confidence bands), discretised thresholds and ties, an interval uncertainty set for TMCERT, and a
   GAC-scale certificate (100 problems, 2 coins) run through the checker. Output: certified risk against a memoryless,
   a clocked and a full-information Red for the same Blue policy. This is the step a lab could actually use.
2. 🔒 **Parameter-Lipschitz lemma**: TMLIPF1 Claim and Witness pass local gates, but review returned Reviewer A `kill` (the transfer is a direct classical Bellman-stability argument) and Reviewer C `revise` (witness/formulation drift, with a proposed repair). No restatement or freeze: the `kill` concerns the theorem's contribution, which the witness repair does not address. Any next version needs a distinct result beyond the standard simulation-lemma argument.
3. ✅/🔄 **Composition of trusted and untrusted monitoring**: `ControlStack/ComposeGame.lean` proves a product bound (1 − r) + r·τ·L·(n_s+1)/(n_h+1) for a joint protocol in which the trusted monitor has fresh coins, plus factorisation, the per-submission product lemma and a tightness witness (standard axioms). Remaining: a bridge from TMCERT/N1b certificates to the per-submission trusted miss bound τ. See [COMPOSITION-N1-UMPROT.md](COMPOSITION-N1-UMPROT.md).
4. 🔄 **Sharper adaptive converse**: `ControlStack/AdaptiveBalance.lean`, `AdaptiveGeneric.lean` and `AdaptiveUMADAPT.lean` prove the balancing inequality, optional-decoder adaptive recursion, and uniform-seed risk composition. A separate kernel-gated proofport also proves the sharper bound against the actual setup and protocol definitions with standard axioms. No frozen statement changed; the frozen theorem remains `t(1 − tn/k)`. Registering and red-teaming a separate strengthened statement remains.
5. 🔄 **Usefulness checker**: `ControlStack/UseQ.lean` has a rational `checkUseQ`, a soundness bridge from sub-solutions to expected honest reward under full-history-dependent admissible selectors, and a positive one-state witness. Claim and witness pass the ledger harness Lean gate with standard axioms; reviewer family red-team passed. The statement is attributed to reviewer family, so `Reviewer A` is not a foreign review; it remains unfrozen pending a second distinct foreign-family review. `numerics/lasr_usefulness_certificate.lean` demonstrates the checker on the current interval fixture; it does not discharge deployment sampling assumptions.

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
