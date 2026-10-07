# ROADMAP: control-stack status (kept current; last updated 2026-10-07, session 8)

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
| UMADAPTF2 | sharp adaptive converse (t/k)·[(k−a)(1−t)^q + a(1−t)^(q+1)]; strictly beats UMADAPTF1, attained at the witness instance | ✅ verified (frozen cf874653d2fa; session 8) |
| UMUSEF1 | honest availability identities; mimicry constraint; Cantelli slack costs | ✅ verified |
| UMDEFERF1 | audit-then-defer: needs a uniform stopping hazard; no-go without one | ✅ verified |
| UMCERTF1 | certificate form: exact one-shot reduction, Lean-checkable grid certificates (0.154 → 0.07 certified), exactness results | ✅ verified (session 3) |
| TMCERTF1 | finite-horizon trusted-monitoring certificate checker with rectangular uncertainty, usefulness, rational checker and abstraction interface | ✅ verified (frozen 53a3bc12f43c; session 3) |
| TMCERTUSF1 | rational usefulness-certificate checker: sound lower bound on honest reward for every admissible history-dependent selector; accepted certificates are never vacuous | ✅ verified (frozen 3b0cda8ceba9; session 8) |
| TMLIPF1 | parameter-Lipschitz certificate transfer: one-step Bellman error, transfer, grid transfer over arbitrary target sets, policy-quantified risk corollary | ✅ verified (frozen 5c844eb0129e, override; session 8) |
| TMGACF1 | GAC safety/usefulness bridges and exact separation of constant-rate, coin-count and clocked Red | ✅ verified (frozen 89331ac41986; session 3) |
| CANONF1 | a verified canonicaliser (toy language) as a concrete trusted mediator | ✅ verified |

### Interface level (VCVio operational games)
| item | what it gives | status |
|---|---|---|
| `Spike` | TV bound for arbitrary `ProbComp` distinguishers | ✅ proved |
| `HoneypotBridgeProof` | the honeypot test as a crypto-style game is exactly binomial | ✅ proved |
| `RefinementProof` | trace-level protocol game = the core recursion; end-to-end bound | ✅ proved |
| `OutcomeProof` | five-outcome game; honest-completion bridge to UMUSEF1; Pareto identity | ✅ proved (session 3) |
| `SoftSlack` | soft-slack honeypot game: exact survival, seed factorisation, end-to-end bound (1−r)+r·L·n_s/(n_h+1) | ✅ proved (session 5) |
| `SoftHockey` | hockey-stick form of the soft-slack bound: (1−r)+r·(δ+e^η·n_s/(n_h+1)) | ✅ proved (session 5) |
| `StratifiedGame` | per-class binomial survival; end-to-end (1−r)+r·L·(s_c+1)/(m+1) under classwise domination and coverage | ✅ proved (session 6) |
| `DeferGame` | audit-then-defer game equals the exact `ENNReal` recursion, and under calibrated kernels equals the frozen UMDEFERF1 `catV` (`defer_bridge`) | ✅ proved (session 7; calibration is an equality on recall, halt and service rates) |
| `DeferMono` | **monotone defer bound** (`defer_mono`): recall ≥ r, halt hazard ≥ η and service catch ≥ a imply operational catastrophe ≤ ledger `catV`; with `defer_bridge` the bound is exact under calibration | ✅ proved (session 8) |
| `ComposeGame` | trusted + untrusted monitoring in one game; fresh trusted coins make the misses multiply: (1 − r) + r·τ·L·(n_s+1)/(n_h+1); tight at n_h = 0 | ✅ proved (session 8) |
| `ComposeAvg` | composition for any joint kernel (`composedJ_end`) and with the population-average trusted miss τ̄ = 1 − TPR (`composedPop_end`), so certified ROC bands plug in | ✅ proved (session 8) |
| `ComposeBlindSpot` | **negative result**: population-average trusted miss 1/1000, yet a content-adaptive Red reaches catastrophe w.p. 1; sampled ROC data cannot certify the per-submission τ | ✅ proved (session 8) |

### Empirical certification (preregistered; Lean-checked certificates)
| item | what it gives | status |
|---|---|---|
| LaStraj 2.0 (`PREREG-LASTRAJ.md`) | 30 honest / 17 attack; pipeline end to end | ✅ done; vacuous (≈1 at 100 tasks): too few attacks; Lean passes |
| LASR held-out test split, all 42 conditions (`PREREG-LASR-TEST.md`) | family-wise 95% over every condition | ✅ done; closed-source monitor 0.63–0.83 at 100 tasks, 0.05–0.22 per task; open-source ≈1; Lean checks running |
| LinuxArena 217, cutoffs 7/3 (`PREREG-LINUXARENA.md`) | 250 honest / 150 attack, public task-set scores | ✅ done; per-task risk 0.115 (Opus attacker), 0.32 (Sol), but 92% of honest work deferred |
| LinuxArena 217, environment-split calibration (`PREREG-LINUXARENA-SPLIT.md`) | thresholds chosen on 2 environments, certified on 3 | ✅ done; FPR transfers (≤ 6.5%), per-task risk 0.82 (Opus): this monitor's exact safety–usefulness trade-off |
| Risk decomposition (`CERTIFICATE-DECOMPOSITION.md`, post hoc) | point estimate vs certified | ✅ done; weak monitors: the monitor is the limit; strong monitors at 100 tasks: statistical margin (needs ~1,000–3,000 attacks or predeclaring fewer cutoffs) |
| Statistical audit (`numerics/stat_audit.py`, post hoc) | duplication, epochs, clustering, matched populations | ✅ done; LASR clean (1 epoch, no duplicates); LinuxArena task ids and honest main-task scores are stripped in the public JSON (cannot audit repeats or report completion); matched-population split: TPR at ≥8 is 7/56 (band [0.04, 0.27]) vs 39/150 pooled, so detection does not transport across environments |
| Assurance manifests (`assurance/`, `tools/assurance.py`) | per-certificate theorem/data/preregistration hashes and assumption status; checker refuses to promote categories | ✅ done; 44 manifests, 0 deployment-grade |
| Held-out data search (`reviews/heldout-data-search-2026-10-07.md`) | public datasets, prior art (rocci; Gao 2026) | ✅ done |

### Layer 2: actions (first step)
| item | what it gives | status |
|---|---|---|
| SANDBOXF1, SANDBOX2F1 | mount-table model of a bubblewrap sandbox: the writable-root weakness and the corrected bind order | ✅ verified (model theorems; nothing deployed) |

## 2. In flight
| item | status |
|---|---|
| Lean checks of the 42 LASR certificates and 2 LinuxArena certificates | 🔄 running sequentially (≈5 min each) |
| GitHub export (private `jwcodes12/control-stack`) | ✅ refreshed with every session-8 result (`a8e5540`); refresh again after the Lean checks |

## 3. Next (reorganised after external review, 2026-10-07; see `reviews/external-review-2026-10-07.md`)
Goal: one end-to-end, independently checkable safety case, optimising for how much uncertainty each result removes.

| priority | work | definition of success | status |
|---|---|---|---|
| P0 | choose one concrete catastrophe and restricted deployment | explicit bad event, action space, threat model, horizon, acceptable usefulness | ⏳ |
| P0 | action gateway | every relevant tool action intercepted before execution; unauthorised actions fail closed | ⏳ (touches the agent runtime: 🔒 John) |
| P0 | implementation correspondence | runtime traces refine the Lean transition model, or remaining assumptions stated | ⏳ |
| P1 | empirical certificate validity | held-out, correctly timed measurements for matched populations; pre-action scores | 🔄 (preregistered runs done; transport and timing gaps found) |
| P1 | trusted/untrusted composition | Lean bound for the actual joint protocol incl. shared state and audit budget | 🔄 (`ComposeGame`, `ComposeAvg`, `ComposeBlindSpot`) |
| P1 | one reproducible safety case | a verifier reproduces the safety/usefulness pair and every unmet assumption | 🔄 (assurance manifests) |
| P1 | CI | fast tier (source scan, numerics, manifests) + slow tier (Lean ledger, certificates) | ⏳ |
| P2 | model coverage | multi-step attacks, stateful monitors, distribution shift, correlated failures; environment-state invariants | ⏳ |
| P3 | more mathematics | general balanced-schedule attainment (draft `ledger-drafts/UMADAPTF3-draft.lean`, shelved), sharper bounds | ⏸ demoted |
| — | human review | one AI-control researcher reads the specification and correspondence | 🔒 John |

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
