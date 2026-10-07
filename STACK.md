# STACK: strategy-free (adversary-quantified) control guarantees, conditional on explicit trust hypotheses; status 2026-10-07

**Reading guide (after the final hostile review, `reviews/final-review-{sol,sonnet}.md`).**
- Every row is a *conditional* theorem about an idealised finite model. The adversary is universally quantified, which
  is what makes it capability-independent.
- The conclusions hold only under the explicit assumptions listed:
  - scaffold (fresh stateless monitor calls; the view is the complete input);
  - upfront testing and absorbing shutdown;
  - a constant audit recall r;
  - honeypot construction and coverage;
  - a certified domination constant for the mediator.
- The protocol bounds are on the **joint** event "survives the honeypot test and then causes an uncaught catastrophe",
  measured from before testing. They are not conditional on observed test success.
- None of this is a deployed-system assurance.
- **One-sided (Sonnet, final review).**
  - In the halting variant a monitor that flags everything satisfies every bound, so the upper bounds measure the
    **adversarial gain over the always-flag baseline**.
  - Usefulness is now in Lean (UMUSEF1): honest false shutdown, false halt, completion, and the obstruction
    α₀·u ≤ X for every universal certificate X at completion target u.
- **Coarse-regime caveat.** The positive results' hypotheses are satisfiable at realistic budgets only for coarse
  mediated views (k ≲ 4–8 bad classes). There, the untrusted monitor's value over a trusted class rule is *not*
  established (DESIGN §5).
- **Who must be trusted for what:**

  | quantity | what it asserts | kind |
  |---|---|---|
  | L (or δ) | Blue's honeypot generator, after mediation, spans every bad submission U could produce, up to the constant | constructibility / honeypot–U parity (A9) |
  | r | a human audit catches every bad submission U could produce, with probability ≥ r (constant r in the Lean recursion) | audit–U parity (A6, STANDING) |
  | A1–A4, A11 | fresh stateless monitor calls; the view is the complete input; upfront testing; a caught attack is absorbing shutdown | scaffold engineering, not proved |
  | κ, n_h, n_s, b | Blue's protocol parameters | trusted by construction |

Each row is a machine-checked guarantee, or a planned one. Every verified row passed:
- a red team by two foreign model families;
- the proofledger Lean gate (standard axioms only);
- an orchestrator fidelity audit (`campaigns/<C>/forms/<CID>/fidelity-orchestrator.md`).

Statement sources are in `ledger/*.lean` and the model in `DESIGN.md` (v1).

Status legend:
- **verified**: kernel-checked, frozen statement;
- **pending**: frozen or draft, unproved;
- **open**: not yet formalised.

## Layer 1: collusion (untrusted monitoring with honeypots and a mediator)

| CID | plain-English guarantee | assumptions it needs (DESIGN §2.3) | protocols it speaks to | status |
|---|---|---|---|---|
| UMHSF1 | No monitor rule can pass attacks much more often than honeypots unless the mediated attack and honeypot laws differ. Precisely: pass(attack) ≤ e^η·pass(honeypot) + hs_η, attained by some [0,1] rule. Mediation never increases hs_η. An exact-decoder content-preserving mediator cannot reduce hs_η below the content-level value. With a decoder that errs with probability ≤ γ on **every** submission, it cannot go below that value minus (1+e^η)γ. For a chosen bad set B, no law Q on views has a likelihood-ratio constant below Σ_z max_{x∈B} M(x,z), the *exponentiated* maximal leakage. The attaining Q is an arbitrary view law, not necessarily a constructible honeypot law. | finite laws | the testing core of any honeypot-based untrusted-monitoring analysis (no protocol semantics involved) | **verified** (frozen c4a262fd3de3; Sol-high + Flash pass; gate: standard axioms) |
| UMSURVF1 | The honeypot test's survival depends only on the monitor's honeypot pass rate h. Hard slack: survival = P(Bin(n_h,h) ≤ n_s) and h·survival ≤ (n_s+1)/(n_h+1). Constant schedule κ ∈ (0,1]: survival = (1−κh)^{n_h} and h·survival ≤ 1/(κ(n_h+1)), i.e. n_s/(n_h+1) for κ = 1/n_s, n_s ≥ 1. | A1–A3 (fresh contexts, iid honeypots) | Greenblatt upfront synthetic testing; LASR slack | **verified** (frozen 89139ffcfe63; Sol-high + Flash pass; gate: standard axioms) |
| UMPROTF1 | **For every colluding pair** (shared seed, stateless monitor, adaptive generator, free choice of submission): P(survive the test, then uncaught catastrophe) ≤ (1−r) + r·L·(n_s+1)/(n_h+1) when every bad submission's view is L-dominated by the mediated honeypot law. Hockey-stick and soft-slack forms also hold. The first bad submission decides, **because catching an attack is absorbing shutdown** (A11): if a caught attack were merely blocked, the bound fails (Sol: 3/4 > 1/2). The recursion uses a *constant* audit recall r; the conditional-recall refinement is open. One-shot attainment: S(h)(1−r+r·a). | A1–A11; L or δ is a hypothesis on the trusted mediator and honeypot law; r is STANDING; bounds the adversarial gain over always-flag; usefulness not formalised | *motivated by* the upfront-honeypot mechanism of Greenblatt et al. §3.4 and LASR. It is not a formalisation of LASR Eq. (1), which also has upfront audits, attack rates, defer dynamics and retraining slack, and no reduction to it is proved | **verified** (frozen 1385777cdd90; Sol-high + Flash pass; gate: standard axioms) |
| UMSTRATF1 | With a content-only mediator, m honeypots per bad class and class-aware shutdown, every colluding pair has risk ≤ (1−r) + r(s_c+1)/(m+1), with no *additional* class-count factor **at fixed per-class budget**. At a fixed total budget n_h = k·m, this is (1−r) + r·k(s_c+1)/(n_h+k), so the class count reappears. Under exact class decoding an explicit colluder attains binCDF(m,s_c,t)(1−r+rt); the counting bound itself is not claimed tight. | A1–A10; content-only M; Blue can build honeypots per class | a design variant of the halting idealisation; no named protocol | **verified** (frozen d2b4b11507cc; Sol-high + Flash pass; gate: standard axioms) |
| UMNOGOF1 | If the mediator has an exact decoder for a content class and Bad has k distinct classes, then for **every** iid honeypot law one deterministic colluding pair wins, uniformly over every shutdown schedule, budget, recall and horizon N ≥ 1, with probability ≥ (1−1/k)^{n_h}. This holds in the free-submission model; availability on an exogenous task stream is not shown. It is a finite-sample bound, not a proof that no finite domination constant exists. | free-submission model (lower bound) | why decodable mediators (e.g. CANONF1's canonicaliser) with many Red-choosable bad classes cannot get small risk from iid honeypots at realistic n_h. LLM summarisers are not proved decodable, so they are not covered as stated | **verified** (frozen d251d71f8951; Sol-high + Flash pass; gate: standard axioms) |
| UMLOWERF1 | **Design-free converse.** Take a mediator with an exact decoder and k bad submissions in distinct classes. One explicit colluding pair has risk ≥ t(1 − t·n/(k(n_s+1))) against **every** honeypot design (any joint law on n-tuples, independent of the seed) and **every** shutdown rule that tolerates n_s misses (global or class-aware), and for every r, b and N ≥ 1. The pair is a uniform seed on the k submissions; the monitor PASSes the decoded seed class w.p. t; the generator submits the seed. The decoder is fixed before the design. At t = min(1, k(n_s+1)/(2n)), risk ≥ min(1/2, k(n_s+1)/(4n)). With UMSTRATF1 (under its hypotheses), budget per distinguishable class is necessary and sufficient | free-submission model; decodable mediator (lower bound) | why honeypot budget must scale with the number of distinguishable bad classes, for every design; the matching upper bound needs UMSTRATF1's content-only and coverage hypotheses, and the 1 − r floor remains | **verified** (frozen 8415ec049329; Sol-high + Flash pass, after a revise round that fixed the strategy before the design; gate: standard axioms) |
| UMUSEF1 | **Usefulness companion and a usefulness-target obstruction.** The honest side of the same recursions: false halt = P(Bin(N, f₀) > b); honest completion = survH(α₀)·binCDF(N, b, f₀), for every valid schedule and for the class-aware product; the view-blind pair's exact risk. **D·risk = q·completion**, so any universal risk certificate X and completion target u satisfy q·u ≤ D·X, hence α₀·u ≤ X: a protocol that keeps the honest monitor's completion ≥ u cannot certify risk below u × the honest monitor's own miss rate. Also: Cantelli for both binomial tails (slack cost and sufficient slack); the honest ROC 1 − f₀ ≤ e^η α₀ + hs_η(M·μ, M·P_H), where mediation can only raise the floor; and at b = 0 the bound sharpens to L(n_s+1)/(n_h+1) | the honest half is conditional on a nominated honest rule φ₀ and a benign iid stream μ (NOT capability-free); completion is full-run availability, not task usefulness | closes the always-flag loophole of every upper bound; an instance of Games for AI Control's safety/usefulness framing | **verified** (frozen 61a4c0bdf711; v1 rejected by Sol xhigh and Sonnet; v2 → v2.1 after Sol-high revise; Sol-high + Flash pass; 573-line proof; gate: standard axioms) |
| CANONF1 | A verified canonicaliser for a toy imperative language. It preserves semantics, and its output is a unique normal form modulo for→while, `;`-association and local renaming. Laws that agree on classes become identical after mediation, so markers carried only by those freedoms are erased. | (a verified trusted component) | erases an *analogous* For/While channel in the specified toy language. LASR's Python pipeline would need a verified frontend and an observation-level theorem | **verified** (frozen d3d1dd97809f; Sol-high + Flash pass; gate: standard axioms) |

### Interface level (VCVio, `~/research/control-stack`, Lean v4.34; checked with `lake env lean` + `#print axioms`, not ledger-gated)
| file | guarantee | status |
|---|---|---|
| `ControlStack/Spike.lean` | T1 for *arbitrary* `ProbComp` distinguishers through a `ProbComp` mediator: \|Pr[D=1 ∣ mediated attack] − Pr[D=1 ∣ mediated honeypot]\| ≤ tvDist; data processing | checked, standard axioms |
| `ControlStack/HoneypotBridgeProof.lean` | The honeypot test as a crypto-style game. For arbitrary `ProbComp` honeypot law H, mediator M and monitor D (stateless, with fresh coins per call, automatically in `ProbComp`), the number of PASSes among n honeypots is exactly binomial: Pr[#PASS ≤ s] = binCDF(n, s, Pr[D passes a mediated honeypot]). This is the first operational bridge to UMSURVF1's quantity, by textually identical `binCDF` definitions across the two projects | checked (67-line proof), standard axioms |
| `ControlStack/Refinement.lean` + `RefinementProof.lean` | **Operational refinement and end-to-end bound.** The halting protocol is a trace-level `ProbComp` game: shared seed; the honeypot test (fresh calls); then deployment with an adaptive `ProbComp` generator, a fresh mediator, a stateless monitor `D ω z`, and an audit kernel `A h x z` that may depend on the history and use fresh coins; absorbing shutdown on a catch; halt on an unaffordable flag. Proved (394 lines, isolated Opus): (i) **DeployG**: P(catastrophe in deployment) = `catG` exactly, the core `cat` with the audit's actual recall function, with no hypotheses. Hence ≤ `cat` with constant r under conditional recall ≥ r, and = at exact recall. (ii) **Protocol**: the game factorises as Σ_ω Pr[ω]·binCDF(n_h, n_s, h_ω)·P(deploy catastrophe | ω). (iii) **EndToEnd**: under L-domination, every colluding pair and every audit kernel with conditional recall ≥ r has P(catastrophe) ≤ (1−r) + r·L(n_s+1)/(n_h+1). T3a and T3c were re-proved inside this project. (iv) **Attain**: a fixed-bad generator gives Σ ρ·binCDF·(1 − r + r·Pr[PASS | M x]). (v) Witness 27/256 < 1/4. Built-in, load-bearing assumptions: a stateless monitor with fresh coins (a call-counting monitor reaches 1), an audit independent of ω, test before deployment, no benign-audit false positives, rational probabilities, finite types. `cat` is linked to the ledger's `PL_UMPROTF1.cat` by textual identity only; EndToEnd does not need that link | checked, standard axioms (not ledger-gated). Design review: Sonnet (minor; about 4000 exact game-vs-recursion instances, 0 mismatches) |

## Layer 2: actions (reference monitor), first step

SANDBOXF1 models the research harness's sandbox for untrusted provers. It is *not yet* an action monitor for U's tool
calls, and it supplies no structural B̄ to layer 1 (Sonnet B5).


| CID | guarantee | status |
|---|---|---|
| SANDBOXF1 | A model of the proofledger sandbox (bubblewrap mount table). (a) The current policy does **not** confine host writes to scratch: `~/.elan` (executed by the gate) is writable. (b) A read-only-root fixed policy confines host writes to scratch and the declared state directories. (c) The current policy does hide the hidden directories, except through the read-only Mathlib re-bind. These are statements about **modelled pathname resolution**, not about host files. Hard links, symlinks and other aliases are outside the model (Sol). Boundary assumptions: no `/proc/<pid>/root` alias (needs `--unshare-pid`), no network side channels. (a) remains a counterexample inside the model. | **model theorem verified** (frozen 85a64bdfb3ce). **System claim untested**: no canary write was run. **The proposed fix as written regresses hiding** (Sonnet): state-directory binds are placed after the hiding tmpfs, so a state dir that is an ancestor of a hidden dir (e.g. ~/.codex over ~/.codex/sessions) re-exposes it. (b) is still true because it concerns writes only. Corrected in SANDBOX2F1 |
| SANDBOX2F1 | The corrected fix. (a) SANDBOXF1's proposed fix, with ~/.codex declared as a state directory, re-exposes the hidden ~/.codex/sessions (Sonnet's regression, as a counterexample in the model). (b) The corrected policy `fixedPolicy2` places state-directory binds **before** the hiding tmpfs mounts; host writes stay inside scratch or a declared state directory. (c) Under `fixedPolicy2`, hiding holds for **every** choice of state directories: a read that reveals a host path inside a hidden directory lands in the read-only Mathlib re-bind. Same model and boundary assumptions as SANDBOXF1 | **model theorem verified** (frozen 094db3d3379a; Sol-high + Flash pass; gate: standard axioms). **Not deployed**: it needs John's OK, a CLI compatibility test (which state directories codex/agy/claude need) and `--unshare-pid` |

## Existing verified results that slot into the stack (earlier sessions)
- **Trusted monitoring (Redwood):**
  - N1/N1b (`~/research/control-tree/lean/ControlTree.lean`): the audit-game structure, a single-rate saddle point,
    and a dual certificate;
  - K5: noisy clocks.
- **Observables as clocks:**
  - CLKF1/CLKF2: a visible audit counter destroys the value of upfront auditing;
  - LUREF1/LUREF2: silent failures are a clock; erase the failure feedback.

  They are the stateful-adversary caveats to A1 and A4 here. That is an informal connection; **no composition
  theorem is claimed**.

## Prior art and positioning (related-work audit 2026-10-07, `reviews/related-work-2026-10-07.md`; external critique `reviews/external-critique-2026-10-07.md`)
- **Defensible claim.** These are machine-checked worst-case probabilistic bounds for untrusted monitoring with
  upfront honeypots, as far as a limited search shows. Do NOT claim a "first Lean formalisation of control
  protocols". The mathematics is classical (counting, binomial moments, Neyman–Pearson, short inductions).
- **Formal, different object.**
  - Games for AI Control (Griffin, Thomson, Shlegeris, Abate, 2409.07985): trusted monitoring as a POSG, Pareto
    frontiers, defer/audit. Not machine-checked; untrusted monitoring is future work. UMUSE is an instance of its
    safety/usefulness framing.
  - Alignment Contracts (2605.00081, Lean): deterministic effect-trace contracts; the closest Lean "action layer".
  - SOUNDGATE (2607.14166, Verus/TLA+): an external effect gate. It discharges A4/A5/A11-style properties under
    complete mediation.
  - Formal Confinement (Dougherty; Lean Hoare gate on a toy language; two `sorry`s in the while rule).
  - Legitimacy (`abenenson/legitimacy`; deterministic fixtures, `native_decide`).
- **Informal / statistical anticipations.**
  - Roger–Shlegeris "toy models" ("audit a few examples from each category"): the informal precursor of
    UMSTRATF1/UMNOGOF1.
  - LASR 2602.20628 (statistical; App. B.3: safety is bounded by honest ability).
  - Greenblatt et al. 2312.06942 (App. G: a benign-flag guard).
  - Shlegeris, "win/continue/lose" (Nov 2024): the defer stopping ratio, so UMDEFER claims only the adaptive bound,
    the composition and the no-go.
- **Open evidential obligations** (the critique's four): deductive correctness (Lean gate); specification fidelity
  (fidelity audits); implementation correspondence (VCVio refinement, SANDBOX; scaffold unverified); environmental
  validity (L, r, coverage: STANDING, not discharged by any measurement here).

## Assumptions still unproved (what the stack does NOT give)
1. **That any deployed mediator satisfies the trusted-component hypothesis** (domination constant L, or
   hockey-stick δ, over every bad submission).
   - The theorems are parameterised by it.
   - Content preservation forces large domination constants: L ≥ exp-maximal-leakage over the chosen bad set
     (UMHSF1). Coverage requirements grow with the number of decodable bad classes (UMNOGOF1). A finite L always
     exists in a finite model, e.g. L = |Bad| for uniform honeypots over Bad (Sol); the point is that it is too large
     to be useful at realistic n_h.
   - Certifying it for a concrete mediator is open. CANONF1 is the only verified concrete mediator, and it removes only
     three named channels.
2. **Constructibility (A9).** Blue can enumerate a superset B̄ of Bad and build honeypots on it. The action layer
   should supply B̄ structurally.
3. **Worst-case audit recall r (A6, STANDING).** It needs human/U parity, as in Greenblatt et al. and LASR.
4. **Scaffold properties (A1–A4) are assumed, not verified:**
   - fresh monitor contexts;
   - fresh randomness;
   - the view z is the complete monitor input;
   - upfront honeypots.

   Verifying the scaffold is a code-level (Aeneas/hax) target.
5. **Fidelity of the recursions to the operational protocol.** For the halting protocol with hard slack this is now a
   Lean theorem in the VCVio project (`RefinementProof.lean`: game = `catG`, and the end-to-end bound). Still open: soft
   slack (needs real-valued coins), the hockey-stick form, and the stratified design at the game level.
6. **Out of model:**
   - stateful monitors and interleaved honeypots;
   - defer-on-exhaustion (it voids the guarantee; numerics only);
   - multi-step attacks;
   - composition with trusted monitoring (a min, not a product, absent conditional independence);
   - LASR's retraining slack (an assumption about U's learning dynamics).
