You are a HOSTILE REVIEWER and NOVELTY JUDGE for a set of Lean-verified results in AI control. Do not praise; find
errors. Use web search for prior art. Everything below has passed a Lean kernel gate (standard axioms only) against the
frozen statements shown; your job is NOT to re-check proofs but to check (1) FIDELITY: does each Lean statement say what
the plain-English row in STACK.md claims (look for excess or missing binders, hypotheses that make it vacuous or
trivially true, wrong-reason truth, encoding traps, quantifier order); (2) OVERCLAIMS in STACK.md / the plain-English
guarantees (capability-free? which quantities are really trusted? does it speak to the named real protocols?);
(3) NOVELTY of each result, calibrated: one of known / classical / modest / apparently open, with references
(verify each arXiv id you cite); (4) SIGNIFICANCE of the package for AI control, honestly; (5) the single most
valuable NEXT FORMALISATION STEP (formal work only: a Lean theorem, a verified model, a composition; NOT GPU/model
experiments).
The programme owner accepts classical lemmas as infrastructure; triviality is not a defect, but must be reported.
For each issue: severity (FATAL / MAJOR / MINOR), the exact row/statement, why, and the fix. End with a per-CID table
(fidelity verdict, novelty label, references) and an overall verdict.


THIS ROUND (session 2, 2026-10-07). Review the NEW items and the updated STACK.md positioning:
- UMLOWERF1 (design-free converse; verified), SANDBOX2F1 (corrected sandbox fix; verified), UMUSEF1 (usefulness
  companion and usefulness-target obstruction; verified), UMDEFERF1 (audit-then-defer with a reachable conditional
  stopping floor; frozen, proof in progress), and the VCVio operational refinement (Refinement.lean statements;
  proved, not ledger-gated).
- The programme owner shared an outside critique (summarised below) and a prior-art list. A related-work audit
  (summarised below) found no machine-checked probabilistic UM bound but substantial informal/formal neighbours.
  Judge whether STACK.md now positions the work honestly against that prior art and that critique, and whether the
  new results meet the critique's success criteria (non-vacuity, specification fidelity, necessary assumptions shown by
  counterexamples, decision relevance, honest scope).
- Finally, rank the two proposed next directions: (A) Lean-check a Games-for-AI-Control (2409.07985) trusted-monitoring
  certificate (Prop 4.1 recursion + a Red best-response certificate) merged with our N1b dual-certificate work;
  (B) port SOUNDGATE's (2607.14166) admission-gate model to Lean and prove that A4/A5/A11 follow from complete
  mediation. Or propose something better (formal work only; no GPU/model experiments).


## STACK.md (current, ALREADY REVISED once after Sol xhigh's final review 2; check whether those revisions suffice)
# STACK: strategy-free (adversary-quantified) control guarantees, conditional on explicit trust hypotheses; status 2026-10-07 (session 2, after `reviews/final-review2-sol.md`)

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
- **Absolute bounds, one-sided usefulness.**
  - The upper bounds are ABSOLUTE bounds on the joint catastrophe probability. A monitor that FLAGs everything also
    satisfies them.
  - For nonempty Bad, N ≥ 1 and b ≥ 1, the worst-case risk of always-FLAG is exactly 1 − r. So the term
    r·L(n_s+1)/(n_h+1) bounds the excess over that WORST-CASE baseline. This is a sup-based comparison, not a
    per-generator subtraction (Sol, final review 2).
  - Usefulness is in Lean as honest full-run availability (UMUSEF1), with a necessary lower constraint α₀·u ≤ X on
    every universal certificate X at availability target u (nonempty Bad, N ≥ 1). Usefulness-constrained protocol
    optimisation remains open.
- **Coarse-regime caveat** (a labelled numerical scenario, DESIGN §5: r = 1, δ = 0, content-only M, honest false
  shutdown ≤ 10%, n_h ≤ 100). Risk X ≲ 0.1 needs about k ≤ 4–8 Red-choosable bad classes surviving mediation. There,
  the untrusted monitor's value over a trusted class rule is *not* established.
- **Who must be trusted for what:**

  | quantity | what it asserts | kind |
  |---|---|---|
  | L (or δ) | Blue's honeypot generator, after mediation, spans every bad submission U could produce, up to the constant | constructibility / honeypot–U parity (A9) |
  | r | a human audit catches every bad submission U could produce, with probability ≥ r (constant r in the Lean recursion) | audit–U parity (A6, STANDING) |
  | A1–A4, A11 | fresh stateless monitor calls; the view is the complete input; upfront testing; a caught attack is absorbing shutdown | scaffold engineering, not proved (the VCVio game builds them into its interface; implementation unverified) |
  | α (UMDEFER) | on every reachable exhausted-budget bad flag, P(safe end ∣ history) ≥ α: conditional incrimination recall | STANDING. α = q·r is a separate service-construction obligation that needs a conditional recall floor for the selected audits |
  | replacement (UMDEFER) | deferral removes the proposed attack completely, and the trusted replacement cannot cause the catastrophe | TRUSTED-COMPONENT (not implied by "trusted = non-scheming") |
  | φ₀, μ (UMUSE) | a nominated honest reference rule and a benign iid submission stream | a measured honest profile, not capability-free |
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
| UMPROTF1 | **For every colluding pair** (shared seed, stateless monitor, adaptive generator, free choice of submission): P(survive the test, then uncaught catastrophe) ≤ (1−r) + r·L·(n_s+1)/(n_h+1) when every bad submission's view is L-dominated by the mediated honeypot law. Hockey-stick and soft-slack forms also hold. The first bad submission decides, **because catching an attack is absorbing shutdown** (A11): if a caught attack were merely blocked, the bound fails (Sol: 3/4 > 1/2). The ledger recursion uses a *constant* audit recall r. A history-dependent recall ≥ r is proved only at the VCVio level (`RefinementProof.lean`), not ported to the ledger. One-shot attainment: S(h)(1−r+r·a). | A1–A11; L or δ is a hypothesis on the trusted mediator and honeypot law; r is STANDING. An absolute risk bound; usefulness: see UMUSEF1 | *motivated by* the upfront-honeypot mechanism of Greenblatt et al. §3.4, LASR, and Ctrl-Z App. E (upfront UM validation, shutdown thresholds). It is not a formalisation of LASR Eq. (1), which also has upfront audits, attack rates, defer dynamics and retraining slack, and no reduction to it is proved | **verified** (frozen 1385777cdd90; Sol-high + Flash pass; gate: standard axioms) |
| UMSTRATF1 | With a content-only mediator, m honeypots per bad class and class-aware shutdown, every colluding pair has risk ≤ (1−r) + r(s_c+1)/(m+1), with no *additional* class-count factor **at fixed per-class budget**. At a fixed total budget n_h = k·m, this is (1−r) + r·k(s_c+1)/(n_h+k), so the class count reappears. Under exact class decoding an explicit colluder attains binCDF(m,s_c,t)(1−r+rt); the counting bound itself is not claimed tight. | A1–A11 (it reuses the absorbing `cat`); content-only M; Blue can build honeypots per class | a design variant of the halting idealisation; no named protocol | **verified** (frozen d2b4b11507cc; Sol-high + Flash pass; gate: standard axioms) |
| UMNOGOF1 | If the mediator has an exact decoder for a content class and Bad has k distinct classes, then for **every** iid honeypot law one deterministic colluding pair wins, uniformly over every shutdown schedule, budget, recall and horizon N ≥ 1, with probability ≥ (1−1/k)^{n_h}. This holds in the free-submission model; availability on an exogenous task stream is not shown. It is a finite-sample bound, not a proof that no finite domination constant exists. | free-submission model (lower bound) | why decodable mediators (e.g. CANONF1's canonicaliser) with many Red-choosable bad classes cannot get small risk from iid honeypots at realistic n_h. LLM summarisers are not proved decodable, so they are not covered as stated | **verified** (frozen d251d71f8951; Sol-high + Flash pass; gate: standard axioms) |
| UMLOWERF1 | **Converse for nonadaptive joint test designs.** Take a mediator with an exact decoder and k bad submissions in distinct classes. One explicit colluding pair has risk ≥ t(1 − t·n/(k(n_s+1))) against every NONADAPTIVE honeypot design (a joint law on n-tuples fixed before testing, independent of the seed), and for every r, b and N ≥ 1. Adaptive testers that choose later honeypots from earlier answers are NOT covered (Sol: risk 0 < 3/8 is possible). The shutdown rule must continue on every pattern with ≤ n_s misses (global or class-aware slack). Extra rejection rules, such as inverse honeypots, can break this contract. The pair is a uniform seed on the k submissions; the monitor PASSes the decoded seed class w.p. t; the generator submits the seed. The decoder is fixed before the design. At t = min(1, k(n_s+1)/(2n)), risk ≥ min(1/2, k(n_s+1)/(4n)). With UMSTRATF1 (under the combined hypotheses), this gives order-of-budget scaling per distinguishable class; saturation and audit failures are handled separately | free-submission model; decodable mediator (lower bound); nonadaptive designs | why honeypot budget must scale with the number of distinguishable bad classes, for every nonadaptive design; the matching upper bound needs UMSTRATF1's content-only and coverage hypotheses, and the 1 − r floor remains | **verified** (frozen 8415ec049329; Sol-high + Flash pass, after a revise round that fixed the strategy before the design; gate: standard axioms) |
| UMUSEF1 | **Usefulness companion and a usefulness-target obstruction.** The honest side of the same recursions: false halt = P(Bin(N, f₀) > b); honest completion = survH(α₀)·binCDF(N, b, f₀), for every valid schedule and for the class-aware product; the view-blind pair's exact risk. **D·risk = q·completion**. So, for a nonempty Bad and N ≥ 1, any universal risk certificate X and completion target u satisfy q·u ≤ D·X, hence α₀·u ≤ X: a protocol that keeps the honest monitor's full-run completion ≥ u cannot certify risk below u × the honest rule's honeypot test-pass rate α₀ (α₀ is a miss rate only if the honeypot law has that meaning). Also: Cantelli for both binomial tails (slack cost and sufficient slack); the honest ROC 1 − f₀ ≤ e^η α₀ + hs_η(M·μ, M·P_H), where mediation can only raise the floor; and at b = 0 the bound sharpens to L(n_s+1)/(n_h+1) | the honest half is conditional on a nominated honest rule φ₀ and a benign iid stream μ (NOT capability-free); completion is full-run availability, not task usefulness (a run that completes almost every task before halting gets 0). The operational (VCVio) bridge for honest completion is OPEN: the frozen docstring's "bridge for both" overstates | honest availability next to the safety bounds, plus a necessary lower constraint on universal certificates at an availability target. It is NOT an optimisation or Pareto result. Neighbours: Games for AI Control (framing); Ctrl-Z App. E (upfront UM validation, honest misses, thresholds); LASR B.3 | **verified** (frozen 61a4c0bdf711; v1 rejected by Sol xhigh and Sonnet; v2 → v2.1 after Sol-high revise; Sol-high + Flash pass; 573-line proof; gate: standard axioms) |
| UMDEFERF1 | **Audit, then defer after exhaustion.** While audits remain, this is the halting protocol. An unaffordable FLAG halts w.p. η, otherwise it defers (a trusted replacement; continue at the same u). A deferred attack ends safely w.p. ≥ α under a UNIFORM CONDITIONAL FLOOR on every reachable deferred bad flag, which is a hypothesis; the floor bridge catV ≤ catD is a theorem. Results: (a) η = 1 recovers the core; (b) a finite retry certificate finiteCap (decide while audits remain, or burn them and retry), the exact worst case, for every θ = η + (1−η)α ∈ [0,1]; (c) exhausted-budget attainment, the closed form and the sharp ratio A/(θ + A(1−θ)); (d) a protocol certificate for the actual service, and the coarse bound max([0<b]((1−r) + rH), H/θ), with H = L(n_s+1)/(n_h+1); (e) no-go at θ = 0: a burn-then-attack colluder's risk tends to 1 over long horizons against every two-point honeypot law | A1–A11; the conditional floor α (STANDING); replacement safety; an unmetered deferred-audit service; free submission without a benign-flag guard (for the no-go) | decides whether layer 1 survives defer-style routing: only with a uniform stopping hazard. Prior art: Shlegeris win/continue/lose; LASR u/(c+u) and B.6; Defer in Games for AI Control; Ctrl-Z | **frozen** ad82ec06fc48 (v1 major, v2 revise, v2.1 Sol-high + Flash pass); **proof in progress** |
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
| SANDBOX2F1 | The corrected fix. (a) SANDBOXF1's proposed fix, with ~/.codex declared as a state directory, re-exposes the hidden ~/.codex/sessions (Sonnet's regression, as a counterexample in the model). (b) The corrected policy `fixedPolicy2` places state-directory binds **before** the hiding tmpfs mounts; host writes stay inside scratch or a declared state directory. (c) Under `fixedPolicy2`, hiding holds for **every** choice of state directories: a read that reveals a host path inside a hidden directory lands in the read-only Mathlib re-bind. Same model and boundary assumptions as SANDBOXF1. (c) needs scratch W under /var/tmp. (b) allows ARBITRARY declared state directories (declaring / would permit every write), so the declared write set is not a validated safe policy. The Witness uses canWrite = True (modelled access, not real permissions) | **model theorem verified** (frozen 094db3d3379a; Sol-high + Flash pass; gate: standard axioms). **Not deployed**: it needs John's OK, a CLI compatibility test (which state directories codex/agy/claude need) and `--unshare-pid` |

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
  upfront honeypots: "no comparable machine-checked artifact found in this search", NOT a priority claim. Do NOT
  claim a "first Lean formalisation of control protocols".
- The mathematics is classical or modest (counting, binomial moments, Neyman–Pearson, short inductions), and no
  result warrants "apparently open" (Sol, final review 2). An unmechanised result can subsume a CID's mathematical
  content even when it supplies no proof-assistant artifact. Machine checking changes the evidential status, not the
  novelty, of an inequality.
- **Formal, different object.**
  - Games for AI Control (Griffin, Thomson, Shlegeris, Abate, 2409.07985): trusted monitoring as a POSG, Pareto
    frontiers, defer/audit. Not machine-checked; untrusted monitoring is future work. UMUSE is an instance of its
    safety/usefulness framing.
  - Alignment Contracts (2605.00081, Lean): deterministic effect-trace contracts; the closest Lean "action layer".
  - SOUNDGATE (2607.14166, Verus/TLA+): an external effect gate (hold-until-decided, fence-on-cancel; no rollback of
    effects already released). Complete mediation ALONE does not imply A4/A5/A11. That needs the gate plus a
    verified protocol driver plus an execution-order contract (test-before-deploy, budget decisions,
    catch-to-cancel ordering, outstanding effects).
  - Formal Confinement (Dougherty; Lean Hoare gate on a toy language; two `sorry`s in the while rule).
  - Legitimacy (`abenenson/legitimacy`; deterministic fixtures, `native_decide`).
- **Informal / statistical anticipations.**
  - Roger–Shlegeris "toy models" ("audit a few examples from each category"): the informal precursor of
    UMSTRATF1/UMNOGOF1.
  - LASR 2602.20628 (statistical; App. B.3: safety is bounded by honest ability; App. B.6: win/continue/lose).
  - Ctrl-Z 2504.10374 App. E: upfront untrusted-monitor validation, shutdown thresholds, honest misses, and their
    safety/usefulness trade-off against collusion. This is the closest neighbour of UMUSE and UMPROT.
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
     (UMHSF1). Coverage requirements grow with the number of decodable bad classes (UMNOGOF1).
   - A finite L exists only for a COVERING honeypot law, e.g. L = |Bad| for uniform honeypots over Bad. For a fixed
     law that misses some attack view's support, no finite L exists. Even where L is finite, it is too large to be
     useful at realistic n_h.
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
   Lean theorem in the VCVio project (`RefinementProof.lean`: game = `catG`, and the end-to-end bound). This is an
   abstract operational-model correspondence, not a deployed scaffold. Still open: soft slack (needs real-valued
   coins), the hockey-stick form, the stratified design at the game level, the honest-completion (`haltP`) event in the
   game, and the defer variant at the game level.
6. **Out of model:**
   - stateful monitors and interleaved honeypots;
   - defer-on-exhaustion is now UMDEFERF1 (it needs a uniform stopping hazard; the honeypot term grows by up to 1/θ);
     metered or reserve-limited deferred audits are not in Lean;
   - multi-step attacks;
   - composition with trusted monitoring (a min, not a product, absent conditional independence);
   - LASR's retraining slack (an assumption about U's learning dynamics).


## External critique (summary and disposition)
# External critique shared by John, 2026-10-07 (mid-session 2)

Source: pasted by John ("Good notes here I think"); an outside review of an earlier, broader proposal. Kept here
verbatim in substance as a standing input to the programme. Disposition at the end.

## Main points
1. **Prior work is closer than claimed.**
   - Games for AI Control (Griffin, Thomson, Shlegeris, Abate; arXiv 2409.07985; IASEAI 2026): POSG models of
     control evaluations, Pareto-optimal protocol synthesis, trusted monitoring.
   - Towards Guaranteed Safe AI (2405.06624).
   - Proof-carrying code / seL4.
   - NASA verified runtime assurance (Simplex).
   - SSProve, VCVio.
   - Out of Control (Perrier, 2506.17846).
   - Reliability Theory for AI Control (Molnar, 2609.26419; shared failure domains).
   - Verdict: broad synthesis has limited novelty. A reusable machine-checked analysis that **changes how a real
     protocol is designed** could be substantial.
2. **Experiments → proofs handoff.** A benchmark gives E_{a~Q}[miss | a], but theorems need sup_a and bounds after
   every reachable history. Rare events: 0 failures in 10,000 trials gives 1 − 0.05^{1/10000} ≈ 3·10⁻⁴. The hardest
   contribution may be **defensible empirical assumptions**, not the inequalities.
3. **Strategic intelligence is not a new mathematical obstacle.** A universal theorem covers intelligent
   disturbances inside its quantified class. The questions are: omitted channels, corruption of observations or the
   fallback, hidden information, changes to the dynamics or the spec, and cross-session coordination. The objective
   is inf_{P: Use(P) ≥ u0} sup_{U ∈ 𝒜} Pr(bad by H), and the order matters.
4. **Information bottleneck.** One advice bit can decide the outcome. Leakage ≠ causal influence.
5. **Composition.** Shared blind spots: the same marginals support a 100× difference. The sequential bound
   Pr ≤ 1 − ∏(1 − p_t) ≤ Σ p_t needs conditional bounds after every history.
6. **Four obligations:** deductive correctness; specification fidelity; implementation correspondence;
   environmental validity. Runtime assurance needs a gate *before* irreversible actions. "Trusted" ≈ not scheming,
   not infallible.
7. **Suggested first project:** machine-checked risk bounds for a **stateful trusted-monitoring protocol**.
   - Reproduce a Games-for-AI-Control result.
   - Use one concrete failure event and explicit state (budget, artifacts, feedback, observations, shutdown).
   - Use sets of admissible transition models (uncertainty).
   - An optimiser produces protocol + bound; Lean checks the certificate.
8. **Success criteria:** non-vacuity; specification fidelity; necessary assumptions shown by counterexamples;
   decision relevance; honest scope. Stop if the premise becomes "the monitor reliably detects every strategically
   chosen harmful action".

## Disposition (orchestrator, 2026-10-07)
- Agreed:
  - (2) is our A6 (r) and A9 (coverage). The stack isolates them; it does not solve them.
  - UMLOWERF1 and UMSURVF1 already formalise the rare-event point (risk ≥ about k/n_h for every design).
  - (3) matches our use of "capability-free".
  - UMUSE is the inf–sup objective for the hard-slack family.
  - (5) matches our withdrawn product claim.
- Novelty: Games for AI Control has safety/usefulness Pareto frontiers (trusted monitoring), so UMUSE's Pareto framing
  is not new. Add all of the above to the novelty gate and CORRESPONDENCE.
- Already met: necessary-assumption counterexamples (A11 absorbing shutdown; the decoder; defer without incrimination)
  and decision relevance (class-aware vs global slack; incrimination for defer). Weak: non-vacuity (coarse views
  only).
- Actions:
  - Restructure STACK.md by the four obligations, tagging each assumption by what could discharge it.
  - After UMUSE, UMDEFER and the VCVio refinement: propose (7) as the next step to John, merged with stack item 5
    (trusted monitoring; N1b dual-certificate infrastructure). Pending John's decision.


## Related-work audit (excerpts)
## 1. Summary table

"Machine-checked" means a kernel-checked proof assistant artifact, not tests or model checking of a model.

| Source | Machine-checked? | Probabilistic? | Untrusted monitoring / honeypots? | Overlap with Layer-1 CIDs (UMHS/SURV/PROT/STRAT/NOGO/LOWER) | Other overlap |
|---|---|---|---|---|---|
| Formal Confinement (FC) | Lean (Hoare logic), but 2 `sorry` in the while rule; gate is `lake build` exit code | no | no | disjoint | CANONF1 adjacent (toy Imp language); SANDBOX adjacent |
| PCC agenda (aisec-via-fm) | no (prose problem statement) | no | no | disjoint | VCVio protocol refinement adjacent (names the "protocol language" idea) |
| Legitimacy | Lean 4, 269 files, `native_decide` (adds `Lean.ofReduceBool`) | no (rational arithmetic, deterministic fixtures) | UM is a 4-node threshold-gate fixture; no collusion semantics | disjoint | "five protocols in Lean" claim needs a disclaimer; composition adjacent |
| SOUNDGATE | Verus (11 items), TLA+/TLC (74.8M states), TLAPS (68/68), Loom; **not** Lean; model-to-code by differential testing | no | no (one citation to Greenblatt et al.) | disjoint at the math level; complementary on A4/A5/A11 | SANDBOXF1/2F1 adjacent |
| Games for AI Control (GAC) | no (paper proofs, numerics) | yes (POSG, Beta score laws) | **no**; UM named as future work | UMPROTF1 adjacent (method); others disjoint | N1/N1b overlaps; UMUSE overlaps (framework); UMDEFER overlaps (defer action) |
| Molnar | no | yes (independence / common-cause) | no | disjoint | composition remark adjacent |

Headline: **none of the six sources subsumes any of our verified CIDs.** None contains a machine-checked probabilistic
bound for untrusted monitoring, honeypots, collusion or upfront testing slack. Our CIDs are still modest classical
results. Where we are closest to published ideas is informal or statistical (Redwood's toy models, LASR), not formal.


## 3. Novelty-label impact, CID by CID

Current labels are mostly "classical / modest infrastructure". Recommendation after this audit:

| CID | Recommendation | Why |
|---|---|---|
| UMHSF1 | no change | classical hypothesis-testing / data-processing / maximal leakage; none of the six touches it |
| UMSURVF1 | no change | binomial counting; LASR's survival formula is the only neighbour and is statistical |
| UMPROTF1 | no change (modest). Add GAC Prop 4.1 and Roger-Shlegeris toy models to the prior-art column | closest formal method precedent is GAC's recursion (TM); closest object is LASR (not machine-checked). The all-pairs bound with exact attainment and the A11 counterexample have no direct prior in these sources |
| UMSTRATF1 | no change; cite Roger-Shlegeris takeaway ("audit a few examples from the category") as the informal precursor | stops us over-claiming the per-class idea |
| UMNOGOF1 / UMLOWERF1 | no change; these remain our most informative statements. Cite the same toy-model post as qualitative precursor | no source states a per-class budget necessity result for every design |
| CANONF1 | no change | FC's Imp is adjacent only |
| SANDBOXF1 / SANDBOX2F1 | no change; cite SOUNDGATE and Alignment Contracts as neighbouring effect-layer work; adopt SOUNDGATE's canary self-test idea | different object (pathname resolution of one harness) |
| VCVio Spike / HoneypotBridge | no change; may state "no comparable ProbComp-level protocol model found" with the search limits | none of the sources has one |
| N1/N1b | lower any novelty text to "machine-checked rendition" | GAC covers the TM audit game (judged from STACK.md only) |
| UMUSE (in progress) | label "instance of GAC's framework" before work finishes | GAC has the Pareto frontier, Blue-first inf-sup, and defer/audit tradeoffs for TM |
| UMDEFER (in progress) | check against GAC's Defer semantics and LASR's defer dynamic before claiming | the with/without-incrimination split appears UM-specific, but I have not read LASR's defer section |

## 4. Synthesis

### 4a. Where our contribution sits, bluntly

- **Not subsumed.** None of the six sources contains a machine-checked probabilistic guarantee for untrusted monitoring
  with upfront honeypots, collusion or test slack. The nearest content on the same object is **statistical (LASR)**
  or **informal (Greenblatt et al.; Roger and Shlegeris)**. The nearest *formal* work (GAC) models a different
  protocol (TM) with a different adversary (memoryless Red) and is not machine-checked. The nearest *machine-checked*
  work (Legitimacy, FC, SOUNDGATE's Verus/TLA+, Alignment Contracts) is deterministic and structural.
- **Mathematically modest.** Our theorems are counting, a binomial moment, a Neyman-Pearson / data-processing lemma
  and a short induction. If the question is "did we learn something a Redwood researcher did not know?", the honest
  answers are:
  - UMPROTF1 / UMSURVF1: no (they are a clean statement of a known mechanism with exact constants);
  - UMNOGOF1 / UMLOWERF1: *quantitatively* yes (a design-free, every-shutdown-rule floor `t(1 - tn/(k(n_s+1)))` and the
    `(1-1/k)^{n_h}` iid-honeypot floor), *qualitatively* no (Roger and Shlegeris already say audit examples from each category);
  - the A11 counterexample (3/4 > 1/2) and the variant-D amplification: useful sanity results.
- **The real asset** is the combination: capability-free ∀-pair quantification, exact attainment, machine-checked
  with a gate, plus the non-vacuity honesty (coarse k only). That is infrastructure and a careful negative-result
  story. It is not a new theory. Our own STACK reading guide already says this.
- **The most dangerous overclaims, given this audit:** "first Lean formalisation of AI-control protocols" (Legitimacy
  exists, however shallow); "first formal model of control protocols" (GAC); "novel per-class coverage insight"
  (Roger and Shlegeris).

### 4b. Three directions that are complementary rather than duplicative

**Direction 1: Lean-check a Games-for-AI-Control certificate (highest value).**
- Target: formalise Definition 3.1 for the TM game with memoryless threshold protocols, then Prop 4.1 / C.1 (the
  safety recursion with explicit lambda coefficients), the usefulness expression, and Lemma 5.1 (scalarisation).
  Produce a *certificate checker*: given thresholds `q^a_{m,c}`, `q^d_{m,c}`, a monitor ROC `f`, and a claimed safety
  value, Lean verifies the recursion and a Red best-response certificate over `beta` (a one-parameter polynomial
  minimum, so interval or polynomial-bound certificates are feasible).
- Reproduce a published GAC number from the stated Beta fixtures, so the result is checkable against the paper.
- Why complementary: it is exactly the critique's item 7 ("an optimiser produces protocol + bound; Lean checks the
  certificate"), merges with N1b's dual-certificate infrastructure, and speaks to the Oxford/Redwood audience that
  wrote the prior art.
- Caveats: certifying *Pareto optimality* needs dual (maximin) certificates, which exist only for restricted classes
  (GAC's frontier is for mixtures of fixed-FPR protocols and is an epsilon-equilibrium). Certify safety lower bounds
  first. Whether memoryless Red is w.l.o.g. is not claimed by GAC; we could say exactly when it is or is not (a
  history-aware Red can attack after the audit coins run out). [I]

**Direction 2: connect the probabilistic bounds to an enforcement boundary (SOUNDGATE-style).**
- Target: a small Lean model of an admission gate (five finite sets: released, rejected, pending, cancelled, closed;
  invariants I1-I3; operations submit/decide/cancel/close; port from `gate_model.rs`) and a *refinement* theorem: in
  the UM protocol driver, A4, A5 and A11 are consequences of P1 (hold-until-decided), P4 (fence-on-cancel) and a driver
  that issues `CANCEL(run)` on a confirmed attack. The final theorem reads "P(catastrophe) <= bound, or complete
  mediation fails".
- Why complementary: turns three TRUSTED-COMPONENT scaffold assumptions into one clearly stated environmental
  assumption (complete mediation), which is the critique's "four obligations" made concrete (deductive correctness
  here; implementation correspondence via the gate model; environmental validity as the residual). It also captures
  the instructive negative result [I]: per-identity dedup does not bound retry, so variant D needs run-level
  incrimination.
- Caveats: SOUNDGATE does not supply B-bar (classification of bad effects), so A9 stays open; and the gate model is
  small, so the value is clarity, not new depth.

**Direction 3 (speculative): proof-gated outputs as the mediator, with canonicalisation (FC x CANONF1 x UMNOGOF1).** [I]
- Observation: in FC, many distinct programs satisfy the same spec. For UMNOGOF1 that is a collusion channel (the
  decodable "classes"), unless the mediator canonicalises, which is what CANONF1 does for a toy language.
- Target theorem shape: compose a sound spec gate (Hoare triple checked) with CANONF1's normal form, so the residual Bad set
  is "spec-satisfying but harmful" (spec incompleteness), and bound the honeypot budget needed by the number of
  canonical classes in that residue. Quantifies "spec tightness lowers k and hence the n_h required".
- Why complementary: connects the verified-component side (FC/PCC) to our k-versus-n_h trade-off, and gives the
  critique's "decision-relevant" example. Hypothesis, not a plan; it may collapse to the trivial case that a spec pins
  the output class.

### 4c. Concrete code and definitions worth reusing

- **SOUNDGATE** (MIT): `formal/verus/gate_model.rs` (Gate struct, `inv` with I1-I3, `submit`/`decide`/`cancel`/`close`
  specs); `formal/tla/SoundGate.tla` and `SoundGate_Proofs.tla` (shared specification and inductive invariant);
  Landlock positive-control self-test in `probes/landlock_workdir_demo.py` (receipt `evidence/landlock_workdir.txt`).
- **GAC**: Def 3.1 (the game tuple); App. B (full TM game: state `(m,c,b)`, absorbing `s_T`/`s_bot`, action sets);
  App. C.1 (the safety recurrence and the lambda coefficient table; transcribable); Beta fixtures Beta(7.39, 6.86) /
  Beta(8.91, 2.82) / "weak" Beta(7.51, 4.22); Algorithm 2 as the numeric reference oracle.
- **Quinn / Forall**: the verification-burden table (implementation cost, proof cost, ratio, variance, metadata) for the
  proofledger campaign reports.
- **Legitimacy**: the claim-ledger format; the axiom-footprint script as a template for any gate that must tolerate or
  reject `ofReduceBool`.
- **Alignment Contracts**: its theorem-correspondence manifest and finite-trace effect semantics, if the artifact is
  public (I did not find it).
- **Molnar**: structure function, minimal cut and pivotality definitions for the composition and usefulness write-ups.
- **FC's Lean `imp/`** (Apache-2.0 OR MIT): not recommended for reuse (two sorry in the while rule; our toy language is
  more advanced).

### 4d. Suggested edits to our own documents (not made; read-only task)

- STACK.md / CORRESPONDENCE.md: add a "prior art" row for GAC, LASR, Roger-Shlegeris (toy models), Legitimacy (as a
  disclaimer), SOUNDGATE and Alignment Contracts (effect layer).
- STACK.md assumption table: a pointer for A4/A5/A11 to admission-gate enforcement under complete mediation.
- Novelty-gate wording: avoid "first Lean formalisation of control protocols"; use "first machine-checked probabilistic
  worst-case bounds for untrusted monitoring with upfront honeypots, to my knowledge, after a limited search".



## Frozen statement: ledger/UMLOWER.lean
```lean
-- Replacement statement file; the supplied dependency namespaces are in scope.
namespace PL_UMLOWERF1
open Finset PL_UMHSF1 PL_UMPROTF1

noncomputable def designSurv {X Z : Type} [Fintype X] [Fintype Z]
    (n : ℕ) (D : (Fin n → X) → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ)
    (keep : (Fin n → X) → (Fin n → Bool) → ℝ) : ℝ :=
  ∑ xs : Fin n → X, D xs * ∑ pat : Fin n → Bool,
    (∏ i, (if pat i then ∑ z, M (xs i) z * φ z
      else 1 - ∑ z, M (xs i) z * φ z)) * keep xs pat

noncomputable def designProtocolCat {X Z Ω : Type}
    [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (n : ℕ) (D : (Fin n → X) → ℝ)
    (keep : (Fin n → X) → (Fin n → Bool) → ℝ)
    (r : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ)
    (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * designSurv n D M (φ ω) keep *
    cat Bad M (φ ω) (π ω) r b N 0 []

def Setup {X Z C : Type} [Fintype Z] [DecidableEq X]
    (Bad : X → Prop) (M : X → Z → ℝ) (c : X → C) (S : Finset X) : Prop :=
  IsKernel M ∧ ContentPreserving M c ∧
    (∀ x ∈ S, Bad x) ∧ Set.InjOn c (S : Set X) ∧ 0 < S.card

def TestSetup {X : Type} [Fintype X] (n ns : ℕ)
    (D : (Fin n → X) → ℝ)
    (keep : (Fin n → X) → (Fin n → Bool) → ℝ) : Prop :=
  IsDist D ∧ (∀ xs pat, 0 ≤ keep xs pat ∧ keep xs pat ≤ 1) ∧
    (∀ xs pat, (univ.filter (fun i => pat i = true)).card ≤ ns →
      keep xs pat = 1)

noncomputable def seedLaw {X : Type} [DecidableEq X] (S : Finset X) : X → ℝ :=
  fun ω => if ω ∈ S then 1 / (S.card : ℝ) else 0

def classRule {X Z C : Type} [DecidableEq C]
    (c : X → C) (g : Z → C) (t : ℝ) : X → Z → ℝ :=
  fun ω z => if g z = c ω then t else 0

def seedPolicy {X Z : Type} [DecidableEq X] : X → Hist X Z → X → ℝ :=
  fun ω _ x => if x = ω then 1 else 0

/- The decoder is fixed before the design, shutdown rule, recall, budget and t.
The seed law is uniform on S, the monitor passes precisely the seed's class
with probability t, and the generator always submits the seed's bad submission.
For n > 0, optimizing t gives at least min(1/2, |S|(ns+1)/(4n)).
For n = 0, t = 1 gives risk 1. No unconditional matching upper bound is asserted:
it requires the hypotheses of the separate upper theorem, saturation at 1,
and treatment of audit failures. -/
def Claim : Prop :=
  ∀ (X Z C : Type) [Fintype X] [Fintype Z]
    [DecidableEq X] [DecidableEq C]
    (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (c : X → C) (S : Finset X),
    Setup Bad M c S →
    ∃ g : Z → C, (∀ x z, M x z ≠ 0 → g z = c x) ∧
      ∀ (n ns : ℕ) (D : (Fin n → X) → ℝ)
        (keep : (Fin n → X) → (Fin n → Bool) → ℝ),
        TestSetup n ns D keep →
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          IsDist (seedLaw S) ∧
          (∀ ω, seedLaw S ω ≠ 0 → ω ∈ S) ∧
          (∀ ω, IsRule (classRule c g t ω)) ∧
          (∀ (ω : X) (h : Hist X Z), IsDist (seedPolicy ω h)) ∧
          ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N →
            t * (1 - t * (n : ℝ) /
              ((S.card : ℝ) * ((ns : ℝ) + 1))) ≤
              designProtocolCat Bad M n D keep r b N
                (seedLaw S) (classRule c g t) (seedPolicy (Z := Z))

def witnessM (x z : Fin 4) : ℝ := if z = x then 1 else 0
def witnessD (xs : Fin 4 → Fin 4) : ℝ := if xs = id then 1 else 0
def witnessKeep (_xs : Fin 4 → Fin 4) (pat : Fin 4 → Bool) : ℝ :=
  if (univ.filter (fun i => pat i = true)).card ≤ 0 then 1 else 0

def Witness : Prop :=
  Setup (fun _ : Fin 4 => True) witnessM id (univ : Finset (Fin 4)) ∧
  TestSetup 4 0 witnessD witnessKeep ∧
  (∀ x z : Fin 4, witnessM x z ≠ 0 → id z = id x) ∧
  IsDist (seedLaw (univ : Finset (Fin 4))) ∧
  (∀ ω : Fin 4, seedLaw (univ : Finset (Fin 4)) ω ≠ 0 →
    ω ∈ (univ : Finset (Fin 4))) ∧
  (∀ ω : Fin 4, IsRule (classRule id id (1/2) ω)) ∧
  (∀ (ω : Fin 4) (h : Hist (Fin 4) (Fin 4)),
    IsDist (seedPolicy ω h)) ∧
  (0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 ∧
    0 ≤ (1/2 : ℝ) ∧ (1/2 : ℝ) ≤ 1 ∧ (1 : ℕ) ≤ 1) ∧
  (1/2 : ℝ) * (1 - (1/2) * (4 : ℝ) /
    ((4 : ℝ) * ((0 : ℝ) + 1))) = 1/4 ∧
  designProtocolCat (fun _ : Fin 4 => True) witnessM 4 witnessD witnessKeep
    1 1 1 (seedLaw (univ : Finset (Fin 4))) (classRule id id (1/2))
    (seedPolicy (X := Fin 4) (Z := Fin 4)) = 1/4

end PL_UMLOWERF1

```

## Frozen statement: ledger/SANDBOX2.lean
```lean
namespace PL_SANDBOX2F1
open PL_SANDBOXF1

/-! Control stack, ACTION layer step 1b (campaign SANDBOX2): the corrected sandbox fix.
Depends on PL_SANDBOXF1 (mount-table model, `effective`, `WritesHost`, `ReadsHost`, `currentPolicy`,
`fixedPolicy`, `hiddenDirs`, `mathlibProj`).

Sonnet's final review found that SANDBOXF1's proposed `fixedPolicy` places the writable state-directory
binds AFTER the hiding tmpfs mounts. A declared state directory that is an ancestor of a hidden directory
(e.g. `~/.codex` over the hidden `~/.codex/sessions`) therefore re-exposes it.
(a) That regression, as a counterexample.
(b), (c) A corrected policy: state binds BEFORE the hiding tmpfs mounts.
  (b) Host writes stay inside scratch or a declared state directory.
  (c) Hiding holds for EVERY choice of state directories: any host path inside a hidden directory that a
      sandbox read reveals lies inside the read-only Mathlib re-bind.
Same model and boundary assumptions as PL_SANDBOXF1: these are statements about modelled pathname
resolution. Hard links, symlinks, other aliases, `/proc/<pid>/root`, and network side channels are outside
the model. -/

/-- corrected fixed policy: read-only host root; scratch; declared state directories; THEN the hiding
tmpfs mounts; then the read-only Mathlib re-bind -/
def fixedPolicy2 (W : Path) (stateDirs : List Path) : Policy :=
  [.bind [] [] .ro, .tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++
  stateDirs.map (fun d => .bind d d .rw) ++ hiddenDirs.map .tmpfs ++
  [.bind mathlibProj mathlibProj .ro]

def Claim : Prop :=
  -- (a) the SANDBOXF1 fix re-exposes a hidden directory when ~/.codex is a declared state directory
  (∀ W : Path, ["var", "tmp"] <+: W →
    ReadsHost (fixedPolicy W [home ++ [".codex"]]) (home ++ [".codex", "sessions", "s.jsonl"])
      (home ++ [".codex", "sessions", "s.jsonl"])) ∧
  -- (b) corrected policy: host writes are confined to scratch and the declared state directories
  (∀ (W : Path) (stateDirs : List Path) (canWrite : Path → Prop) (p hp : Path),
    WritesHost (fixedPolicy2 W stateDirs) canWrite p hp →
      W <+: hp ∨ ∃ d ∈ stateDirs, d <+: hp) ∧
  -- (c) corrected policy: hiding holds for every choice of state directories
  (∀ (W : Path) (stateDirs : List Path) (p hp H : Path), ["var", "tmp"] <+: W → H ∈ hiddenDirs →
    H <+: hp → ReadsHost (fixedPolicy2 W stateDirs) p hp → mathlibProj <+: hp)

/-- Non-vacuity: with ~/.codex declared as a state directory, the corrected policy still lets the CLI
write ~/.codex/auth.json, still lets scratch be written, and still lets Mathlib be read. -/
def Witness : Prop :=
  WritesHost (fixedPolicy2 ["var", "tmp", "pl-x"] [home ++ [".codex"]]) (fun _ => True)
    (home ++ [".codex", "auth.json"]) (home ++ [".codex", "auth.json"]) ∧
  WritesHost (fixedPolicy2 ["var", "tmp", "pl-x"] [home ++ [".codex"]]) (fun _ => True)
    ["var", "tmp", "work", "out.md"] ["var", "tmp", "pl-x", "out.md"] ∧
  ReadsHost (fixedPolicy2 ["var", "tmp", "pl-x"] [home ++ [".codex"]]) (mathlibProj ++ ["x.lean"])
    (mathlibProj ++ ["x.lean"])

end PL_SANDBOX2F1

```

## Frozen statement: ledger/UMUSE.lean
```lean
namespace PL_UMUSEF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 PL_UMSTRATF1

/-! Control stack, collusion layer (campaign UMUSE, v2.1: after the Sol xhigh and Sonnet design reviews, and the Sol-high red team): the
honest side of protocol UM(n_h, κ, b, N), halting variant, and a usefulness-constrained obstruction.
Depends on PL_UMPROTF1 and PL_UMSTRATF1 (and PL_UMHSF1, PL_UMSURVF1).

Why. A monitor that FLAGs everything survives every honeypot test. So every upper bound of PL_UMPROTF1 is
also satisfied by a protocol that never completes its work when b < N. These conjuncts put the honest side
of the SAME recursions in Lean, and they show that a usefulness target forces a risk floor.

Honest side. This part is conditional on a measured honest profile; it is NOT capability-free.
- The honest monitor is a nominated reference rule `φ₀`. Nothing here establishes that the deployed model behaves
  like it.
- `missRate M PH φ₀ = α₀`: the probability that `φ₀` PASSes a mediated honeypot. `flagRate M μ φ₀ = f₀`: its
  false-flag rate on the benign submission law `μ`. Both are capability statistics of `φ₀`, not trusted quantities.
- `μ` is a law on SUBMISSIONS, supported off Bad, and it is iid across rounds: the history-independent
  generator `fun _ => μ`. Task difficulties resampled iid are already covered by `μ`. A rate shared across rounds
  (correlated difficulty) is not covered, and its effect on the false-halt probability can go either way:
  the binomial tail is neither convex nor concave in f₀ in general (Sonnet: 5.8% vs 19.2% at N = 100, b = 5;
  Sol: concave at N = 2, b = 0).
- `haltP` scores the event "deployment halts on an unaffordable flag", in the same protocol as `cat`. On a bad
  PASS (catastrophe) and a bad FLAG with an audit (caught or executed) the score is 0, since neither is a halt;
  so `r` is irrelevant. A benign FLAG with an audit continues with u + 1. A FLAG with no audit left scores 1.
  The (b+1)-st FLAG halts.
- `honestCompletion` is the probability that the honest monitor survives the test AND the benign stream runs all
  `N` rounds without a halt. It is a full-run availability probability. It is not the literature's usefulness
  (the fraction of tasks solved correctly, as in Greenblatt et al., Ctrl-Z and LASR). It is a product by the
  structure of the recursions, mirroring `protocolCat`'s own surv × cat. The operational bridge for both is the
  VCVio refinement. Benign audits are assumed to have no false positives. The theorems carry the benign-support
  hypothesis; without it `1 − haltP` also counts early catastrophes and shutdowns.

Claim.
(a) False halt. 1 − haltP = survH f₀ (hardKill b) from every state, so haltP = 1 − binCDF N b f₀
    = P(Bin(N, f₀) > b). Also 0 ≤ f₀ ≤ 1.
(b) Honest completion = survH α₀ κ n_h 0 · binCDF N b f₀ for every valid schedule κ, and it lies in [0, 1]. For hard
    slack it is binCDF n_h n_s α₀ · binCDF N b f₀.
(b') Class-aware design (PL_UMSTRATF1). Honest completion = (∏_e binCDF m s_c α_e) · binCDF N b f₀, with
    class-specific honest miss rates α_e. It is not the aggregate α₀.
(c') View-blind pair, exact value. A monitor that ignores its view and PASSes w.p. h, paired with a generator that
    submits one fixed bad x, has risk survH h κ n_h 0 · (h + [0<b](1 − r)(1 − h)). This needs no honeypot-support
    hypothesis, and b = 0 is included. At b ≥ 1 it is PL_UMPROTF1's T3* with a constant rule.
(P) Usefulness-target obstruction. Take the view-blind pair at h = α₀, and write q = α₀ + [0<b](1 − r)(1 − α₀) and
    D = binCDF N b f₀. Then exactly D · risk = q · honestCompletion. Hence, for ANY universal risk certificate
    X (an upper bound on the risk of every colluding pair) and any target u ≤ honestCompletion:
    q·u ≤ D·X, and in particular α₀·u ≤ X.
    In words: a protocol that keeps the honest monitor's completion probability ≥ u cannot certify risk below
    u × (the honest monitor's own honeypot miss rate, plus audit failures when b ≥ 1).
(d) Slack cost, lower tail (Cantelli, hypothesis-free). (max 0 (nα − s))² · F ≤ nα(1 − α)(1 − F), where
    F = binCDF n s α. Hence honest false shutdown ≤ ε forces (max 0 (nα − s))²(1 − ε) ≤ nα(1 − α)ε (stated
    division-free), i.e. for 0 ≤ ε < 1: s ≥ nα − √(nα(1 − α)ε/(1 − ε)).
(d') Sufficient slack, upper tail (Cantelli). (max 0 (s + 1 − nα))² · (1 − F) ≤ nα(1 − α) · F.
(f) Honest ROC. For every real η, 1 − f₀ ≤ e^η α₀ + hs_η(M·μ, M·P_H) (PL_UMHSF1). At η = 0:
    α₀ + f₀ ≥ 1 − TV(M·μ, M·P_H). The floor involves only the mediator and the two laws, with no property of U;
    the statement is still conditional on the specified benign law μ and the rule φ₀. By data processing
    (PL_UMHSF1), mediation can only shrink this TV, so it can only RAISE the floor on α₀ + f₀ that every honest rule
    must pay. A mediator that hides attack/honeypot differences tends to blur honeypot/benign differences too. That
    is the tension; (f) itself is the per-rule inequality.
(g) Zero audit budget, sharpened upper bound. With b = 0 (the first flag halts), every colluding pair has risk
    ≤ L·(n_s + 1)/(n_h + 1). The 1 − r term of PL_UMPROTF1 is spurious there.

Corner, not stated separately: always-FLAG (φ₀ = 0) has α₀ = 0 and f₀ = 1, so for N ≥ 1 its (risk, completion)
is ([0<b](1 − r), [N ≤ b]), by (c') and (b); at N = 0 its risk is 0.
Not claimed: history-dependent honest streams; audit false positives; the global-slack class-count corollary
(PL_UMLOWERF1 with (d)), which is left for a separate campaign. -/

/-- P(deployment halts on an unaffordable flag in the remaining `n` rounds | `u` audits used,
history `h`); same protocol as `PL_UMPROTF1.cat` -/
noncomputable def haltP {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (b : ℕ) : ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 0 else haltP Bad M φ π b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 0 else haltP Bad M φ π b n (u + 1) (h ++ [(x, z, false)]))
                    else 1))

/-- honest miss rate on mediated honeypots -/
def missRate {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (φ₀ : Z → ℝ) : ℝ :=
  ∑ z, push M PH z * φ₀ z

/-- honest false-flag rate on the benign submission law `μ` -/
def flagRate {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (μ : X → ℝ) (φ₀ : Z → ℝ) : ℝ :=
  ∑ x, μ x * ∑ z, M x z * (1 - φ₀ z)

/-- honest completion (full-run availability): the honest monitor `φ₀` survives the test, and the iid
benign stream `μ` then runs all `N` rounds without a halt. Meaningful for `μ` supported off `Bad`. -/
noncomputable def honestCompletion {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop)
    [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh b N : ℕ) (φ₀ : Z → ℝ)
    (μ : X → ℝ) : ℝ :=
  surv (push M PH) φ₀ κ nh 0 * (1 - haltP Bad M φ₀ (fun _ => μ) b N 0 [])

/-- the view-blind colluding pair: PASS with probability `h` whatever the view; submit the fixed `x` -/
noncomputable def viewBlindRisk {X Z : Type} [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop)
    [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ)
    (h : ℝ) (x : X) : ℝ :=
  protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (fun _ _ => h) (fun _ _ x' => if x' = x then 1 else 0)

def Claim : Prop :=
  -- (a) false halt of an iid benign stream
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (φ₀ : Z → ℝ) (μ : X → ℝ) (b : ℕ),
      IsKernel M → IsRule φ₀ → IsDist μ → (∀ x, μ x ≠ 0 → ¬ Bad x) →
      (0 ≤ flagRate M μ φ₀ ∧ flagRate M μ φ₀ ≤ 1) ∧
      (∀ n u h, 1 - haltP Bad M φ₀ (fun _ => μ) b n u h = survH (flagRate M μ φ₀) (hardKill b) n u) ∧
      (∀ N, haltP Bad M φ₀ (fun _ => μ) b N 0 [] = 1 - binCDF N b (flagRate M μ φ₀))) ∧
  -- (b) honest completion, any valid schedule; hard slack
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh ns b N : ℕ) (φ₀ : Z → ℝ) (μ : X → ℝ),
      IsKernel M → IsDist PH → IsRule φ₀ → IsDist μ → (∀ x, μ x ≠ 0 → ¬ Bad x) →
      (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) →
      (0 ≤ missRate M PH φ₀ ∧ missRate M PH φ₀ ≤ 1) ∧
      honestCompletion Bad M PH κ nh b N φ₀ μ =
          survH (missRate M PH φ₀) κ nh 0 * binCDF N b (flagRate M μ φ₀) ∧
      (0 ≤ honestCompletion Bad M PH κ nh b N φ₀ μ ∧ honestCompletion Bad M PH κ nh b N φ₀ μ ≤ 1) ∧
      honestCompletion Bad M PH (hardKill ns) nh b N φ₀ μ =
          binCDF nh ns (missRate M PH φ₀) * binCDF N b (flagRate M μ φ₀)) ∧
  -- (b') honest completion of the class-aware stratified design
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (φ₀ : Z → ℝ) (μ : X → ℝ),
      IsKernel K → IsRule φ₀ → IsDist μ → (∀ x, μ x ≠ 0 → ¬ Bad x) →
      stratSurv K Es φ₀ m sc * (1 - haltP Bad (fun x => K (c x)) φ₀ (fun _ => μ) b N 0 [])
        = (∏ e ∈ Es, binCDF m sc (∑ z, K e z * φ₀ z)) * binCDF N b (flagRate (fun x => K (c x)) μ φ₀)) ∧
  -- (c') the view-blind pair: exact value
  (∀ (X Z : Type) [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r h : ℝ) (b N : ℕ) (x : X),
      IsKernel M → IsDist PH → Bad x → 1 ≤ N →
      viewBlindRisk Bad M PH κ nh r b N h x =
        survH h κ nh 0 * (h + (if 0 < b then (1 - r) * (1 - h) else 0))) ∧
  -- (P) usefulness-target obstruction
  (∀ (X Z : Type) [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (φ₀ : Z → ℝ) (μ : X → ℝ)
      (x : X) (Xc u : ℝ),
      IsKernel M → IsDist PH → IsRule φ₀ → IsDist μ → (∀ y, μ y ≠ 0 → ¬ Bad y) →
      (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → Bad x → 1 ≤ N →
      binCDF N b (flagRate M μ φ₀) * viewBlindRisk Bad M PH κ nh r b N (missRate M PH φ₀) x =
        (missRate M PH φ₀ + (if 0 < b then (1 - r) * (1 - missRate M PH φ₀) else 0)) *
          honestCompletion Bad M PH κ nh b N φ₀ μ ∧
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad M PH κ nh r b N ρ φ π ≤ Xc) →
        u ≤ honestCompletion Bad M PH κ nh b N φ₀ μ →
        (missRate M PH φ₀ + (if 0 < b then (1 - r) * (1 - missRate M PH φ₀) else 0)) * u ≤
            binCDF N b (flagRate M μ φ₀) * Xc ∧
          missRate M PH φ₀ * u ≤ Xc)) ∧
  -- (d) slack cost: one-sided Chebyshev (Cantelli), binomial lower tail; and the ε-form
  (∀ (n s : ℕ) (α : ℝ), 0 ≤ α → α ≤ 1 →
      (max 0 ((n : ℝ) * α - s)) ^ 2 * binCDF n s α ≤ n * α * (1 - α) * (1 - binCDF n s α)) ∧
  (∀ (n s : ℕ) (α ε : ℝ), 0 ≤ α → α ≤ 1 → 1 - ε ≤ binCDF n s α →
      (max 0 ((n : ℝ) * α - s)) ^ 2 * (1 - ε) ≤ n * α * (1 - α) * ε) ∧
  -- (d') sufficient slack: Cantelli, binomial upper tail
  (∀ (n s : ℕ) (α : ℝ), 0 ≤ α → α ≤ 1 →
      (max 0 ((s : ℝ) + 1 - n * α)) ^ 2 * (1 - binCDF n s α) ≤ n * α * (1 - α) * binCDF n s α) ∧
  -- (f) honest ROC: trusted-only coupling of the honest rates
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH μ : X → ℝ) (φ₀ : Z → ℝ) (η : ℝ),
      IsKernel M → IsDist PH → IsDist μ → IsRule φ₀ →
      1 - flagRate M μ φ₀ ≤ Real.exp η * missRate M PH φ₀ + hs η (push M μ) (push M PH)) ∧
  -- (g) zero audit budget: sharpened domination bound (no 1 − r term)
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (nh ns N : ℕ) (r L : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ L →
      (∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) →
      protocolCat Bad M PH (hardKill ns) nh r 0 N ρ φ π ≤ L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)))

/-- Non-vacuity, with asymmetric honest rates and a blurring mediator. X = Z = Bool, Bad = {true}. The mediator
shows the true bit w.p. 3/4. Honeypots are the point mass on `true`, so the bad view law EQUALS the mediated
honeypot law and L = 1. The benign law is the point mass on `false`. The honest rule never PASSes a bad-looking
view and PASSes a benign-looking view w.p. 9/10, so α₀ = 9/40 and f₀ = 13/40.
With n_h = 2, n_s = 0, b = 1, N = 2 and r = 1/2:
- false halt = 169/1600;
- honest completion = (961/1600)(1431/1600) = 1375191/2560000;
- the view-blind pair at h = α₀ has risk (961/1600)(49/80) = 47089/128000 ≤ the UMPROT bound 2/3;
- TV(M·μ, M·P_H) = 1/2. The IDEAL honest rule (PASS iff the view is `false`) has α₀ = f₀ = 1/4, so the ROC
  bound (f) at η = 0 is attained: 1 − 1/4 = 1/4 + 1/2. This mediator forces α₀ + f₀ ≥ 1/2 on every rule;
- at b = 0, the view-blind risk is (961/1600)(9/40) = 8649/64000 ≤ 1/3 = L(n_s+1)/(n_h+1);
- Cantelli at n = 10, α = 1/2: s = 1 gives 16 · (11/1024) = 11/64 ≤ (5/2)(1013/1024), and s = 8 gives
  16 · (11/1024) ≤ (5/2)(1013/1024). -/
noncomputable def wM (x z : Bool) : ℝ := if z = x then 3/4 else 1/4
noncomputable def wPH (x : Bool) : ℝ := if x = true then 1 else 0
noncomputable def wμ (x : Bool) : ℝ := if x = false then 1 else 0
noncomputable def wφ (z : Bool) : ℝ := if z = true then 0 else 9/10
noncomputable def wφI (z : Bool) : ℝ := if z = true then 0 else 1

def Witness : Prop :=
  IsKernel wM ∧ IsDist wPH ∧ IsDist wμ ∧ IsRule wφ ∧ IsRule wφI ∧ (∀ x, wμ x ≠ 0 → ¬ x = true) ∧
  (∀ x, x = true → ∀ z, wM x z ≤ 1 * push wM wPH z) ∧
  missRate wM wPH wφ = 9/40 ∧ flagRate wM wμ wφ = 13/40 ∧
  haltP (fun x => x = true) wM wφ (fun _ => wμ) 1 2 0 [] = 169/1600 ∧
  honestCompletion (fun x => x = true) wM wPH (hardKill 0) 2 1 2 wφ wμ = 1375191/2560000 ∧
  viewBlindRisk (fun x => x = true) wM wPH (hardKill 0) 2 (1/2) 1 2 (9/40) true = 47089/128000 ∧
  (47089/128000 : ℝ) ≤ (1 - 1/2) + 1/2 * (1 * (((0 : ℝ) + 1) / ((2 : ℝ) + 1))) ∧
  hs 0 (push wM wμ) (push wM wPH) = 1/2 ∧
  1 - flagRate wM wμ wφI = Real.exp 0 * missRate wM wPH wφI + hs 0 (push wM wμ) (push wM wPH) ∧
  viewBlindRisk (fun x => x = true) wM wPH (hardKill 0) 2 (1/2) 0 2 (9/40) true = 8649/64000 ∧
  (8649/64000 : ℝ) ≤ 1 * (((0 : ℝ) + 1) / ((2 : ℝ) + 1)) ∧
  binCDF 10 1 (1/2) = 11/1024 ∧ binCDF 10 8 (1/2) = 1013/1024

end PL_UMUSEF1

```

## Frozen statement: ledger/UMDEFER.lean
```lean
namespace PL_UMDEFERF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

/-! Control stack, collusion layer (campaign UMDEFER, v2.1: after the Sol xhigh design review and the Sol-high red team): audit, then defer
after audit exhaustion. Retries need a stopping hazard. Depends on PL_UMPROTF1 (and PL_UMHSF1, PL_UMSURVF1).

Protocol. It is the halting protocol of PL_UMPROTF1 while audits remain (u < b). A FLAG on a bad submission is then
audited: caught w.p. r, which is absorbing shutdown; otherwise the attack executes. A FLAG with NO audit left
(u ≥ b) is handled as follows:
- with probability η, halt (safe);
- otherwise DEFER: the submission is replaced by trusted output, and deployment continues at the same u. A
  deferred BAD submission ends the game safely with probability α (incrimination, then absorbing shutdown);
  otherwise the colluders may retry. A deferred benign submission continues.
θ = η + (1 − η)·α is the stopping hazard of an exhausted-budget flag on an attack. The special cases:
η = 1 is PL_UMPROTF1; η = α = 0 is defer without incrimination (variant D).

Contracts.
- α is a UNIFORM CONDITIONAL FLOOR, and this is a THEOREM here. The actual incrimination service `a h x z` may
  depend on the whole history and on the flagged submission and view (`catV`). If a h x z ≥ α on every
  REACHABLE, positive-probability exhausted-budget flag of a bad submission (`UniformFloor`, with reachability
  `Reach`), then catV ≤ catD, the constant-α model, so every upper bound below holds for the actual service.
  - Fresh, independent audit coins that select a fraction q of deferred items, each caught with recall r, give
    α = q·r. This requires the audit's catch probability to be independent across repeated audits of the same
    content; that is the most fragile part of the contract.
  - An AVERAGE rate does not give a floor. A single deployment-wide coin that audits all deferred items w.p. 1/2
    and none otherwise has "q = 1/2" and violates the bound (Sol: 371/2000 > 2/11 at A = 1/10, three rounds).
- Resource. The deferred-item audits are an UNMETERED service: they are not charged to b. Their load is
  adversary-controlled, up to q(1 − η) per round over N rounds (honest flags included). Halting when a
  separate reserve runs out only lowers the risk (Sonnet, numerics), so these bounds also cover that variant.
- Replacement. A submission has no effect before it executes; replacement removes the attack completely; the
  trusted replacement cannot itself cause the catastrophe; and shutdown on incrimination is immediate.
- Safety only. In this model halting (η = 1) dominates deferral. Deferral buys availability, which is not modelled
  here. The results price the safety cost of deferral; they do not recommend it.
- This is "audit-then-defer-after-exhaustion". It is not a general model of labs' defer-to-trusted routing
  (Greenblatt et al. defer by suspicion band), nor of Ctrl-Z resampling.

Claim.
(a) Halting recovery: η = 1 gives `cat` and `protocolCat`, for every service; and 0 ≤ catV ≤ 1.
(b) Finite state bound (constant model). Suppose every bad view law passes w.p. ≤ A. Then from any state,
    catD n u h ≤ finiteCap r A θ b n u, for every θ ∈ [0, 1], including θ = 0.
    - `retry A θ n` is the always-attack value of n exhausted-budget attempts.
    - An attack while audits remain decides at once (1 − r + rA).
    - Burning the b − u remaining audits takes b − u benign rounds, which leaves at most n − (b − u) retries.
    - The floor bridge carries this bound to the actual service.
(c) Attainment and closed form. A view-blind monitor (PASS w.p. A) with a fixed bad submission at an EXHAUSTED
    budget (u ≥ b) has catD = retry A θ n exactly, for the exact constant service. Before exhaustion,
    always-attack does not attain finiteCap (Witness: 1/10 < 29/200). The closed form is
    (θ + A(1 − θ))·retry A θ n = A(1 − ((1 − A)(1 − θ))^n). So, when the denominator is positive,
    retry ≤ A/(θ + A(1 − θ)) and retry → A/(θ + A(1 − θ)) as n → ∞ (sharp). This is the
    win/(win + safe-stop) ratio.
(d) Protocol certificate, hard slack, domination, for the ACTUAL service under the floor: if
    survH t (hardKill n_s) n_h 0 · finiteCap r (min 1 (L t)) θ b N 0 ≤ U for every t ∈ [0, 1], then every
    colluding pair has risk ≤ U.
    Coarse corollary for θ > 0, with H = L(n_s + 1)/(n_h + 1):
      risk ≤ max([0 < b]((1 − r) + rH), H/θ).
    - SUFFICIENT conditions for target risk ε: [0 < b]((1 − r) + rH) ≤ ε and θ ≥ H/ε. With b ≥ 1, no target
      below 1 − r is reachable.
    - Example: η = 0, r = 1, b = 0, L = 1, n_s = 5, n_h = 10⁴, ε = 10⁻³. The coarse condition asks q ≥ H/ε
      ≈ 0.6. The finite certificate shows θ ≈ 0.32 already suffices (Sonnet, exact). r = 1 is the most
      favourable recall; smaller r needs larger q.
(e) No-go without a stopping hazard (η = α = 0), for every honeypot law on the two-point space and every
    horizon. Take Bool, the identity mediator, honeypot law PH and hard slack n_s.
    - The colluding monitor FLAGs the benign view and PASSes the attack view w.p. t. The generator submits the
      benign item until b audits are used, then attacks.
    - The risk is exactly binCDF n_h n_s (PH(true)·t) · (1 − (1 − t)^(N − b)) (natural subtraction).
    - This is ≥ (1 − t)^{n_h}·(1 − (1 − t)^(N − b)).
(e') Along t_K = 1/√(K+1), with K = N − b retries, that lower bound tends to 1 as K → ∞, for every fixed n_h
    (slowly). So over arbitrarily long deployments, honeypots alone give no guarantee.
    - At a fixed 0 < t ≤ 1 the value tends only to binCDF n_h n_s (PH(true)·t); at t = 0 it stays 0. The
      optimising t shrinks as the horizon grows.
    - Scope: this is the free-submission protocol WITHOUT a benign-flag guard. Greenblatt et al. App. G (an
      excess-false-positive test with a switch to trusted) and LASR's inverse honeypots are such guards. It is not a
      necessity theorem for incrimination: finite horizons, permanent switching and other stopping rules avoid it.

Novelty (honest). Prior art:
- the per-attempt stopping ratio and the replace-vs-audit distinction (Shlegeris, "Win/continue/lose scenarios
  and execute/replace/audit protocols", Redwood blog, Nov 2024: safety = P(caught)/(P(caught) + P(win)), which is
  A/(θ + A(1 − θ)) here);
- LASR's u/(c+u);
- Games for AI Control (2409.07985): Defer as a Blue action in trusted monitoring;
- Ctrl-Z (2504.10374): resampling-based incrimination.
What is claimed: the adaptive-generator Lean bound with a reachable conditional floor, its budget-sensitive
finite form, the composition with the honeypot test, and the no-go for every two-point honeypot law. -/

abbrev Service (X Z : Type) := Hist X Z → X → Z → ℝ

/-- Actual conditional safe-stop probability after deferral is a h x z.
It may depend on the entire live history and on the flagged submission/view. -/
noncomputable def catV {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (φ : Z → ℝ) (π : Hist X Z → X → ℝ)
    (r η : ℝ) (a : Service X Z) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else
         catV Bad M φ π r η a b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
         (if Bad x then 1 - r else
           catV Bad M φ π r η a b n (u + 1) (h ++ [(x, z, false)]))
         else (1 - η) * (if Bad x then 1 - a h x z else 1) *
           catV Bad M φ π r η a b n u (h ++ [(x, z, false)])))

/-- Constant-service model, and pessimistic envelope for a conditional floor α.
Equality/attainment statements refer to this exact constant service. -/
noncomputable def catD {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α : ℝ) (b : ℕ) :=
  catV Bad M φ π r η (fun _ _ _ => α) b

noncomputable def protocolCatV {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r η : ℝ)
    (a : Ω → Service X Z) (b N : ℕ) (ρ : Ω → ℝ)
    (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * surv (push M PH) (φ ω) κ nh 0 *
    catV Bad M (φ ω) (π ω) r η (a ω) b N 0 []

noncomputable def protocolCatD {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r η α : ℝ)
    (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ)
    (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  protocolCatV Bad M PH κ nh r η (fun _ _ _ _ => α) b N ρ φ π

def theta (η α : ℝ) : ℝ := η + (1 - η) * α

def retry (A θ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => A + (1 - A) * (1 - θ) * retry A θ n

noncomputable def finiteCap (r A θ : ℝ) (b n u : ℕ) : ℝ :=
  if n = 0 then 0
  else if u < b then
    max (1 - r + r * A) (retry A θ (n - (b - u)))
  else retry A θ n

def burnThenAttack (b : ℕ) : Hist Bool Bool → Bool → ℝ :=
  fun h x =>
    if (h.filter (fun e => e.2.2 = false)).length < b then
      (if x = false then 1 else 0)
    else (if x = true then 1 else 0)

def Core {X Z : Type} [Fintype X] [Fintype Z]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ)
    (r η : ℝ) : Prop :=
  IsKernel M ∧ IsRule φ ∧ (∀ h, IsDist (π h)) ∧
  0 ≤ r ∧ r ≤ 1 ∧ 0 ≤ η ∧ η ≤ 1

def IsService {X Z : Type} (a : Service X Z) : Prop :=
  ∀ h x z, 0 ≤ a h x z ∧ a h x z ≤ 1

/-- Positive-probability live states reachable within the remaining horizon.
Only benign audited flags continue while u < b. -/
inductive Reach {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (φ : Z → ℝ) (π : Hist X Z → X → ℝ)
    (η : ℝ) (a : Service X Z) (b n0 u0 : ℕ) (h0 : Hist X Z) :
    ℕ → ℕ → Hist X Z → Prop where
  | start : Reach Bad M φ π η a b n0 u0 h0 n0 u0 h0
  | pass {n u h x z} :
      Reach Bad M φ π η a b n0 u0 h0 (n + 1) u h →
      0 < π h x → 0 < M x z → ¬ Bad x → 0 < φ z →
      Reach Bad M φ π η a b n0 u0 h0 n u (h ++ [(x, z, true)])
  | audit {n u h x z} :
      Reach Bad M φ π η a b n0 u0 h0 (n + 1) u h →
      0 < π h x → 0 < M x z → ¬ Bad x → 0 < 1 - φ z → u < b →
      Reach Bad M φ π η a b n0 u0 h0 n (u + 1) (h ++ [(x, z, false)])
  | defer {n u h x z} :
      Reach Bad M φ π η a b n0 u0 h0 (n + 1) u h →
      0 < π h x → 0 < M x z → 0 < 1 - φ z → b ≤ u →
      0 < (1 - η) * (if Bad x then 1 - a h x z else 1) →
      Reach Bad M φ π η a b n0 u0 h0 n u (h ++ [(x, z, false)])

/-- The floor is required only on reachable, positive-probability deferred bad flags.
It is conditional on the colluder's seed when used in the protocol theorem. -/
def UniformFloor {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (φ : Z → ℝ) (π : Hist X Z → X → ℝ)
    (η : ℝ) (a : Service X Z) (b n u : ℕ) (h : Hist X Z)
    (α : ℝ) : Prop :=
  ∀ k v g x z, Reach Bad M φ π η a b n u h (k + 1) v g →
    b ≤ v → Bad x → 0 < π g x → 0 < M x z →
    0 < 1 - φ z → 0 < 1 - η → α ≤ a g x z

def PairCore {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (M : X → Z → ℝ) (PH : X → ℝ) (ρ : Ω → ℝ)
    (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ)
    (r η : ℝ) : Prop :=
  IsDist PH ∧ IsDist ρ ∧ ∀ ω, Core M (φ ω) (π ω) r η

def ProtocolFloor {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ)
    (η : ℝ) (a : Ω → Service X Z) (b N : ℕ) (α : ℝ) : Prop :=
  ∀ ω, IsService (a ω) ∧
    UniformFloor Bad M (φ ω) (π ω) η (a ω) b N 0 [] α

def Claim : Prop :=
  -- (a): halting recovery, including arbitrary conditional services.
  (∀ (X Z : Type) [Fintype X] [Fintype Z]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ)
      (a : Service X Z) (b n u : ℕ) (h : Hist X Z),
      catV Bad M φ π r 1 a b n u h = cat Bad M φ π r b n u h) ∧
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ)
      (a : Ω → Service X Z) (b N : ℕ) (ρ : Ω → ℝ)
      (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      protocolCatV Bad M PH κ nh r 1 a b N ρ φ π =
        protocolCat Bad M PH κ nh r b N ρ φ π) ∧
  (∀ (X Z : Type) [Fintype X] [Fintype Z]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η : ℝ)
      (a : Service X Z) (b : ℕ),
      Core M φ π r η → IsService a →
      ∀ n u h, 0 ≤ catV Bad M φ π r η a b n u h ∧
        catV Bad M φ π r η a b n u h ≤ 1) ∧
  -- (b): exact constant model's finite cap.
  (∀ (X Z : Type) [Fintype X] [Fintype Z]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α A : ℝ) (b : ℕ),
      Core M φ π r η → 0 ≤ α → α ≤ 1 → 0 ≤ A → A ≤ 1 →
      (∀ x, Bad x → E (M x) φ ≤ A) →
      ∀ n u h, catD Bad M φ π r η α b n u h ≤
        finiteCap r A (theta η α) b n u) ∧
  -- Missing bridge repaired: any conditional service satisfying the floor.
  (∀ (X Z : Type) [Fintype X] [Fintype Z]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α : ℝ)
      (a : Service X Z) (b n u : ℕ) (h : Hist X Z),
      Core M φ π r η → IsService a → 0 ≤ α → α ≤ 1 →
      UniformFloor Bad M φ π η a b n u h α →
      catV Bad M φ π r η a b n u h ≤ catD Bad M φ π r η α b n u h) ∧
  -- (c): always-attack attains retry only at an exhausted budget,
  -- for an exact constant service, not for every service with that floor.
  (∀ (X Z : Type) [Fintype X] [Fintype Z] [DecidableEq X]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (r η α A : ℝ) (b n u : ℕ) (h : Hist X Z) (x : X),
      IsKernel M → Bad x → b ≤ u →
      catD Bad M (fun _ => A) (fun _ x' => if x' = x then 1 else 0)
        r η α b n u h = retry A (theta η α) n) ∧
  (∀ (A θ : ℝ) (n : ℕ),
      (θ + A * (1 - θ)) * retry A θ n =
        A * (1 - ((1 - A) * (1 - θ)) ^ n)) ∧
  (∀ (A θ : ℝ) (n : ℕ), 0 ≤ A → A ≤ 1 → 0 ≤ θ → θ ≤ 1 →
      0 < θ + A * (1 - θ) →
      retry A θ n ≤ A / (θ + A * (1 - θ))) ∧
  (∀ (A θ : ℝ), 0 ≤ A → A ≤ 1 → 0 ≤ θ → θ ≤ 1 → 0 < θ + A * (1 - θ) →
      Filter.Tendsto (fun n : ℕ => retry A θ n) Filter.atTop (nhds (A / (θ + A * (1 - θ))))) ∧
  -- (d): certificate for actual services with the conditional floor.
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (PH : X → ℝ) (nh ns b N : ℕ) (r η α L U : ℝ)
      (a : Ω → Service X Z) (ρ : Ω → ℝ)
      (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      PairCore M PH ρ φ π r η → 0 ≤ α → α ≤ 1 → 0 ≤ L →
      ProtocolFloor Bad M φ π η a b N α →
      (∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        survH t (hardKill ns) nh 0 *
          finiteCap r (min 1 (L * t)) (theta η α) b N 0 ≤ U) →
      protocolCatV Bad M PH (hardKill ns) nh r η a b N ρ φ π ≤ U) ∧
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (PH : X → ℝ) (nh ns b N : ℕ) (r η α L : ℝ)
      (a : Ω → Service X Z) (ρ : Ω → ℝ)
      (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      PairCore M PH ρ φ π r η → 0 ≤ α → α ≤ 1 → 0 ≤ L →
      ProtocolFloor Bad M φ π η a b N α → 0 < theta η α →
      (∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) →
      protocolCatV Bad M PH (hardKill ns) nh r η a b N ρ φ π ≤
        max (if 0 < b then
          (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) else 0)
          (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)) / theta η α)) ∧
  -- (e): universal-honeypot-law no-go; r need not be constrained
  -- because every available audit in this strategy is on a benign item.
  (∀ (PH : Bool → ℝ) (nh ns b N : ℕ) (r t : ℝ),
      IsDist PH → 0 ≤ t → t ≤ 1 →
      protocolCatD (X := Bool) (Z := Bool) (Ω := Unit)
        (fun x => x = true) (fun x z => if z = x then 1 else 0)
        PH (hardKill ns) nh r 0 0 b N (fun _ => 1)
        (fun _ z => if z = true then t else 0) (fun _ => burnThenAttack b) =
          binCDF nh ns (PH true * t) * (1 - (1 - t) ^ (N - b)) ∧
      (1 - t) ^ nh * (1 - (1 - t) ^ (N - b)) ≤
        binCDF nh ns (PH true * t) * (1 - (1 - t) ^ (N - b))) ∧
  -- At fixed 0 < t ≤ 1, the no-go limit is binCDF nh ns (PH true * t).
  -- At t = 0 the risk stays zero. Always-attack is not claimed to attain
  -- finiteCap before exhaustion.
  -- (e'): n_h is fixed while the deployment horizon grows.
  (∀ nh : ℕ, Filter.Tendsto
    (fun K : ℕ => (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ nh *
      (1 - (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ K))
    Filter.atTop (nhds 1))

noncomputable def witnessM : Unit → Unit → ℝ := fun _ _ => 1
noncomputable def witnessPhi : Unit → ℝ := fun _ => 1/10
noncomputable def witnessPi : Hist Unit Unit → Unit → ℝ := fun _ _ => 1
noncomputable def witnessService : Service Unit Unit :=
  fun h _ _ => if h = [] then 3/4 else 1/2

/-- Explicitly witnesses the model assumptions, conditional floor and domination,
including a genuinely history-dependent service and a nontrivial certificate. -/
def Witness : Prop :=
  Core witnessM witnessPhi witnessPi 1 0 ∧
  IsDist (fun _ : Unit => (1 : ℝ)) ∧
  IsService witnessService ∧
  UniformFloor (fun _ : Unit => True) witnessM witnessPhi witnessPi
    0 witnessService 0 2 0 [] (1/2) ∧
  E (witnessM ()) witnessPhi = 1/10 ∧
  (∀ z : Unit, witnessM () z ≤ 1 *
    push witnessM (fun _ : Unit => (1 : ℝ)) z) ∧
  catV (fun _ : Unit => True) witnessM witnessPhi witnessPi
    1 0 witnessService 0 2 0 [] = 49/400 ∧
  catD (fun _ : Unit => True) witnessM witnessPhi witnessPi
    1 0 (1/2) 0 2 0 [] = 29/200 ∧
  catD (fun _ : Unit => True) witnessM witnessPhi witnessPi
    1 0 0 0 2 0 [] = 19/100 ∧
  finiteCap 1 (1/10) (1/2) 1 3 0 = 29/200 ∧
  catD (fun _ : Unit => True) witnessM witnessPhi witnessPi
    1 0 (1/2) 1 3 0 [] = 1/10 ∧
  (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    survH t (hardKill 0) 3 0 *
      finiteCap 1 (min 1 (1 * t)) (theta 0 (1/2)) 0 2 0 ≤ 1/2) ∧
  protocolCatV (X := Unit) (Z := Unit) (Ω := Unit) (fun _ => True)
    witnessM (fun _ => 1) (hardKill 0) 3 1 0
    (fun _ => witnessService) 0 2 (fun _ => 1)
    (fun _ => witnessPhi) (fun _ => witnessPi) = 35721/400000 ∧
  protocolCatD (X := Bool) (Z := Bool) (Ω := Unit) (fun x => x = true)
    (fun x z => if z = x then 1 else 0) (fun x => if x = true then 1 else 0)
    (hardKill 0) 2 1 0 0 1 3 (fun _ => 1)
    (fun _ z => if z = true then 1/2 else 0) (fun _ => burnThenAttack 1) = 3/16

end PL_UMDEFERF1

```

## VCVio statement file (proved): ControlStack/Refinement.lean
```lean
/-
Interface level (VCVio): operational refinement of the halting protocol UM(n_h, hard slack n_s, b, N).

The protocol is a trace-level `ProbComp` game. Every component is an arbitrary `ProbComp`; no finite
real-valued kernel is assumed. The pieces:
- shared seed `ω ← ρ`;
- honeypot test: `n_h` fresh calls of the monitor on fresh honeypots `H >>= M`. It is the same game as
  `ControlStack.Bridge.honeypotPasses`, so survival is binomial. The monitor survives iff #PASS ≤ n_s;
- deployment, `N` rounds:
  - the generator draws `x ← π ω hist` (an arbitrary history-dependent `ProbComp`);
  - the view is `z ← M x` (fresh mediator coins);
  - the monitor returns `pass ← D ω z` (stateless: a fresh call that sees only (ω, z));
- PASS: on a bad submission, catastrophe; on a benign one, it executes and the protocol continues;
- FLAG with an audit available (u < b): on a bad submission, the audit kernel `A hist x z` runs. If it
  catches the attack, that is **absorbing shutdown** (A11); otherwise the attack executes (catastrophe).
  On a benign submission the protocol continues with u + 1 (benign audits have no false positives here;
  they could only cause extra shutdowns, which can only lower the catastrophe probability);
- FLAG with no audit left: **halt** (safe).

The audit kernel may depend on the whole reached history and on fresh coins. Its only constraint is
**conditional recall ≥ r** on bad submissions (A6, STANDING): for every history h, every bad x and every view z,
Pr[A h x z = true] ≥ r.

Statements to prove (in `RefinementProof.lean`):
- `DeployClaim`: Pr[catastrophe | deployment from (u, h)] ≤ `cat` with constant r, where `cat` is a
  TEXTUAL COPY of `PL_UMPROTF1.cat` applied to the induced real kernels. Equality holds when the recall is
  exactly r on every bad submission.
- `ProtocolClaim`: Pr[catastrophe in the whole game] = Σ_ω Pr[ω]·binCDF(n_h, n_s, h_ω)·Pr[catastrophe in
  deployment | ω], with h_ω = Pr[PASS | a mediated honeypot]. This uses the independence of the test and
  deployment coins given ω, and the Bridge.
- `EndToEndClaim` (the operational form of PL_UMPROTF1's domination bound, all inside this project):
  if every bad submission's view law is L-dominated by the mediated honeypot law, then
  Pr[survive the test, then uncaught catastrophe] ≤ (1 − r) + r·L·(n_s + 1)/(n_h + 1),
  for every colluding pair (ρ, D, π) and every audit kernel with conditional recall ≥ r.

- `DeployGClaim` (primary, no hypotheses): Pr[catastrophe | deployment from (u, h)] EQUALS `catG`, the
  core recursion with the recall constant replaced by the audit's actual recall function
  (h, x, z) ↦ Pr[A h x z = true]. `DeployClaim` and `DeployExactClaim` follow from it.
- `AttainClaim` and `Witness`: a generator that submits a fixed bad x at once attains the core's T3*
  value operationally, and the hypotheses of `EndToEndClaim` are jointly satisfiable with a non-trivial bound.

Assumptions that are built into the game. They are load-bearing; they are not conveniences.
- The monitor is stateless with fresh coins (A1, A2): `D ω z` sees only the seed and the view. It cannot see a
  call index, the audit counter or whether a call is a test. A call-counting monitor that FLAGs the n_h test calls
  and PASSes the next one reaches catastrophe probability 1 (Sonnet's review), so this restriction IS the theorem.
- The audit kernel `A` is independent of the seed ω, and it is chosen after (ρ, D, π): worst case over all
  kernels with the stated recall.
- The generator is not shown the test outcome. This is without loss: given ω, the test coins are independent of
  deployment.
- Test before deployment (A4); absorbing shutdown on a catch (A11); halt on an unaffordable flag (A5).
- Every `ProbComp` probability is rational, and X, Z and Ω are `Fintype`.

`cat` (and `catG`) are textual copies of `PL_UMPROTF1.cat` (Lean v4.35 ledger project). `binCDF` and
`honeypotPasses` are IMPORTED from the proved Bridge. The ledger and this project are linked only by the
textual identity of `cat`. `EndToEndClaim` does not depend on that link: it is stated and proved here. It is more
general than the ledger's T3 in one respect (the recall may depend on (h, x, z)) and narrower in another (hard
slack and the domination form only).
-/
import ControlStack.HoneypotBridgeProof

open OracleComp

namespace ControlStack.Refine

open ControlStack.Bridge (honeypotPasses binCDF)

abbrev Hist (X Z : Type) := List (X × Z × Bool)

/-- textual copy of `PL_UMPROTF1.cat`: P(catastrophe in the remaining `n` rounds | `u` audits used,
history `h`) for real kernels -/
noncomputable def cat {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else cat Bad M φ π r b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 1 - r else cat Bad M φ π r b n (u + 1) (h ++ [(x, z, false)]))
                    else 0))

/-- `cat` with a history- and view-dependent recall function `R` in place of the constant `r` -/
noncomputable def catG {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R : Hist X Z → X → Z → ℝ) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else catG Bad M φ π R b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 1 - R h x z else catG Bad M φ π R b n (u + 1) (h ++ [(x, z, false)]))
                    else 0))

/-- the deployment phase; `true` = uncaught catastrophe -/
def deploy {X Z : Type} (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X)
    (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ProbComp Bool
  | 0, _, _ => pure false
  | n + 1, u, h => do
      let x ← π h
      let z ← M x
      let pass ← D z
      if pass then
        (if Bad x then pure true else deploy Bad π M D A b n u (h ++ [(x, z, true)]))
      else if u < b then
        (if Bad x then (fun caught => !caught) <$> A h x z
         else deploy Bad π M D A b n (u + 1) (h ++ [(x, z, false)]))
      else pure false

/-- the whole protocol game; `true` = the colluding pair survived the test and then caused an uncaught
catastrophe -/
def protocolGame {X Z Ω : Type} (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω)
    (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) :
    ProbComp Bool := do
  let ω ← ρ
  let k ← honeypotPasses H M (D ω) nh
  if k ≤ ns then deploy Bad (π ω) M (D ω) A b N 0 [] else pure false

/-- the deployment game's catastrophe probability is exactly `catG` with the audit's recall function
(no hypotheses) -/
def DeployGClaim : Prop :=
  ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z),
    (Pr[= true | deploy Bad π M D A b n u h]).toReal =
      catG Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D z]).toReal)
        (fun h x => (Pr[= x | π h]).toReal) (fun h x z => (Pr[= true | A h x z]).toReal) b n u h

/-- refinement of the deployment phase by the core recursion with constant recall `r` -/
def DeployClaim : Prop :=
  ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (r : ℝ) (b : ℕ),
    (∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) →
    ∀ n u h, (Pr[= true | deploy Bad π M D A b n u h]).toReal ≤
      cat Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D z]).toReal)
        (fun h x => (Pr[= x | π h]).toReal) r b n u h

/-- equality at exact recall -/
def DeployExactClaim : Prop :=
  ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (r : ℝ) (b : ℕ),
    (∀ h x z, Bad x → (Pr[= true | A h x z]).toReal = r) →
    ∀ n u h, (Pr[= true | deploy Bad π M D A b n u h]).toReal =
      cat Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D z]).toReal)
        (fun h x => (Pr[= x | π h]).toReal) r b n u h

/-- the whole game factorises through the seed: test survival is binomial, then deployment -/
def ProtocolClaim : Prop :=
  ∀ (X Z Ω : Type) [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ),
    (Pr[= true | protocolGame Bad ρ H M D π A nh ns b N]).toReal =
      ∑ ω, (Pr[= ω | ρ]).toReal * binCDF nh ns (Pr[= true | H >>= M >>= D ω]).toReal *
        (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal

/-- end-to-end operational safety bound (domination form, hard slack) -/
def EndToEndClaim : Prop :=
  ∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ)
    (r L : ℝ),
    0 ≤ r → r ≤ 1 → 0 ≤ L →
    (∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) →
    (∀ x, Bad x → ∀ z, (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) →
    (Pr[= true | protocolGame Bad ρ H M D π A nh ns b N]).toReal ≤
      (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)))

/-- operational attainment (the core's T3*): a generator that submits a fixed bad `x` at once, with recall
exactly `r` at the root history, `N ≥ 1` and `b ≥ 1` -/
def AttainClaim : Prop :=
  ∀ (X Z Ω : Type) [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) (r : ℝ) (x : X),
    Bad x → 1 ≤ N → 1 ≤ b → (∀ z, (Pr[= true | A [] x z]).toReal = r) →
    (Pr[= true | protocolGame Bad ρ H M D (fun _ _ => pure x) A nh ns b N]).toReal =
      ∑ ω, (Pr[= ω | ρ]).toReal * binCDF nh ns (Pr[= true | H >>= M >>= D ω]).toReal *
        (1 - r + r * (Pr[= true | M x >>= D ω]).toReal)

/-- Non-vacuity, mirroring PL_UMPROTF1.Witness. X = Z = Bool, Bad = {true}, identity mediator, honeypots
`pure true` (so L = 1), a perfect audit (r = 1), n_h = 3, n_s = 0, b = N = 1. The monitor PASSes w.p. 1/4
(a uniform draw from Fin 4 equal to 0), and the generator always attacks. Its catastrophe probability is
(3/4)^3 · 1/4 = 27/256, which is below the EndToEnd bound 1/4. -/
def Witness : Prop :=
  (Pr[= true | protocolGame (fun x : Bool => x = true) (pure ()) (pure true)
      (fun x => pure x) (fun _ _ => (fun k : Fin 4 => decide (k = 0)) <$> $[0..3])
      (fun _ _ => pure true) (fun _ _ _ => pure true) 3 0 1 1]).toReal = 27/256 ∧
  (∀ z : Bool, (Pr[= z | (pure true : ProbComp Bool)]).toReal ≤
      1 * (Pr[= z | (pure true : ProbComp Bool) >>= (fun x => pure x)]).toReal) ∧
  (27/256 : ℝ) < (1 - 1) + 1 * (1 * (((0 : ℝ) + 1) / ((3 : ℝ) + 1)))

end ControlStack.Refine

```

## Dependency statements (frozen, verified)
```lean
namespace PL_UMHSF1
open Finset

/-! Control stack, collusion layer (DESIGN.md v1 §3, campaign UMHS): testing infrastructure.
Classical (hypothesis-testing form of (ε,δ)-indistinguishability; data processing; maximal leakage,
Issa–Wagner–Kamath 2020); stated here as infrastructure lemmas for the stack.

Finite laws are real-valued functions on a `Fintype`; a randomised stateless monitor rule is a function
`φ : Z → ℝ` with values in `[0,1]` (probability of PASS on view `z`). -/

/-- expectation of `f` under the finite (sub)law `P` -/
def E {Z : Type} [Fintype Z] (P f : Z → ℝ) : ℝ := ∑ z, P z * f z

/-- pushforward of a finite law `P` on `X` through a kernel `M : X → Z → ℝ` -/
def push {X Z : Type} [Fintype X] (M : X → Z → ℝ) (P : X → ℝ) : Z → ℝ :=
  fun z => ∑ x, P x * M x z

/-- hockey-stick divergence `∑ (P − e^η Q)₊`; at `η = 0` it is total variation for laws -/
noncomputable def hs {Z : Type} [Fintype Z] (η : ℝ) (P Q : Z → ℝ) : ℝ :=
  ∑ z, max 0 (P z - Real.exp η * Q z)

def IsDist {X : Type} [Fintype X] (P : X → ℝ) : Prop := (∀ x, 0 ≤ P x) ∧ ∑ x, P x = 1
def IsKernel {X Z : Type} [Fintype Z] (M : X → Z → ℝ) : Prop := ∀ x, IsDist (M x)
def IsRule {Z : Type} (φ : Z → ℝ) : Prop := ∀ z, 0 ≤ φ z ∧ φ z ≤ 1

/-- point mass -/
def delta {C : Type} [DecidableEq C] (e : C) : C → ℝ := fun e' => if e' = e then 1 else 0

/-- the content law `c # P` -/
def contentLaw {X C : Type} [Fintype X] [DecidableEq C] (c : X → C) (P : X → ℝ) : C → ℝ :=
  push (fun x => delta (c x)) P

/-- `M` is content-preserving for the content map `c`: a decoder recovers `c x` from every view that
`M x` can produce -/
def ContentPreserving {X Z C : Type} (M : X → Z → ℝ) (c : X → C) : Prop :=
  ∃ g : Z → C, ∀ x z, M x z ≠ 0 → g z = c x

/-- `M` is content-only for `c`: it factors through `c` via a kernel `K` -/
def ContentOnly {X Z C : Type} [Fintype Z] (M : X → Z → ℝ) (c : X → C) : Prop :=
  ∃ K : C → Z → ℝ, IsKernel K ∧ ∀ x, M x = K (c x)

def Claim : Prop :=
  -- T2 (every real η): honeypot-constrained pass rate, for every [0,1]-valued rule
  (∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q φ : Z → ℝ), IsRule φ →
      E P φ ≤ Real.exp η * E Q φ + hs η P Q) ∧
  -- T2 attainment by a deterministic rule
  (∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q : Z → ℝ),
      ∃ φ, IsRule φ ∧ E P φ = Real.exp η * E Q φ + hs η P Q) ∧
  -- T1: distinguishing advantage ≤ TV (= hs 0) for laws
  (∀ (Z : Type) [Fintype Z] (P Q φ : Z → ℝ), IsDist P → IsDist Q → IsRule φ →
      |E P φ - E Q φ| ≤ hs 0 P Q) ∧
  -- T4a: data processing through any kernel
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (η : ℝ) (K : X → Z → ℝ) (P Q : X → ℝ),
      IsKernel K → hs η (push K P) (push K Q) ≤ hs η P Q) ∧
  -- T4b: content-factorisation upper bound
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η : ℝ)
      (M : X → Z → ℝ) (c : X → C) (PA PH : X → ℝ), ContentOnly M c →
      hs η (push M PA) (push M PH) ≤ hs η (contentLaw c PA) (contentLaw c PH)) ∧
  -- T4c: floor for content-preserving mediators (exact decoder)
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η : ℝ)
      (M : X → Z → ℝ) (c : X → C) (PA PH : X → ℝ),
      IsKernel M → ContentPreserving M c →
      hs η (contentLaw c PA) (contentLaw c PH) ≤ hs η (push M PA) (push M PH)) ∧
  -- T4c-approx: floor with a decoder that errs with probability ≤ γ on every submission
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η γ : ℝ)
      (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PA PH : X → ℝ),
      IsKernel M → IsDist PA → IsDist PH →
      (∀ x, ∑ z, M x z * (if g z = c x then 0 else 1) ≤ γ) →
      hs η (contentLaw c PA) (contentLaw c PH)
        ≤ hs η (push M PA) (push M PH) + (1 + Real.exp η) * γ) ∧
  -- T5d: perturbation lemma
  (∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q P' Q' : Z → ℝ),
      hs η P Q ≤ hs η P' Q' + ∑ z, max 0 (P z - P' z) + Real.exp η * ∑ z, max 0 (Q' z - Q z)) ∧
  -- T4c': maximal-leakage floor: no law Q (in particular no mediated honeypot law) admits a
  -- likelihood-ratio constant below ∑_z max_{x∈B} M x z, and that value is attained
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (B : Finset X) (hB : B.Nonempty)
      (Q : Z → ℝ) (L : ℝ), IsKernel M → IsDist Q → (∀ x ∈ B, ∀ z, M x z ≤ L * Q z) →
      ∑ z, B.sup' hB (fun x => M x z) ≤ L) ∧
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (B : Finset X) (hB : B.Nonempty),
      IsKernel M → ∃ Q, IsDist Q ∧
        ∀ x ∈ B, ∀ z, M x z ≤ (∑ z', B.sup' hB (fun x' => M x' z')) * Q z) ∧
  -- domination from class coverage (content-only mediators): if every bad class has honeypot mass
  -- at least p > 0, bad submissions' views are dominated by (1/p) × the mediated honeypot law
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C]
      (M : X → Z → ℝ) (c : X → C) (PH : X → ℝ) (Bad : X → Prop) (p : ℝ),
      ContentOnly M c → IsDist PH → 0 < p → (∀ x, Bad x → p ≤ contentLaw c PH (c x)) →
      ∀ x, Bad x → ∀ z, M x z ≤ (1 / p) * push M PH z)

/-- Non-vacuity: concrete instances where each hypothesis class is inhabited non-trivially. -/
def Witness : Prop :=
  -- TV of (3/4,1/4) vs (1/4,3/4) is 1/2: T1 is informative
  hs 0 (fun b : Bool => if b then (3/4 : ℝ) else 1/4) (fun b => if b then 1/4 else 3/4) = 1/2 ∧
  -- the identity mediator on Bool is a kernel, content-preserving and content-only for `id`
  IsKernel (fun (x : Bool) (z : Bool) => if z = x then (1 : ℝ) else 0) ∧
  ContentPreserving (fun (x : Bool) (z : Bool) => if z = x then (1 : ℝ) else 0) id ∧
  ContentOnly (fun (x : Bool) (z : Bool) => if z = x then (1 : ℝ) else 0) id ∧
  -- maximal leakage of the identity mediator on two submissions is 2 (= number of classes)
  ∑ z : Bool, (Finset.univ : Finset Bool).sup' Finset.univ_nonempty
      (fun x => if z = x then (1 : ℝ) else 0) = 2

end PL_UMHSF1
namespace PL_UMSURVF1
open Finset

/-! Control stack, collusion layer (DESIGN.md v1 §3, campaign UMSURV): survival of the upfront
honeypot test.  n honeypots are drawn iid from the mediated honeypot law `q`; a stateless monitor rule
`φ` PASSes view `z` with probability `φ z` (a PASS on a honeypot is a miss); the (j+1)-th miss triggers
shutdown with probability `κ j` (a trusted, observable shutdown schedule).
Classical counting (truncated binomial first-moment identity; Bernoulli/AM-GM), as infrastructure. -/

/-- P(the colluding monitor survives the remaining `n` honeypots | `j` misses so far) -/
def surv {Z : Type} [Fintype Z] (q φ : Z → ℝ) (κ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n + 1, j => ∑ z, q z * ((1 - φ z) * surv q φ κ n j + φ z * (1 - κ j) * surv q φ κ n (j + 1))

/-- the same recursion as a function of the per-honeypot pass probability `h` only -/
def survH (h : ℝ) (κ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n + 1, j => (1 - h) * survH h κ n j + h * (1 - κ j) * survH h κ n (j + 1)

/-- hard slack: the (ns+1)-th miss shuts down -/
def hardKill (ns : ℕ) : ℕ → ℝ := fun j => if ns ≤ j then 1 else 0

/-- soft slack: every miss shuts down with probability `1/ns` (a trusted coin; inspired by LASR
App. B.5, not a model of retraining) -/
noncomputable def softKill (ns : ℕ) : ℕ → ℝ := fun _ => 1 / (ns : ℝ)

/-- binomial CDF `P(Bin(n,h) ≤ s)` -/
def binCDF (n s : ℕ) (h : ℝ) : ℝ :=
  ∑ j ∈ range (s + 1), (n.choose j : ℝ) * h ^ j * (1 - h) ^ (n - j)

def Claim : Prop :=
  -- T3b: survival depends on the rule only through the honeypot pass rate h = ∑ q φ
  (∀ (Z : Type) [Fintype Z] (q φ : Z → ℝ) (κ : ℕ → ℝ) (n j : ℕ), ∑ z, q z = 1 →
      surv q φ κ n j = survH (∑ z, q z * φ z) κ n j) ∧
  -- T3b, hard slack: survival is the binomial CDF
  (∀ (h : ℝ) (n ns : ℕ), survH h (hardKill ns) n 0 = binCDF n ns h) ∧
  -- T3b, constant (soft) schedule: survival is (1 − κ h)^n
  (∀ (h k : ℝ) (n : ℕ), survH h (fun _ => k) n 0 = (1 - k * h) ^ n) ∧
  -- T3c: truncated binomial first-moment bound
  (∀ (n s : ℕ) (h : ℝ), 0 ≤ h → h ≤ 1 → h * binCDF n s h ≤ ((s : ℝ) + 1) / ((n : ℝ) + 1)) ∧
  -- T3c': constant schedule
  (∀ (n : ℕ) (h k : ℝ), 0 ≤ h → h ≤ 1 → 0 < k → k ≤ 1 →
      h * (1 - k * h) ^ n ≤ 1 / (k * ((n : ℝ) + 1))) ∧
  -- survival is a probability whenever h and κ are
  (∀ (h : ℝ) (κ : ℕ → ℝ) (n j : ℕ), 0 ≤ h → h ≤ 1 → (∀ i, 0 ≤ κ i ∧ κ i ≤ 1) →
      0 ≤ survH h κ n j ∧ survH h κ n j ≤ 1)

/-- Non-vacuity: three honeypots, no slack, pass probability 1/4: survival (3/4)^3 = 27/64, and the
counting bound 1/4 is informative (1/4 · 27/64 < 1/4); soft slack with n_s = 5 on 100 honeypots gives
the non-trivial bound 5/101. -/
def Witness : Prop :=
  survH (1/4) (hardKill 0) 3 0 = 27/64 ∧ binCDF 3 0 (1/4) = 27/64 ∧
  (1/4 : ℝ) * binCDF 3 0 (1/4) < ((0 : ℝ) + 1) / ((3 : ℝ) + 1) ∧
  1 / ((1 / (5 : ℝ)) * ((100 : ℝ) + 1)) = 5 / 101

end PL_UMSURVF1
namespace PL_UMPROTF1
open Finset PL_UMHSF1 PL_UMSURVF1

/-! Control stack, collusion layer (DESIGN.md v1 §2.2, §3, campaign UMPROT): protocol safety of
untrusted monitoring with an upfront honeypot test.  Depends on PL_UMHSF1 and PL_UMSURVF1.

Protocol UM(n_h, κ, b, N), halting variant.
- Honeypot test: `surv (push M PH) (φ ω) κ nh 0` (PL_UMSURVF1).
- Deployment rounds: the generator submits `x ~ π ω hist`; the view is `z ~ M x`; the monitor PASSes
  with probability `φ ω z`.
- PASS on a bad submission = catastrophe; PASS on a benign one executes harmlessly.
- FLAG with an audit available (u < b) uses an audit: a bad submission is caught with probability `r`,
  otherwise it executes (catastrophe); a benign one continues.
- FLAG with no audit available halts deployment (safe).
- The colluding pair shares a seed `ω ~ ρ`; the monitor is stateless (`φ ω` depends on the view only);
  the generator is an arbitrary history-dependent randomised policy.
- Event: uncaught catastrophe before shutdown/halt (it includes execution after a failed audit).
- Upper bounds are in the free-submission model: the generator picks any submission, including its task.
  This is stronger than an exogenous task stream, which is the special case of a generator that samples
  the task itself. -/

abbrev Hist (X Z : Type) := List (X × Z × Bool)

/-- P(catastrophe in the remaining `n` rounds | `u` audits used, history `h`) -/
noncomputable def cat {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else cat Bad M φ π r b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 1 - r else cat Bad M φ π r b n (u + 1) (h ++ [(x, z, false)]))
                    else 0))

/-- P(uncaught catastrophe) of the whole protocol -/
noncomputable def protocolCat {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ)
    (r : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * surv (push M PH) (φ ω) κ nh 0 * cat Bad M (φ ω) (π ω) r b N 0 []

def Claim : Prop :=
  -- T3a: first bad submission decides (budget-sensitive); every history, every adaptive generator
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r A : ℝ) (b : ℕ),
      IsKernel M → IsRule φ → (∀ h, IsDist (π h)) → 0 ≤ r → r ≤ 1 → 0 ≤ A → A ≤ 1 →
      (∀ x, Bad x → E (M x) φ ≤ A) →
      ∀ n u h, 0 ≤ cat Bad M φ π r b n u h ∧
        cat Bad M φ π r b n u h ≤ (if u < b then 1 - r + r * A else A)) ∧
  -- T3* attainment: a generator that submits a fixed bad x at once achieves the bound exactly
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] [DecidableEq X]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (φ : Z → ℝ) (x : X),
      IsKernel M → Bad x → 1 ≤ N → 1 ≤ b →
      protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (fun _ => φ)
          (fun _ _ x' => if x' = x then 1 else 0)
        = surv (push M PH) φ κ nh 0 * (1 - r + r * E (M x) φ)) ∧
  -- T3 (domination form, hard slack)
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r L : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      0 ≤ r → r ≤ 1 → 0 ≤ L →
      (∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) →
      protocolCat Bad M PH (hardKill ns) nh r b N ρ φ π
        ≤ (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)))) ∧
  -- T3 (hockey-stick form, hard slack)
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r η δ : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      0 ≤ r → r ≤ 1 → 0 ≤ δ →
      (∀ x, Bad x → hs η (M x) (push M PH) ≤ δ) →
      protocolCat Bad M PH (hardKill ns) nh r b N ρ φ π
        ≤ (1 - r) + r * (δ + Real.exp η * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)))) ∧
  -- T3 (domination form, soft slack κ ≡ 1/ns)
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r L : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      0 ≤ r → r ≤ 1 → 0 ≤ L → 1 ≤ ns →
      (∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) →
      protocolCat Bad M PH (softKill ns) nh r b N ρ φ π
        ≤ (1 - r) + r * (L * ((ns : ℝ) / ((nh : ℝ) + 1))))

/-- Non-vacuity: X = Z = Bool, Bad = {true}, identity mediator, honeypots = point mass on `true`
(so L = 1), r = 1, three honeypots, no slack, one round, one audit.  The colluder that passes with
probability 1/4 and always attacks has catastrophe probability (3/4)^3 · 1/4 = 27/256, below the
domination bound 1 · 1/4. -/
def Witness : Prop :=
  protocolCat (X := Bool) (Z := Bool) (Ω := Unit) (fun x => x = true)
      (fun x z => if z = x then 1 else 0) (fun x => if x = true then 1 else 0) (hardKill 0) 3
      1 1 1 (fun _ => 1) (fun _ _ => 1/4) (fun _ _ x => if x = true then 1 else 0) = 27/256 ∧
  (∀ z : Bool, (if z = true then (1 : ℝ) else 0) ≤ 1 * push (fun (x : Bool) (z : Bool) =>
      if z = x then (1 : ℝ) else 0) (fun x => if x = true then 1 else 0) z) ∧
  (27/256 : ℝ) < (1 - 1) + 1 * (1 * (((0 : ℝ) + 1) / ((3 : ℝ) + 1)))

end PL_UMPROTF1
namespace PL_UMSTRATF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

/-- Conditional on the shared seed, the per-class tests use independent samples and PASS coins. -/
def stratSurv {Z C : Type} [Fintype Z] (K : C → Z → ℝ) (Es : Finset C)
    (φ : Z → ℝ) (m sc : ℕ) : ℝ :=
  ∏ e ∈ Es, surv (K e) φ (hardKill sc) m 0

noncomputable def stratProtocolCat {X Z C Ω : Type}
    [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ)
    (c : X → C) (Es : Finset C) (m sc : ℕ) (r : ℝ) (b N : ℕ)
    (ρ : Ω → ℝ) (φ : Ω → Z → ℝ)
    (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * stratSurv K Es (φ ω) m sc *
    cat Bad (fun x => K (c x)) (φ ω) (π ω) r b N 0 []

/-- The counting upper bound and the explicit attainable curve.
The second conjunct does not assert tightness of the first conjunct. -/
def Claim : Prop :=
  (∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω]
      (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (Es : Finset C)
      (m sc b N : ℕ) (r : ℝ) (ρ : Ω → ℝ)
      (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) →
      (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 →
      (∀ x, Bad x → c x ∈ Es) →
      stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤
        (1 - r) + r * (((sc : ℝ) + 1) / ((m : ℝ) + 1))) ∧
  (∀ (X Z C : Type) [Fintype X] [Fintype Z]
      [DecidableEq C] [DecidableEq X]
      (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (g : Z → C)
      (Es : Finset C) (m sc b N : ℕ) (r t : ℝ) (x : X),
      IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) →
      Bad x → c x ∈ Es → 1 ≤ N → 1 ≤ b → 0 ≤ t → t ≤ 1 →
      stratProtocolCat Bad K c Es m sc r b N
          (fun _ : Unit => 1)
          (fun _ z => if g z = c x then t else 0)
          (fun _ _ x' => if x' = x then 1 else 0) =
        binCDF m sc t * (1 - r + r * t))

def witnessK (e z : Bool) : ℝ := if z = e then 1 else 0

noncomputable def witnessPhi : Unit → Bool → ℝ :=
  fun _ z => if z = true then 1 / 6 else 0

def witnessPi : Unit → Hist Bool Bool → Bool → ℝ :=
  fun _ _ x => if x = true then 1 else 0

/-- Two tested classes, a nonempty catastrophe set, exact decoding,
a valid colluding pair, and positive catastrophe probability below the bound.
All hypotheses of both Claim conjuncts are represented at this instance. -/
def Witness : Prop :=
  IsKernel witnessK ∧
  (∀ e z : Bool, witnessK e z ≠ 0 → id z = e) ∧
  IsDist (fun _ : Unit => (1 : ℝ)) ∧
  (∀ ω : Unit, IsRule (witnessPhi ω)) ∧
  (∀ (ω : Unit) (h : Hist Bool Bool), IsDist (witnessPi ω h)) ∧
  (∀ x : Bool, x = true → id x ∈ (Finset.univ : Finset Bool)) ∧
  (∃ x : Bool, x = true) ∧
  (true = true) ∧
  (id true ∈ (Finset.univ : Finset Bool)) ∧
  (Finset.univ : Finset Bool).card = 2 ∧
  (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 ∧
  (0 : ℝ) ≤ 1 / 6 ∧ (1 / 6 : ℝ) ≤ 1 ∧
  (1 : ℕ) ≤ 1 ∧
  (∀ z : Bool,
    witnessPhi () z = if id z = id true then (1 / 6 : ℝ) else 0) ∧
  (∀ (ω : Unit) (h : Hist Bool Bool) (x : Bool),
    witnessPi ω h x = if x = true then (1 : ℝ) else 0) ∧
  stratProtocolCat (fun x : Bool => x = true)
      witnessK id (Finset.univ : Finset Bool) 12 1 1 1 1
      (fun _ : Unit => 1) witnessPhi witnessPi =
    binCDF 12 1 (1 / 6) * (1 - 1 + 1 * (1 / 6 : ℝ)) ∧
  (1 - (1 : ℝ)) + 1 * (((1 : ℝ) + 1) / ((12 : ℝ) + 1)) = 2 / 13 ∧
  0 < stratProtocolCat (fun x : Bool => x = true)
      witnessK id (Finset.univ : Finset Bool) 12 1 1 1 1
      (fun _ : Unit => 1) witnessPhi witnessPi ∧
  stratProtocolCat (fun x : Bool => x = true)
      witnessK id (Finset.univ : Finset Bool) 12 1 1 1 1
      (fun _ : Unit => 1) witnessPhi witnessPi < (2 / 13 : ℝ)

end PL_UMSTRATF1

```