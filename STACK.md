# STACK: strategy-free (adversary-quantified) control guarantees, conditional on explicit trust hypotheses; status 2026-10-07 (session 2, after `reviews/final-review2-Reviewer A.md`)

**Reading guide (after the final hostile review, `reviews/final-review-{Reviewer A,Reviewer B}.md`).**
- Every row is a *conditional* theorem about an idealised finite model. The adversary is universally quantified, which
  makes the bounds independent of the adversary's strategy WITHIN THE MODELLED CLASS (stateless fresh-context monitor,
  shared seed, single-step Bad). Capability re-enters through L, r, α, the scaffold and the model class. A1–A11 are
  defined in DESIGN §2.3.
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
    per-generator subtraction (Reviewer A, final review 2). The 1 − r value is T3a at A = 0 together with UMUSE (c').
  - **Honest-free floor (AOQL; Reviewer B, final review 2).** The view-blind pair at ANY h is a colluding pair. So, with
    nonempty Bad and N ≥ 1, sup-risk ≥ max_h survH(h)·(1 − r + r·h) for b ≥ 1 (and max_h survH(h)·h at b = 0), with no
    honest profile, mediator or L. For r = 1 and hard slack this is max_h h·binCDF(n_h, n_s, h): the average outgoing
    quality limit (AOQL) of the single-sampling plan (n_h, c = n_s) (Dodge–Romig acceptance sampling). The honeypot
    test IS an acceptance-sampling plan, and UMSURV's survival is its OC curve. At L = 1, UMPROT's honeypot term
    (n_s+1)/(n_h+1) is therefore tight within a factor ≤ e: the ratio is about 1/e at n_s = 0, 0.535 at
    (100, 5), and 0.764 at (1000, 59). UMCERTF1 (F)/(X) state the floor and its exactness at L = 1 as ledger theorems; (Xp) gives exactness for decodable content-only mediators.
  - Usefulness is in Lean as honest full-run availability and exact honest-side identities (UMUSEF1). The only
    coupling to risk is mimicry: a view-blind colluder that passes honeypots at the honest rate α₀ is a colluding
    pair, so every universal certificate X satisfies X ≥ risk(view-blind at α₀) ≥ α₀·u (nonempty Bad, N ≥ 1). The
    honest-free AOQL floor above dominates this. The usefulness-forced slack cost is Cantelli (d); its composition with
    UMPROT's honeypot term is not a Lean theorem. Usefulness-constrained protocol optimisation remains open.
- **Coarse-regime caveat** (a labelled numerical scenario, DESIGN §5 and `numerics/umuse_frontier.out`: r = 1, δ = 0,
  content-only M, an honest honeypot-test false shutdown ≤ 10%, n_h ≤ 100).
  - Risk ≲ 0.1 needs a small honest miss rate α₀ ≲ 0.01 AND about k ≤ 4–8 Red-choosable bad classes surviving
    mediation. At α₀ = 0.05, k = 8 the class-aware value is 0.163, and global slack gives 0.26–0.48.
  - These are sups over the one-class colluder family (lower bounds on the worst case; for r = 1 they equal the
    class-aware design's exact sup). Since UMCERTF1 these values are EXACT worst cases ((S2), (Xp)) and Lean-checkable by grid certificates
    (fixture: certified 0.07 vs the counting 0.154 at m = 12, s_c = 1; exact 0.0683).
  - There, the untrusted monitor's value over a trusted class rule is *not* established.
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
- the ledger harness Lean gate (standard axioms only);
- an orchestrator fidelity audit (`campaigns/<C>/forms/<CID>/fidelity-orchestrator.md`).

No row has had a human expert review yet.

Statement sources are in `ledger/*.lean` and the model in `DESIGN.md` (v1).

Status legend:
- **verified**: kernel-checked, frozen statement;
- **pending**: frozen or draft, unproved;
- **open**: not yet formalised.

## Layer 1: collusion (untrusted monitoring with honeypots and a mediator)

| CID | plain-English guarantee | assumptions it needs (DESIGN §2.3) | protocols it speaks to | status |
|---|---|---|---|---|
| UMHSF1 | No monitor rule can pass attacks much more often than honeypots unless the mediated attack and honeypot laws differ. Precisely: pass(attack) ≤ e^η·pass(honeypot) + hs_η, attained by some [0,1] rule. Mediation never increases hs_η. An exact-decoder content-preserving mediator cannot reduce hs_η below the content-level value. With a decoder that errs with probability ≤ γ on **every** submission, it cannot go below that value minus (1+e^η)γ. For a chosen bad set B, no law Q on views has a likelihood-ratio constant below Σ_z max_{x∈B} M(x,z), the *exponentiated* maximal leakage. The attaining Q is an arbitrary view law, not necessarily a constructible honeypot law. | finite laws | the testing core of any honeypot-based untrusted-monitoring analysis (no protocol semantics involved) | **verified** (frozen c4a262fd3de3; Reviewer A + Reviewer C pass; gate: standard axioms) |
| UMSURVF1 | The honeypot test's survival depends only on the monitor's honeypot pass rate h. Hard slack: survival = P(Bin(n_h,h) ≤ n_s) and h·survival ≤ (n_s+1)/(n_h+1). Constant schedule κ ∈ (0,1]: survival = (1−κh)^{n_h} and h·survival ≤ 1/(κ(n_h+1)), i.e. n_s/(n_h+1) for κ = 1/n_s, n_s ≥ 1. | A1–A3 (fresh contexts, iid honeypots) | Greenblatt upfront synthetic testing; LASR slack | **verified** (frozen 89139ffcfe63; Reviewer A + Reviewer C pass; gate: standard axioms) |
| UMPROTF1 | **For every colluding pair** (shared seed, stateless monitor, adaptive generator, free choice of submission): P(survive the test, then uncaught catastrophe) ≤ (1−r) + r·L·(n_s+1)/(n_h+1) when every bad submission's view is L-dominated by the mediated honeypot law. Hockey-stick and soft-slack forms also hold. The first bad submission decides, **because catching an attack is absorbing shutdown** (A11): if a caught attack were merely blocked, the bound fails (Reviewer A: 3/4 > 1/2). The ledger recursion uses a *constant* audit recall r. A history-dependent recall ≥ r is proved only at the VCVio level (`RefinementProof.lean`), not ported to the ledger. One-shot attainment: S(h)(1−r+r·a). | A1–A11; L or δ is a hypothesis on the trusted mediator and honeypot law; r is STANDING. An absolute risk bound; usefulness: see UMUSEF1 | *motivated by* the upfront-honeypot mechanism of Greenblatt et al. §3.4, LASR, and Ctrl-Z App. E (upfront UM validation, shutdown thresholds). It is not a formalisation of LASR Eq. (1), which also has upfront audits, attack rates, defer dynamics and retraining slack, and no reduction to it is proved | **verified** (frozen 1385777cdd90; Reviewer A + Reviewer C pass; gate: standard axioms) |
| UMSTRATF1 | With a content-only mediator, m honeypots per bad class and class-aware shutdown, every colluding pair has risk ≤ (1−r) + r(s_c+1)/(m+1), with no *additional* class-count factor **at fixed per-class budget**. At a fixed total budget n_h = k·m, this is (1−r) + r·k(s_c+1)/(n_h+k), so the class count reappears. Under exact class decoding an explicit colluder attains binCDF(m,s_c,t)(1−r+rt); the counting bound itself is not claimed tight. | A1–A11 (it reuses the absorbing `cat`); content-only M; Blue can build honeypots per class | a design variant of the halting idealisation; no named protocol | **verified** (frozen d2b4b11507cc; Reviewer A + Reviewer C pass; gate: standard axioms) |
| UMNOGOF1 | If the mediator has an exact decoder for a content class and Bad has k distinct classes, then for **every** iid honeypot law one deterministic colluding pair wins, uniformly over every shutdown schedule, budget, recall and horizon N ≥ 1, with probability ≥ (1−1/k)^{n_h}. This holds in the free-submission model; availability on an exogenous task stream is not shown. It is a finite-sample bound, not a proof that no finite domination constant exists. | free-submission model (lower bound) | why decodable mediators (e.g. CANONF1's canonicaliser) with many Red-choosable bad classes cannot get small risk from iid honeypots at realistic n_h. LLM summarisers are not proved decodable, so they are not covered as stated | **verified** (frozen d251d71f8951; Reviewer A + Reviewer C pass; gate: standard axioms) |
| UMLOWERF1 | **Converse for nonadaptive joint test designs** (adaptive testers beat the formula, pointwise and after optimisation: UMADAPTF1; the adaptive converse t(1 − tn/k) is UMADAPTF1). Take a mediator with an exact decoder and k bad submissions in distinct classes. One explicit colluding pair has risk ≥ t(1 − t·n/(k(n_s+1))) against every NONADAPTIVE honeypot design (a joint law on n-tuples fixed before testing, independent of the seed), and for every r, b and N ≥ 1. Adaptive testers that choose later honeypots from earlier answers are NOT covered (Reviewer A: risk 0 < 3/8 is possible). The shutdown rule must continue on every pattern with ≤ n_s misses (global or class-aware slack). Extra rejection rules, such as inverse honeypots, can break this contract. The pair is a uniform seed on the k submissions; the monitor PASSes the decoded seed class w.p. t; the generator submits the seed. The decoder is fixed before the design. At t = min(1, k(n_s+1)/(2n)), risk ≥ min(1/2, k(n_s+1)/(4n)). With UMSTRATF1 (under the combined hypotheses), this gives order-of-budget scaling per distinguishable class; saturation and audit failures are handled separately | free-submission model; decodable mediator (lower bound); nonadaptive designs | why honeypot budget must scale with the number of distinguishable bad classes, for every nonadaptive design; the matching upper bound needs UMSTRATF1's content-only and coverage hypotheses, and the 1 − r floor remains | **verified** (frozen 8415ec049329; Reviewer A + Reviewer C pass, after a revise round that fixed the strategy before the design; gate: standard axioms) |
| UMADAPTF1 | **Converse for ADAPTIVE testers (session 3).** Adaptive tester: the next honeypot law depends on the full test history (honeypots, views, answers); a randomised final keep. Contract: the forced-FLAG reference run is accepted w.p. 1 (sufficient: keep = 1 on all-FLAG histories, i.e. any miss-only slack rule). (a) Against the UMLOWERF1 colluding pair, every such tester leaves risk ≥ t·max(0, 1 − t·n/k) (identical until bad); (a') ≥ min(1/2, k/(4n)) at t = min(1, k/(2n)). So the budget must grow linearly in the number k of decodable bad classes for EVERY adaptive tester; the (n_s+1) factor of UMLOWERF1 is lost. (c1) An explicit adaptive tester refutes UMLOWERF1's nonadaptive formula pointwise; (c2) a 3-class sticky tester has risk t − t³ + t⁴/3 < 1/2 for every t, below UMLOWERF1's optimised nonadaptive value 1/2. Witness: tight at 3/8; a tester rejecting the perfect record (contract violated) gives 1/8 | free-submission model; decodable mediator (lower bound); the tester's coins independent of the seed; the colluders do not see the test | closes the adaptive-design gap of UMLOWERF1 and shows its nonadaptive restriction is necessary | **verified** (frozen a416cc05f830; v0 Reviewer A minor + Reviewer B minor (pointwise overclaim); v1 Reviewer A + Reviewer C pass; 484-line proof; gate: standard axioms) |
| UMUSEF1 | **Usefulness companion and a usefulness-target obstruction.** The honest side of the same recursions: false halt = P(Bin(N, f₀) > b); honest completion = survH(α₀)·binCDF(N, b, f₀), for every valid schedule and for the class-aware product; the view-blind pair's exact risk. **D·risk = q·completion**. So, for a nonempty Bad and N ≥ 1, any universal risk certificate X and completion target u satisfy q·u ≤ D·X, hence α₀·u ≤ X: a protocol that keeps the honest monitor's full-run completion ≥ u cannot certify risk below u × the honest rule's honeypot test-pass rate α₀ (α₀ is a miss rate only if the honeypot law has that meaning). Also: Cantelli for both binomial tails (slack cost and sufficient slack); the honest ROC 1 − f₀ ≤ e^η α₀ + hs_η(M·μ, M·P_H), where mediation can only raise the floor; and at b = 0 the bound sharpens to L(n_s+1)/(n_h+1) | the honest half is conditional on a nominated honest rule φ₀ and a benign iid stream μ (NOT capability-free); completion is full-run availability, not task usefulness (a run that completes almost every task before halting gets 0). The operational (VCVio) bridge for honest completion is now proved in `ControlStack/OutcomeProof.lean` (session 3); the frozen docstring's "bridge for both" was premature when written | honest availability next to the safety bounds, plus a necessary lower constraint on universal certificates at an availability target. It is NOT an optimisation or Pareto result. Neighbours: Games for AI Control (framing); Ctrl-Z App. E (upfront UM validation, honest misses, thresholds); LASR B.3 | **verified** (frozen 61a4c0bdf711; v1 rejected by Reviewer A and Reviewer B; v2 → v2.1 after Reviewer A revise; Reviewer A + Reviewer C pass; 573-line proof; gate: standard axioms) |
| UMDEFERF1 | **Audit, then defer after exhaustion.** While audits remain, this is the halting protocol. An unaffordable FLAG halts w.p. η, otherwise it defers (a trusted replacement; continue at the same u). A deferred attack ends safely w.p. ≥ α under a UNIFORM CONDITIONAL FLOOR on every reachable deferred bad flag, which is a hypothesis; the floor bridge catV ≤ catD is a theorem. Results: (a) η = 1 recovers the core; (b) a finite retry certificate finiteCap (decide while audits remain, or burn them and retry), for every θ = η + (1−η)α ∈ [0,1]. It is an upper bound attained at an exhausted budget (Lean) and, numerically, before exhaustion when benign and bad views are separable; (c) exhausted-budget attainment, the closed form and the sharp ratio A/(θ + A(1−θ)); (d) a protocol certificate for the actual service, and the coarse bound max([0<b]((1−r) + rH), H/θ), with H = L(n_s+1)/(n_h+1). (In the docstring example θ ≈ 0.32 is a 32% conditional audit load on deferred items in an unmetered service; compare halting at b = 0, risk ≤ H ≈ 6·10⁻⁴ with no audits but no availability.) (e) no-go at θ = 0: a burn-then-attack colluder tuned to the horizon has risk tending to 1 over long horizons, against every two-point honeypot law | A1–A11; the conditional floor α (STANDING); replacement safety; an unmetered deferred-audit service; free submission without a benign-flag guard (for the no-go) | the proved guarantee for defer-style routing requires a uniform stopping hazard. (e) is a no-go only for the free-submission model without a benign-flag guard. Prior art: Shlegeris win/continue/lose; LASR u/(c+u) and B.6; Defer in Games for AI Control; Ctrl-Z | **verified** (frozen ad82ec06fc48; v1 major, v2 revise, v2.1 Reviewer A + Reviewer C pass; 714-line proof; gate: standard axioms) |
| UMCERTF1 | **Certificate form of UMPROT/UMSTRAT (session 3).** (R) In the halting protocol, every colluding pair (finite shared seed, stateless monitor, history-dependent generator) has risk ≤ U iff every ONE-SHOT pair does (a fixed bad x attacked in round 1 with a stateless rule ψ): value survH(E_{M·PH}ψ)·capB(E_{M x}ψ), capB = 1 − r + r·a (b ≥ 1) or a (b = 0); any valid κ, N ≥ 1. (C) Any envelope env of bad pass rates over the honeypot pass rate gives a sound certificate sup_t survH(t)·capB(min 1 (env t)) ≤ U; (E) L·t and e^η t + δ are envelopes; (G0) survH is antitone in the pass rate; (G), (CG), (SG) finite monotone GRID certificates check it with rational arithmetic; (D) never worse than the counting bounds. Exactness: (F) view-blind floor (the AOQL for hard slack at r = 1 or b = 0); (X) at perfect honeypots (L = 1 forces M x = push M PH); (Xp) for decodable content-only mediators with minimum class mass p (the DESIGN §5 global column); (S1)/(S2) the stratified design's exact worst case is max_t binCDF(m, s_c, t)·capB(t) under exact decoding, any b. Lean-checked fixtures: m = 12, s_c = 1: certified 0.07, exact ≈ 0.0683, counting 0.154; soft slack n_h = 100, n_s = 5: 0.019 vs 0.0495; L = 4, r = 9/10, n_h = 30, n_s = 1: 0.17 vs 0.332 | A1–A11 as UMPROTF1/UMSTRATF1; (R) is halting-specific (non-halting variants and phase-aware monitors excluded) | turns design tables into Lean-checked certificates; first milestone of a certificate checker (direction A) | **verified** (frozen 73c2633b1568; v0 Reviewer A major (overclaims only) + Reviewer B minor; v1 Reviewer A + Reviewer C pass; 750-line proof; gate: standard axioms) |
| CANONF1 | A verified canonicaliser for a toy imperative language. It preserves semantics, and its output is a unique normal form modulo for→while, `;`-association and local renaming. Laws that agree on classes become identical after mediation, so markers carried only by those freedoms are erased. | (a verified trusted component) | erases an *analogous* For/While channel in the specified toy language. LASR's Python pipeline would need a verified frontend and an observation-level theorem | **verified** (frozen d3d1dd97809f; Reviewer A + Reviewer C pass; gate: standard axioms) |

### Interface level (VCVio, `<research-root>/control-stack`, Lean v4.34; checked with `lake env lean` + `#print axioms`, not ledger-gated)
| file | guarantee | status |
|---|---|---|
| `ControlStack/Spike.lean` | T1 for *arbitrary* `ProbComp` distinguishers through a `ProbComp` mediator: \|Pr[D=1 ∣ mediated attack] − Pr[D=1 ∣ mediated honeypot]\| ≤ tvDist; data processing | checked, standard axioms |
| `ControlStack/HoneypotBridgeProof.lean` | The honeypot test as a crypto-style game. For arbitrary `ProbComp` honeypot law H, mediator M and monitor D (stateless, with fresh coins per call, automatically in `ProbComp`), the number of PASSes among n honeypots is exactly binomial: Pr[#PASS ≤ s] = binCDF(n, s, Pr[D passes a mediated honeypot]). This is an operational bridge to UMSURVF1's quantity, by textually identical `binCDF` definitions across the two projects | checked (67-line proof), standard axioms |
| `ControlStack/Refinement.lean` + `RefinementProof.lean` | **Operational adequacy (game = recursion) and end-to-end bound.** The halting protocol is a trace-level `ProbComp` game: shared seed; the honeypot test (fresh calls); then deployment with an adaptive `ProbComp` generator, a fresh mediator, a stateless monitor `D ω z`, and an audit kernel `A h x z` that may depend on the history and use fresh coins; absorbing shutdown on a catch; halt on an unaffordable flag. Proved (394 lines, isolated prover agent): (i) **DeployG**: P(catastrophe in deployment) = `catG` exactly, the core `cat` with the audit's actual recall function, with no hypotheses. Hence ≤ `cat` with constant r under conditional recall ≥ r, and = at exact recall. (ii) **Protocol**: the game factorises as Σ_ω Pr[ω]·binCDF(n_h, n_s, h_ω)·P(deploy catastrophe | ω). (iii) **EndToEnd**: under L-domination, every colluding pair and every audit kernel with conditional recall ≥ r has P(catastrophe) ≤ (1−r) + r·L(n_s+1)/(n_h+1). T3a and T3c were re-proved inside this project. (iv) **Attain**: a fixed-bad generator gives Σ ρ·binCDF·(1 − r + r·Pr[PASS | M x]). (v) Witness 27/256 < 1/4. Built-in, load-bearing assumptions: a stateless monitor with fresh coins (a call-counting monitor reaches 1), an audit independent of ω, test before deployment, no benign-audit false positives, rational probabilities, finite types. `cat` is linked to the ledger's `PL_UMPROTF1.cat` by textual identity only; EndToEnd does not need that link | checked, standard axioms (not ledger-gated). Design review: Reviewer B (minor; about 4000 exact game-vs-recursion instances, 0 mismatches) |

| `ControlStack/Outcome.lean` + `OutcomeProof.lean` | **Outcome-valued game (session 3, precursor 3).** The halting protocol returns one of five outcomes (complete, catastrophe, caught, rejected, halted). Proved (512 lines, isolated prover agent): its catastrophe marginal IS the Boolean `protocolGame` (program equality), so every Refine result transfers; the deployment outcome law is exactly four recursions `catG`, `caughtG`, `haltP` (textual copy of PL_UMUSEF1.haltP), `complG`, which conserve mass for any real φ, R and are nonnegative for lawful inputs; the whole law factorises through the seed (rejected = Σ ρ(1 − binCDF)). **Honest-completion bridge:** an honest seed-free monitor on an iid benign stream has Pr[complete] = binCDF(n_h, n_s, α₀)·binCDF(N, b, f₀), with α₀, f₀ PROVED equal to PL_UMUSEF1's missRate/flagRate of the induced kernels (textual copies) and haltP/complG proved binomial: the operational form of UMUSEF1 (a), (b). **Pareto identity** (operational UMUSEF1 (c'), (P)): in one configured protocol, the view-blind colluder (PASS w.p. α₀) has risk binCDF(n_h, n_s, α₀)·q and binCDF(N, b, f₀)·risk = q·Pr[complete | honest], so every certificate X for Unit-seed pairs satisfies q·Pr[complete] ≤ binCDF(N, b, f₀)·X. Safety and availability are measured in two runs (colluding vs honest) of the same protocol, not as two marginals of one run | checked, standard axioms (not ledger-gated). Design review: Reviewer A (major: rate-link overclaim, 'two marginals' overclaim; fixed in v1) and Reviewer B (same two majors; all claims brute-forced true) |
## Trusted-monitoring layer (direction A)

| CID | guarantee | assumptions | protocols | status |
|---|---|---|---|---|
| TMCERTF1 | Finite-horizon certificate bounds risk for every history-dependent Red and rectangular model choice; includes usefulness, least certificates, rational `decide +kernel` checking, convex-hull coverage, and abstraction soundness. | Finite lawful game; nonnegative continuation values; listed rows cover every concrete row for deployment. | Finite-state monitoring games with auditable rational transition tables; arbitrary Red policies within the model. | **verified** (frozen 53a3bc12f43c; 448-line proof; two-family red team pass; claim and witness gates, standard axioms) |
| TMGACF1 | Certified GAC instance: bridges safety and usefulness recurrences, grid enclosure, and exact separation 13/50 constant-rate vs 9/32 coin-count vs 11/32 clocked/full-information Red. | TMCERTF1; GAC threshold adapter lawfulness and stated ROC constraints; finite-horizon game. | GAC-style threshold auditing and attack-rate policies, including clocked and coin-aware Red. | **verified** (frozen 89331ac41986; 554-line proof; two-family red team pass; claim and witness gates, standard axioms) |

**Usefulness checker extension (in progress).** `ControlStack/UseQ.lean` contains an exact-rational `checkUseQ` and a Lean soundness bridge: an accepted sub-solution lower-bounds expected cumulative reward for a fixed honest action under every full-history-dependent admissible row selector, assuming nonnegative transitions on admissible rows. A positive one-state witness compiles. Claim and witness pass the ledger harness Lean gate with standard axioms; reviewer family red-team passed. A second foreign-family review was rejected by automatic review because it would send the private statement to a new destination; no freeze. `numerics/lasr_usefulness_certificate.lean` also passes the rational checker on the current 100-step interval fixture and proves the conditional floor `22873/250`; held-out deployment evidence remains open.

**Parameter-Lipschitz certificate transfer (TMLIPF1, draft).** Claim and witness pass local ledger harness gates with standard axioms. Two sandbox red-team attempts did not complete; external reviewer dispatch remains pending destination approval. The statement is not frozen.

## Layer 2: actions (reference monitor), first step

SANDBOXF1 models the research harness's sandbox for untrusted provers. It is *not yet* an action monitor for U's tool
calls, and it supplies no structural B̄ to layer 1 (Reviewer B B5).


| CID | guarantee | status |
|---|---|---|
| SANDBOXF1 | A model of the ledger harness sandbox (bubblewrap mount table). (a) The current policy does **not** confine host writes to scratch: `~/.elan` (executed by the gate) is writable. (b) A read-only-root fixed policy confines host writes to scratch and the declared state directories. (c) The current policy does hide the hidden directories, except through the read-only Mathlib re-bind. These are statements about **modelled pathname resolution**, not about host files. Hard links, symlinks and other aliases are outside the model (Reviewer A). Boundary assumptions: no `/proc/<pid>/root` alias (needs `--unshare-pid`), no network side channels. (a) remains a counterexample inside the model. | **model theorem verified** (frozen 85a64bdfb3ce). **System claim untested**: no canary write was run. **The proposed fix as written regresses hiding** (Reviewer B): state-directory binds are placed after the hiding tmpfs, so a state dir that is an ancestor of a hidden dir (e.g. ~/.agent-runtime over ~/.agent-runtime/sessions) re-exposes it. (b) is still true because it concerns writes only. Corrected in SANDBOX2F1 |
| SANDBOX2F1 | The corrected fix. (a) SANDBOXF1's proposed fix, with ~/.agent-runtime declared as a state directory, re-exposes the hidden ~/.agent-runtime/sessions (Reviewer B's regression, as a counterexample in the model). (b) The corrected policy `fixedPolicy2` places state-directory binds **before** the hiding tmpfs mounts; host writes stay inside scratch or a declared state directory. (c) Under `fixedPolicy2`, hiding holds for every choice of state directories, for the 11 modelled hidden DIRECTORIES: a read that reveals a host path inside one lands in the read-only Mathlib re-bind, which is an explicit read-only hole. Hidden FILES are not modelled: `~/.agent-runtime/history.jsonl` would be exposed when `~/.agent-runtime` is declared, unless its empty-file bind is placed after the state binds. Same model and boundary assumptions as SANDBOXF1. (c) needs scratch W under /var/tmp. (b) allows ARBITRARY declared state directories (declaring / would permit every write), so the declared write set is not a validated safe policy. The Witness uses canWrite = True (modelled access, not real permissions) | **model theorem verified** (frozen 094db3d3379a; Reviewer A + Reviewer C pass; gate: standard axioms). **Not deployed**: it needs John's OK, a CLI compatibility test (which state directories agent runtime/Reviewer C/prover agent need) and `--unshare-pid` |

## Existing verified results that slot into the stack (earlier sessions)
- **Trusted monitoring (Redwood):**
  - N1/N1b (`<research-root>/control-tree/lean/ControlTree.lean`): the audit-game structure, a single-rate saddle point,
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
  result warrants "apparently open" (Reviewer A, final review 2). An unmechanised result can subsume a CID's mathematical
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

## Sharper adaptive converse in progress

`ControlStack/AdaptiveBalance.lean` proves the discrete balancing lemma for exact class counts and the quotient/remainder bound. `ControlStack/AdaptiveSharp.lean` proves the weighted path aggregation and uniform-seed `t/k` corollary. The adaptive tester's all-FLAG path measure is not yet connected to those abstractions; UMADAPTF1 remains the verified `t(1 − tn/k)` theorem.

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
  abstract operational-model correspondence, not a deployed scaffold. `SoftSlack.lean` proves the VCVio soft-hazard
  honeypot survival bridge (with `ns = d+1` and an exact finite uniform coin), seed-conditional whole-protocol
  factorization, the scalar first-moment inequality `h(1-h/ns)^nh ≤ ns/(nh+1)`, and the end-to-end soft-slack bound
  `(1-r)+r·L·ns/(nh+1)` under row domination and worst-case recall (the same hypotheses as `RefinementProof.endToEnd`).
  `SoftHockey.lean` proves the operational pass bridge from finite hockey-stick divergence and the end-to-end bound
  `(1-r)+r·(δ+e^η·ns/(nh+1))` under a per-bad-row divergence bound and worst-case recall. `StratifiedGame.lean`
  models independent per-class hard-slack tests and proves their exact binomial product survival law, seeded protocol
  decomposition, and end-to-end bound `(1-r)+r·L·(sc+1)/(m+1)` under classwise domination, class coverage, and recall.
`DeferGame.lean` proves exact operational equality with a service-dependent `ENNReal` recursion, with a proved one-step probability expansion. The attempted calibrated real-valued bridge exposed a semantic mismatch: on an exhausted bad row, the operational game terminates with catastrophe probability `(1-η)(1-a)`, but `catV` multiplies that term by the recursive continuation value. The ledger theorem is not connected to this operational game; reconcile the intended post-service behavior before promoting a bridge. No frozen statement was changed.
  The honest-completion event is now in the game (`OutcomeProof.lean`).
6. **Out of model:**
   - stateful monitors and interleaved honeypots;
   - defer-on-exhaustion is now UMDEFERF1 (it needs a uniform stopping hazard; the honeypot term grows by up to 1/θ);
     metered or reserve-limited deferred audits are not in Lean;
   - multi-step attacks;
   - composition with trusted monitoring (a min, not a product, absent conditional independence);
   - LASR's retraining slack (an assumption about U's learning dynamics).
7. **Sample-to-deployment gap.** DESIGN-A2 now contains a real-data LASR score archive demonstration, including exact simultaneous bands and a kernel-checked 100-problem interval game. Its source data are not established as predeclared held-out IID samples from the deployment distribution; this verifies the table/checker pipeline conditionally and does not discharge environmental validity.
