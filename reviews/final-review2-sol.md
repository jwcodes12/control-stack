**The current positioning needs MAJOR revisions.** I found no FATAL defect in the supplied verified statements. The main failures concern scope, missing conditions in the prose, and claims about what has been formalised. UMDEFER remains pending; accepting its frozen specification is separate from accepting a proof.

I take the reported kernel gates as given. Statements and definitions omitted from this prompt receive a limited fidelity verdict.

1. **MAJOR — UMLOWERF1: “design-free” excludes adaptive test construction.**

   The quantifier order fixes the decoder before the design. For each fixed `t`, the same uniform seed law and class rule work against every admissible `D`. That revision addresses the earlier strategy-after-design problem.

   However, `D : (Fin n → X) → ℝ` samples an entire tuple independently of the seed. It does not represent a tester choosing later honeypots from earlier monitor answers. An adaptive testing algorithm can be initially independent of the secret seed while its resulting tuple becomes correlated with it.

   Concrete boundary: take four exactly decoded bad classes, `t = 1`, `n_s = 1`, and five tests. Scan classes until the first PASS, then repeat that class. Every seed produces two misses and shutdown. Risk is zero, whereas the displayed lower expression is
   \[
   1-\frac{5}{4\cdot2}=\frac38.
   \]
   This is outside the Lean theorem, not a contradiction of it.

   `TestSetup` also requires continuation on **every** tuple/pattern with at most `n_s` PASSes. Additional rejection criteria, such as an inverse-honeypot guard, need not satisfy that contract.

   **Fix:** call this a **converse for nonadaptive joint test designs under the stated miss-tolerance contract**. Qualify every “every design” occurrence accordingly. “Necessary and sufficient” should mean order-of-budget scaling under the combined lower and upper hypotheses, with saturation and audit failures handled separately.

   The mathematics is modest: average the miss count over the uniform seed, apply Markov at `n_s+1`, and use the first deployment PASS. Uniformity over `r`, `b`, and `N ≥ 1` comes from winning through that PASS; it does not establish a general audit-game lower bound.

2. **MAJOR — UMUSEF1: the obstruction’s prose omits nonempty Bad and `N ≥ 1`.**

   Exact statement: conjunct `(P)` requires `Bad x` and `1 ≤ N`. The row says that any universal certificate and completion target satisfy `α₀·u ≤ X` without stating those restrictions.

   At `N = 0`, catastrophe risk is zero while test survival—and therefore honest completion—can be positive. A positive `α₀·u` then contradicts the unqualified prose. With `Bad = ∅`, every colluding pair also has zero catastrophe risk, regardless of a positive test-pass rate.

   **Fix:** state the obstruction for **a nonempty bad set and a positive deployment horizon**, under `(P)`’s remaining hypotheses. Apply the same qualification to UMDEFER’s statement that targets below `1−r` are impossible when `b ≥ 1`.

   Also retain the distinction between a honeypot **test-pass rate** and a deployment attack miss rate. Calling `α₀` an honest backdoor miss rate requires the honeypot law to have the corresponding semantic interpretation.

3. **MAJOR — UMUSE positioning: a necessary constraint is being presented as an optimisation result.**

   Exact claims: “closes the always-flag loophole of every upper bound” and the disposition’s “UMUSE is the inf–sup objective for the hard-slack family.”

   `(P)` proves a necessary condition on universal certificates for fixed protocol parameters and a nominated honest profile. It does not define and solve a Blue optimisation problem, establish feasibility at a target, certify a Pareto frontier, or prove optimality. Full-run availability also differs from expected useful work: a run that completes almost every task before halting receives zero completion credit.

   **Fix:** replace those claims with:

   > UMUSE formalises honest full-run availability and a necessary lower constraint on universal safety certificates at an availability target. Usefulness-constrained protocol optimisation remains open.

   GAC already supplies the safety/usefulness optimisation framework. The new contribution here is the particular obstruction and its formalisation. [Games for AI Control, 2409.07985](https://arxiv.org/html/2409.07985v2)

4. **MAJOR — STACK reading guide and UMPROTF1: “gain over always-flag” needs a defined comparator.**

   The theorem bounds an **absolute joint catastrophe probability**. It does not subtract an always-flag execution.

   For the same generator, the comparison can behave differently: let it submit a benign item followed by a bad item, with one audit. Always-FLAG consumes the audit on the benign item and then halts safely. A rule that PASSes the benign item and FLAGs the bad one incurs risk `1−r`. Thus a per-generator excess bound cannot simply discard the `1−r` term.

   A worst-case comparison can be derived: with nonempty Bad, `N ≥ 1`, and `b ≥ 1`, the always-flag rule’s worst-case risk is exactly `1−r`; subtracting that **worst-case value** gives an excess comparison.

   **Fix:** label the existing bounds as absolute risk bounds. If retaining “gain,” define the supremum-based comparator and prove its corollary. Keep `b = 0` separate.

5. **MAJOR — UMSTRATF1’s assumption column omits A11.**

   Exact row: assumptions are listed as “A1–A10; content-only M; Blue can build honeypots per class.”

   `stratProtocolCat` calls the same absorbing `cat` recursion as UMPROTF1. Catching a bad submission ends deployment. The stratified theorem therefore inherits the absorbing-shutdown requirement.

   **Fix:** add A11 explicitly. The introductory reading guide does not repair an inaccurate per-row assumption list.

6. **MAJOR — UMUSE’s claimed operational bridge is absent from the supplied VCVio statements.**

   Exact assertion in UMUSE’s header: “The operational bridge for both is the VCVio refinement.”

   `Refinement.lean` proves catastrophe probabilities, their recursion correspondence, and the protocol bound. It contains no operational `haltP`, honest-completion event, or availability correspondence. Its Boolean result merges completion, caught shutdown, test rejection, and budget halt into `false`.

   **Fix:** instrument the operational game with distinct terminal outcomes—completion, catastrophe, caught shutdown, test rejection, and budget halt—and prove the honest availability correspondence. Until then, mark that bridge open.

   The existing refinement also establishes **abstract operational-model correspondence**, not correspondence to a deployed scaffold. Fresh calls, complete monitor inputs, and phase ordering are enforced by the model’s interface; their implementation remains unverified.

7. **MAJOR — UMDEFER: the conditional-floor bridge does not establish an actual incrimination service.**

   Exact statements: `UniformFloor`, `ProtocolFloor`, and the bridge `catV ≤ catD`.

   The floor is substantive: it holds after every relevant reachable history and, in the protocol theorem, separately for every seed. The theorem assumes that contract. It does not manufacture it from an average audit rate or from “fresh coins.”

   Independent selection with probability `q` is insufficient if the selected auditor has systematic blind spots. To derive `α = q·r`, selected audits need the appropriate **conditional recall floor** after the relevant histories. Full independence of catch outcomes is sufficient but stronger than necessary.

   Deferral also assumes complete removal of the proposed attack and a replacement that cannot cause the catastrophe. “Trusted” meaning nonscheming does not establish that property.

   **Fix:** add conditional incrimination recall and replacement safety to the central trust table. Label `α = q·r` as a separate service-construction obligation. A future formal construction should state its conditional recall premise explicitly.

   The deployment-wide audit-coin counterexample addresses a necessary-assumption question. It does not discharge that assumption.

8. **MINOR — UMDEFER: resource and reserve guarantees exceed the frozen `Claim`.**

   Exact prose: deferred-audit load is “up to `q(1−η)` per round,” and the bounds “also cover” halting when a separate reserve runs out.

   There is no `q`, reserve state, or audit-load variable in the frozen model. The load expression is an **expected** rate under a specified selection service, not a pathwise maximum. Reserve-triggered halting is not among the frozen conclusions.

   **Fix:** say “expected number of selected deferred audits is at most `Nq(1−η)` under this service construction.” Mark reserve monotonicity as pending until a metered-service extension proves it. These costs matter when comparing deferral with a protocol using the same total audit resources.

9. **MAJOR — proposed direction B: complete mediation alone cannot imply A4/A5/A11.**

   Exact proposal: prove those properties “follow from complete mediation.”

   Complete mediation requires effects to pass through the gate. It does not require testing before deployment, halting on budget exhaustion, or cancelling the run on a detected attack. A completely mediated system can approve deployment effects before testing finishes.

   SOUNDGATE’s cancellation property concerns subsequent releases after cancellation. The paper explicitly excludes rollback of effects already released and in flight. [SOUNDGATE, 2607.14166, §5.3](https://arxiv.org/pdf/2607.14166)

   **Fix:** prove a composition theorem for **gate + verified protocol driver + explicit execution-order contract**. It must specify phase ordering, budget decisions, catch-to-cancel ordering, and treatment of outstanding effects. Your longer proposal already mentions a driver; those obligations must remain visible in the final theorem.

   A Lean port of the admission core alone would not establish them.

10. **MAJOR — related-work audit: Ctrl-Z is undercounted as a UMUSE neighbour.**

   The audit associates UMUSE mainly with GAC’s framework. Ctrl-Z Appendix E directly discusses upfront untrusted-monitor validation, shutdown thresholds, honest misses, and the resulting safety/usefulness trade-off. It optimises those parameters against collusion strategies. That is closer to UMUSE’s object than a trusted-monitoring framework alone. [Ctrl-Z, 2504.10374, Appendix E](https://arxiv.org/html/2504.10374v1)

   LASR explicitly anticipates the honest-ability ceiling in B.3 and uses win/continue/lose dynamics in B.6. [LASR, 2602.20628](https://arxiv.org/html/2602.20628v1)

   **Fix:** add Ctrl-Z to UMUSE and UMPROT’s direct-neighbour references. Distinguish novel statements, new formal renditions, and new packaging. “None of six sources subsumes a CID” is too categorical: an unmechanised result can subsume its mathematical content even when it does not supply the proof-assistant artifact.

   I found no earlier machine-checked artifact for this particular UM theorem family in the searched material. That supports **“no comparable artifact found in this search,”** not a priority claim.

11. **MINOR — SANDBOX2F1: the model contract needs its parameter boundary stated explicitly.**

   The correction is consistent with the described mount model. Conjunct `(c)` nevertheless requires scratch `W` to lie under `/var/tmp`. Conjunct `(b)` allows arbitrary declared state directories: declaring the root makes its write-confinement conclusion permit essentially all host writes.

   The witness uses `canWrite = True`. It demonstrates possible modelled access, not real filesystem permissions or CLI compatibility.

   **Fix:** retain the pathname-model qualification, state the scratch restriction, and distinguish the declared write set from an independently validated safe write policy. For a stronger policy theorem, constrain state directories against trusted executable and security-critical locations.

   The parent pathname definitions were not supplied, so I cannot independently audit their encoding here. Nothing shown establishes host confinement or deployment readiness.

12. **MINOR — STACK has unsupported thresholds and stale status statements.**

   Exact locations:

   - “Only” coarse views with `k ≲ 4–8` work at realistic budgets: no budget, target risk, recall, or honest-profile assumptions accompany that threshold.
   - UMPROTF1 still says usefulness is not formalised.
   - Its conditional-recall refinement is called open despite the operational result; distinguish an open ledger port from a proved VCVio version.
   - UMDEFER lacks a pending stack row, while defer remains described as numerics only.
   - “A finite L always exists in a finite model” needs an existential choice of a covering honeypot law. For a fixed law missing an attack view’s support, no finite L exists.

   **Fix:** replace `4–8` with a parameterised feasibility statement or a labelled numerical scenario; synchronise status wording; and qualify the existence claim by constructibility and coverage.

   The critique disposition also overstates the rare-event connection. UMLOWER and UMSURV analyse protocol sampling; neither converts a benchmark average into a worst-case, history-conditional premise.

The package’s significance is limited to conditional analysis and assumption exposure. It provides quantitative reasons to reject some honeypot designs and distinguishes shutdown from silent suppression. It does not demonstrate that untrusted monitoring improves on a trusted class rule, certify useful worst-case recall for a concrete mediator/auditor, or establish deployed-system control.

Against the critique’s success criteria:

| Criterion | Judgment |
|---|---|
| Non-vacuity | Toy mathematical non-vacuity is demonstrated. Low-risk operation with meaningful useful work and bounded total resources is not. |
| Specification fidelity | Several prose claims exceed the supplied statements. Catastrophe correspondence is proved; honest-completion correspondence is absent. |
| Necessary assumptions | Counterexamples expose several failures. They do not establish the positive assumptions or exhaust omitted channels. |
| Decision relevance | Class-budget scaling and stopping hazards constrain idealised designs. Their relevance to a named implementation remains conditional. |
| Honest scope | Many qualifications are explicit, but the minimax, baseline-gain, operational-availability, and gate-entailment claims need correction. |

The classical neighbours are substantial. Universal adversary quantification is standard in information-theoretic security; probabilistic game verification already has reusable foundations in VCVio and SSProve. Effect enforcement has the reference-monitor lineage and current AI-specific formal work. Machine checking changes the evidential status of an artifact, not the novelty of the underlying inequality. [Dwork–Roth](https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf), [VCVio](https://eprint.iacr.org/2024/1819), [SSProve](https://eprint.iacr.org/2021/397.pdf), [Alignment Contracts, 2605.00081](https://arxiv.org/abs/2605.00081)

**Rank A above B, with a required scope correction to A.** GAC’s trusted-monitoring example restricts Red to a memoryless policy with a fixed backdoor probability `β`. Certifying its polynomial best response certifies that adversary class; it does not establish safety against history-aware Red. Blue’s dependence on remaining tasks and audit budget does not remove that restriction. [GAC, §4 and Appendix B](https://arxiv.org/html/2409.07985v2)

The **single most valuable next formalisation** is an A-derived certificate checker for a finite, stateful trusted-monitoring model with explicit adversary observations and uncertainty in conditional transitions.

Its soundness theorem should say:

> For a fixed Blue controller, a valid risk certificate bounds catastrophe probability for every admissible history-dependent Red policy and every admissible conditional transition model. A separate honest-mode certificate lower-bounds expected useful reward.

Use the GAC recursion as the first restricted instance and reuse N1b where its certificate hypotheses apply. The deliverable should include:

- explicit budget, feedback, observation, execution, and shutdown state;
- kernel-checkable inequalities covering admissible transitions after every relevant history;
- one certified risk/usefulness point and a counterexample showing when the fixed-`β` certificate fails under additional Red observations.

Checking rounded ROC inputs certifies the rounded model. Reproducing a published Beta-fixture number requires explicit approximation bounds.

This project would address the critique’s proposed certificate workflow. A literal GAC transcription would be known infrastructure. B comes second because copying an already verified gate into Lean adds little unless the new work proves the driver composition identified above.

The table distinguishes mathematical novelty from artifact novelty. References marked as neighbours do not claim exact subsumption. All arXiv identifiers cited below were checked against their landing pages.

| CID / item | Fidelity verdict | Novelty label | References |
|---|---|---|---|
| UMHSF1 | Matches the supplied statement; arbitrary attaining view law remains distinct from constructible honeypots | **classical** | [Issa–Wagner–Kamath, 1807.07878](https://arxiv.org/abs/1807.07878); [Dwork–Roth](https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf) |
| UMSURVF1 | Matches under fresh iid calls; algebraic identities have broader domains than probability interpretations | **classical** | [LASR B.5, 2602.20628](https://arxiv.org/html/2602.20628v1) |
| UMPROTF1 | Absolute joint-event bound matches; baseline-gain and status wording need revision | **modest** | [Greenblatt et al., 2312.06942](https://arxiv.org/abs/2312.06942); [LASR](https://arxiv.org/abs/2602.20628); [Ctrl-Z](https://arxiv.org/abs/2504.10374) |
| UMSTRATF1 | Bound matches; assumption column omits A11 | **modest** | [Roger–Shlegeris toy models](https://www.alignmentforum.org/posts/MDeGts4Aw9DktCkXw/toy-models-of-ai-control-for-concentrated-catastrophe) |
| UMNOGOF1 | Row-only verdict: stated qualifications are appropriate; frozen Claim absent | **modest** | [Roger–Shlegeris toy models](https://www.alignmentforum.org/posts/MDeGts4Aw9DktCkXw/toy-models-of-ai-control-for-concentrated-catastrophe) |
| UMLOWERF1 | Matches nonadaptive joint designs; broader “every design” reading fails | **modest** | [Roger–Shlegeris](https://www.alignmentforum.org/posts/MDeGts4Aw9DktCkXw/toy-models-of-ai-control-for-concentrated-catastrophe); exact quantitative statement not found |
| UMUSEF1 | Core identities match; obstruction conditions omitted; minimax and operational-availability claims exceed statement | **modest** | [GAC](https://arxiv.org/abs/2409.07985); [Ctrl-Z Appendix E](https://arxiv.org/html/2504.10374v1); [LASR B.3](https://arxiv.org/html/2602.20628v1) |
| UMDEFERF1 | Frozen specification is conditional as advertised; service construction and resource extensions absent; proof pending | **modest** | [Shlegeris stopping scenarios](https://blog.redwoodresearch.org/p/wincontinuelose-scenarios-and-executereplaceaudi); [LASR B.6](https://arxiv.org/html/2602.20628v1); [Ctrl-Z](https://arxiv.org/abs/2504.10374) |
| CANONF1 | Full fidelity unassessed: statement absent; toy-language scope is explicit | **classical** | [CompCert](https://compcert.org/index.html), semantic-preservation neighbour |
| SANDBOXF1 | Full fidelity unassessed: parent definitions absent; write-only fix does not establish hiding | **modest** | [Bubblewrap](https://github.com/containers/bubblewrap); [SOUNDGATE](https://arxiv.org/abs/2607.14166), effect-layer neighbour |
| SANDBOX2F1 | Consistent with described model; scratch restriction and arbitrary state-directory scope need emphasis | **modest** | [Bubblewrap](https://github.com/containers/bubblewrap); [SOUNDGATE](https://arxiv.org/abs/2607.14166) |
| VCVio Spike | Row-only verdict; TV/data processing is classical | **classical** | [VCVio](https://eprint.iacr.org/2024/1819); [Dwork–Roth](https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf) |
| VCVio HoneypotBridge | Row-only verdict; bridge establishes an abstract binomial game interpretation | **classical** | [VCVio](https://eprint.iacr.org/2024/1819); [LASR B.5](https://arxiv.org/html/2602.20628v1) |
| VCVio Refinement | Supplied catastrophe claims match the game; completion and implementation correspondence remain unproved | **modest** | [VCVio](https://eprint.iacr.org/2024/1819); [Greenblatt et al.](https://arxiv.org/abs/2312.06942) |
| N1/N1b | Statements absent; individual certificate fidelity unassessed | **known**, at the reported audit-game level | [GAC](https://arxiv.org/abs/2409.07985); [Roger–Shlegeris](https://www.alignmentforum.org/posts/MDeGts4Aw9DktCkXw/toy-models-of-ai-control-for-concentrated-catastrophe) |

**Overall verdict: MAJOR revisions required to STACK.md.** The defensible package is classical and modest formal infrastructure with quantitative negative results. Its practical AI-control significance remains unestablished. None of the reviewed results warrants an “apparently open” novelty label.