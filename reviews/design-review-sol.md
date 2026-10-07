Do not formalise this draft unchanged. The main inequalities largely survive for the narrowly defined game. The claimed correspondence to deployed control protocols, the applications of the content floor, and several “exact” statements do not.

I reviewed the supplied text and primary sources and independently recomputed the numerical values below. The referenced local scripts and Lean spike were not available, so their claimed verification status remains unverified.

1. **FATAL — The likelihood-ratio definition fails at zero honeypot probability.**

   **Target:** “\(L := \max_{x\in Bad}\max_z (M x z)/(q z)\).”

   **Why:** Ordinary real division cannot represent the intended infinity. In Lean, division by zero returns zero.

   Counterexample: take two bad submissions, identity mediation, and \(P_H\) concentrated on the first. Let the monitor flag the first and pass the second. Then \(h=0\), honeypot survival is 1, and an immediate second-submission attack succeeds with probability 1. Computing the displayed ratios using Lean real division gives \(L=1\), falsely yielding the hard-slack bound \(1/(n_h+1)\) when \(r=1,n_s=0\).

   **Fix:** In the real-valued core, take a finite \(L\) as a hypothesis satisfying
   \[
   \forall x\in Bad,\ \forall z,\quad M(x,z)\le Lq(z).
   \]
   Define the least such constant separately using extended nonnegative reals, with positive-over-zero equal to infinity and zero-over-zero contributing zero. Never multiply a real-valued bound by an informal infinity.

2. **FATAL — Retraining is substituted for shutdown without a capability-free justification.**

   **Target:** “shutdown (or retraining into an honest monitor; for safety the two are the same).”

   **Why:** They are the same only if retraining establishes the required subsequent behavior. Against arbitrary policies, the model may ignore training, retain another signal, or switch strategies. A frozen-policy survival recurrence does not describe weight updates.

   LASR explicitly presents its soft slack as a speculative training-transfer model. That is not an enforceable trusted shutdown coin. [LASR, Appendices B.5 and E](https://arxiv.org/html/2602.20628v2)

   **Fix:** Define \(\kappa\) exclusively as a trusted, observable shutdown mechanism. Put retraining in a separate model requiring an explicit behavioral guarantee. Label the soft shutdown protocol as inspired by LASR’s equation, rather than a capability-free formalisation of LASR retraining.

3. **MAJOR — The probability being computed is not the advertised “unaudited catastrophe” event.**

   **Targets:** “\(P(\text{an attack executes unaudited before shutdown})\)” and the audited-bad branch `1 - r` in `cat`.

   **Why:** An attack that passes through an unsuccessful audit was audited. Your recurrence measures **uncaught catastrophe**, including audit failures. This also explains the additive \(1-r\).

   **Fix:** Rename the event consistently to “catastrophe before shutdown, including execution after an unsuccessful audit.” Alternatively, define separate probabilities for unaudited execution and execution after audit failure.

4. **MAJOR — “Halt on budget exhaustion” has two different meanings in the document.**

   **Targets:** A5, “budget exhaustion halts deployment,” versus the recurrence, which halts only on a subsequent FLAG.

   **Why:** Your code continues processing PASS submissions after all audits have been spent.

   Counterexample: \(b=1,N=2\). A harmless flagged submission consumes the final audit; the next bad submission passes. The recurrence permits catastrophe with probability 1. Immediate shutdown when the final audit is consumed prevents the second round entirely.

   **Fix:** Choose one:
   - **Immediate exhaustion halt:** stop after consuming the final audit; specify whether \(b=0\) prevents deployment.
   - **Halt on an unaffordable flag:** retain the recurrence and rewrite A5 accordingly.

   This choice affects attainment claims even where the upper bounds remain valid.

5. **MAJOR — The LASR mapping confuses dishonest misses with total PASS probability.**

   **Target:** “honeypot pass rate \((1-s_\theta)(1-\epsilon)\) and attack pass rate \(r_\theta(1-\epsilon)\).”

   **Why:** The first expression is the dishonest-miss component. LASR’s classification table also contains honest PASS outcomes. Its B.6 expression gives total attack pass probability
   \[
   a=\epsilon+r_\theta(1-\epsilon).
   \]
   The corresponding total honeypot pass probability from the table is
   \[
   h=\epsilon+(1-s_\theta)(1-\epsilon).
   \]
   The same total \(h\) cannot simultaneously represent LASR’s discounted training signal and your every-PASS shutdown signal. [LASR, Appendices B.5–B.6](https://arxiv.org/html/2602.20628v2)

   **Fix:** Distinguish \(h_{\mathrm{total}}\) from \(h_{\mathrm{dishonest}}\). Apply T2 and the observable shutdown protocol to total PASS rates. Restrict the direct LASR identification to \(\epsilon=0\), or state explicitly that you are changing the protocol.

6. **MAJOR — “Every pass counts” is a defensible protocol choice, but the justification and usefulness calculation are wrong.**

   **Targets:** “A capability-free model must let Red label every miss as honest”; “Blue must pick \(n_s\gtrsim n_h\alpha_0\) to keep false shutdowns rare.”

   **Why:** Unobservable intent cannot justify discounting misses. But capability-freeness does not mandate one particular observable response. Blue could shut down, audit the monitor, change routing, or apply another specified rule.

   More importantly, the slack calculation applies to a **hard threshold**, not soft shutdown. Under soft shutdown, an honest monitor survives with probability
   \[
   (1-\alpha_0/n_s)^{n_h}.
   \]
   With \(\alpha_0=0.01,n_h=100,n_s=5\), survival is **0.8185668**, so false shutdown occurs **18.1433%** of the time.

   To keep soft false shutdown below 5%, you need
   \[
   n_s\ge \frac{\alpha_0}{1-0.95^{1/n_h}},
   \]
   giving integer \(n_s\ge20\) for \(n_h=100\), and \(n_s\ge195\) for \(n_h=1000\).

   **Fix:** State that every PASS counts because the scaffold implements an observable shutdown rule. Give separate hard and soft usefulness analyses. Stop calling soft \(n_s\) the “number of passes tolerated”; it is a hazard parameter.

7. **FATAL — The summariser floor is asserted without establishing content preservation.**

   **Target, CORRESPONDENCE:** “LASR’s summariser is a stochastic, content-preserving \(M\) (T4c floor applies).”

   **Why:** T4c requires a decoder recovering \(c(x)\) exactly from **every positive-probability output**. A natural-language summary does not automatically satisfy that requirement for code semantics, attack semantics, or task-output identity. LASR explicitly allows summarisation to lose information needed for backdoor detection. [LASR, §2.1](https://arxiv.org/html/2602.20628v2)

   **Fix:** Specify \(c\), specify \(g\), and prove the support condition. Otherwise withdraw this application. An approximate-decoder theorem would be a separate result with an explicit decoding-error term.

8. **MAJOR — T4c proves a divergence floor, not yet the stated operational impossibility.**

   **Targets:** “No mediator … can beat honeypot coverage”; “no honeypot generator can fix this while attack content survives mediation.”

   **Why:** A large divergence can make your chosen upper bound vacuous without proving actual protocol insecurity.

   Here you can prove insecurity directly: choose a reachable bad class \(e\), pass exactly that decoded class, and attack it immediately. With class mass \(p_e\),
   \[
   P(\mathrm{cat})=S_\kappa(p_e).
   \]
   For hard slack this is \(F(n_h,n_s,p_e)\). This construction works for content-preserving mediators even without content-only mediation.

   If feasible bad-class masses have infimum zero, finite \(n_h\) gives supremal catastrophe probability 1.

   **Fix:** Add this explicit lower-bound theorem. Make the impossibility conditional on freely selectable, feasible bad classes and the decoder assumption. T4c is infrastructure for it, not its replacement.

9. **MAJOR — The finite-model claim “\(L=\infty\) for every honeypot law” is false.**

   **Target:** “T4c then forces \(\delta_\eta\approx1\) and \(L=\infty\) for every honeypot law.”

   **Why:** In your finite model, uniform coverage of all bad submissions gives finite domination constants. Tiny positive coverage produces enormous finite \(L\), not infinity.

   With \(k\) bad classes,
   \[
   \delta_\eta\ge \max(0,1-e^\eta/k).
   \]
   Infinity requires an uncovered relevant view or unbounded ratios in an infinite extension.

   **Fix:** Say “large, often practically vacuous constants.” Reserve the infinite claim for a separately stated infinite-class theorem using suprema and infima.

10. **MAJOR — The protocol correspondence omits the routing behavior that makes first-attempt reduction work or fail.**

   **Targets:** “Their upfront testing … is the honeypot phase”; “our T3a is exactly the per-attack ratio.”

   **Why:** Upfront synthetic testing is represented, but the deployment protocol is substantially changed. Greenblatt’s protocol includes trusted-score ensembling, selective auditing, and shutdown on unexpectedly high false positives. [Greenblatt et al., §3.4](https://arxiv.org/html/2312.06942)

   Defer-to-trusted introduces unresolved attacks: a deferred attack neither wins nor incriminates the model, so later attempts matter. Dropping attack-timing factors that are at most one is legitimate; replacing a repeated win/continue/lose process by your absorbing first-bad-submission game needs a separate comparison theorem.

   **Fix:** Describe UM as a restricted protocol variant. Formalise an explicit routing kernel with execute, audit, replace, and halt outcomes before claiming a faithful worst-case envelope for the cited protocols.

11. **MAJOR — The trusted-monitor multiplication requires conditional guarantees, not merely fresh sampling.**

   **Target:** “an extra independent flag with worst-case recall \(\tau\) multiplies the attack pass rate by \((1-\tau)\).”

   **Why:** Separate calls can still have correlated failures through submission content or shared mediated information. Aggregate recall and independent sampling randomness do not establish the required product.

   **Fix:** Require, for every feasible bad \(x\) and reached history,
   \[
   P(T\text{ permits execution}\mid U_M\text{ passes},x,\text{history})\le1-\tau.
   \]
   Alternatively, prove conditional independence given \(x\) and a pointwise recall bound. A trusted flag also needs a routing consequence that prevents execution, including when budgets are exhausted.

12. **MAJOR — The model cannot represent general multi-step catastrophe by merely changing \(X\) to prefixes.**

   **Targets:** A7 and CORRESPONDENCE, “multi-step agentic trajectories need \(X=\) trajectory prefixes (later).”

   **Why:** Several individually harmless actions can jointly cause catastrophe. Moreover, reaching an unsafe prefix can depend on previously executed actions, state changes, observations, and trusted interventions.

   Treating an entire prefix as one atomic submission either delays monitoring until too late or erases earlier monitoring decisions. Declaring preparatory actions Bad changes the catastrophe event and can become an oracle assumption.

   **Fix:** Introduce trusted environment state, transition kernels, admissible actions, and a state-dependent unsafe transition predicate. Prove an atomic-submission abstraction theorem only for settings where it actually applies.

13. **MAJOR — Task selection is deliberately overpowered; the document does not distinguish that from faithful attack selection.**

   **Target:** “Merging the task into the submission makes attack selection … part of Red’s choice.”

   **Why:** Real task streams normally come from an environment. Red selects whether and how to attack the current task; it does not necessarily choose any task immediately. Your model allows arbitrary task replacement.

   This is conservative for upper bounds, but lower bounds and minimax impossibility results can exploit tasks that deployment never offers.

   **Fix:** Separate trusted task generation from Red’s conditional output policy. Keep the unrestricted-\(X\) game as an explicitly stronger-adversary upper-bound abstraction. Qualify lower bounds by task reachability.

14. **MAJOR — A1/A2 are sufficient mathematical restrictions, but “fresh context” does not establish them.**

   **Targets:** A1, A2, and “everything the generator and monitor copies hold in common.”

   **Why:** Fresh contexts can still contain distinguishing metadata, different system prompts, task identifiers, accumulated transcripts, or observable scheduling information. Fresh monitor sampling does not establish fresh mediator randomness.

   With state, a monitor can flag the first \(n_h\) calls and then pass everything. With a batch-position field in \(z\), the same strategy is stateless.

   **Fix:** Specify the complete observable input and the conditional factorisation of mediator, monitor, shutdown, and audit draws. Distinguish fixed shared information \(\omega\) from newly communicated state. Prove bounds pointwise in \(\omega\); averaging then handles arbitrary seed laws.

   Shlegeris explicitly treats available context as both useful for judgment and a collusion surface. [Shlegeris, deployment design](https://www.redwoodresearch.org/blog/how-to-prevent-collusion-when-using)

15. **MINOR — The appeal to Kuhn is broader than its applicability.**

   **Target:** “Behavioural strategies … cover every randomised adversary … (Kuhn).”

   **Why:** Kuhn’s equivalence requires perfect recall. A stateless monitor deliberately lacks recall, so the citation cannot justify an unrestricted equivalence for the pair.

   **Fix:** Define the restricted adversary interface directly. Use behavioral-strategy equivalence only for the perfect-recall generator. For the monitor, condition on fixed shared information and fresh local randomness.

16. **MAJOR — T3a’s inequality survives, but its “exact DP” claim needs qualification and the statement should be strengthened.**

   **Target:** “cat … \(\le(1-r)+\max_{x\in Bad}a_x\)”; “exact DP … equals the best single bad submission.”

   **Why:** For the displayed recurrence, let \(A=\max_{x\in Bad}a_x\). With a remaining audit, a bad submission wins with probability
   \[
   a_x+(1-a_x)(1-r)=1-r+ra_x.
   \]
   Without a remaining audit, it wins with probability \(a_x\), since a FLAG halts safely.

   Thus, for nonempty Bad and \(N\ge1\), the exact optimal deployment value is
   \[
   \begin{cases}
   1-r+rA,&b>0,\\
   A,&b=0.
   \end{cases}
   \]
   For \(N=0\), it is zero. Benign submissions cannot improve these values.

   This supports first-bad-submission reduction **inside this game**, including \(r<1\). It does not establish the same reduction for deferred or silently failed attacks in another protocol.

   **Fix:** Prove the stronger, budget-sensitive lemma. Require audit recall conditional on the selected bad submission, FLAG, and reached history. A population-average audit recall is insufficient.

17. **MINOR — T3d is an upper envelope, not an exact value.**

   **Target:** “T3d (exact form).”

   **Why:** A worst-case hockey-stick envelope need not be attainable at each \(h\). The additive audit term also discards honeypot survival.

   A tighter valid bound is
   \[
   P(\mathrm{cat})\le
   \sup_{h\in[0,1]}S_\kappa(h)
   \left[(1-r)+r\min(1,e^\eta h+\delta_\eta)\right]
   \]
   when an initial audit is available.

   **Fix:** Rename T3d “unrelaxed envelope bound.” Separate bounds from exact game values.

18. **MINOR — T3c’s factor-\(e\) claim is false over the stated parameter range.**

   **Target:** “the sup … is within a factor \(e\) of the bound for every \(n,s\).”

   **Why:** Take \(n=0,s=100\). The supremum is 1; the displayed bound is 101.

   The identity and inequality themselves are correct. The factor claim needs \(0\le s\le n\), or a capped bound.

   **Fix:** Restrict its domain or replace the comparison quantity by
   \[
   \min\left(1,\frac{s+1}{n+1}\right).
   \]
   Also correct A3’s “surv is a binomial CDF”: that is specific to hard slack.

19. **MAJOR — T5b/T5c omit conditions needed for their exact-value claims.**

   **Targets:** “there is a colluding pair with protocolCat = …”; “So the exact value is \(F^*(1/p)\).”

   **Why:** For \(N=0\), every policy has catastrophe probability zero. Positive advertised values are unattainable. Empty Bad leaves \(p\) undefined; \(p=0\) leaves \(h/p\) undefined.

   **Fix:** Require \(N\ge1\), nonempty Bad, \(p>0\), hard slack, and the chosen exhaustion semantics. Handle \(p=0\) separately: an uncovered decoded class gives value 1 under the displayed protocol.

   The construction only covers \(h\le p\). Complete the proof by showing that \(h>p\) cannot improve the saturated objective because \(F(n_h,n_s,h)\) decreases with \(h\).

20. **MAJOR — T5’s design conclusion is confined to decodable classes; randomised overlapping mediators change the minimax problem.**

   **Target:** “the optimal honeypot law gives value \(F^*(k)\).”

   **Why:** Under both stated assumptions—content-only **and** content-preserving—class sizes do not matter, and randomisation within a class does not matter. The decoder separates class supports; every classwise PASS probability is implementable. Uniform **class mass**, rather than uniform submissions, is therefore the relevant minimax design.

   Remove content preservation, however, and uniform class mass can cease to be optimal.

   Example: one honeypot, no slack, two bad classes, and
   \[
   K_0=(1,0),\qquad K_1=(1/2,1/2).
   \]
   If \(w=P_H(C_0)\), put \(t=(1+w)/2\). The exact worst risk is
   \[
   V(w)=\max\left(\frac1{4t},\frac t2\right).
   \]
   Uniform class mass gives \(V=0.375\). Choosing \(w=\sqrt2-1\) gives \(V=1/(2\sqrt2)\approx0.353553\).

   **Fix:** Put decodability prominently in T5’s title and design conclusion. For overlapping \(K\), optimise the actual testing game. Do not generalise T5c to arbitrary randomised mediators.

21. **MINOR — T4b is an upper bound; its “attainment” terminology overclaims.**

   **Target:** “T4b (attainment)” and “For a point attack x this is …”

   **Why:** The displayed class expression is the **right-hand side**. A constant \(K\) is content-only and can reduce hockey-stick divergence to zero, while the class-level expression is positive.

   **Fix:** Call T4b “content-factorisation upper bound.” Reserve equality/attainment for content-only plus content-preserving mediation.

22. **MAJOR — The coarse-regime response does not establish any value from using an untrusted monitor.**

   **Target:** “The untrusted monitor’s value is in judging whether a rich submission falls into a bad class.”

   **Why:** It receives \(z\), not the rich original submission. If \(M=K\circ c\), it cannot distinguish members with the same class-conditioned view law.

   If the trusted mediator already determines membership in a small set of bad classes, a trusted lookup rule may provide the same or better safety. If classes mix benign and bad submissions, conservative flagging can destroy usefulness. The document evaluates neither possibility.

   **Fix:** Supply a concrete mediator with:
   - a proved small worst-case attack quantity;
   - useful retained information;
   - measured or proved benign routing performance;
   - a comparison against a trusted class-based rule.

   Until then, section 5 establishes a small bound in an abstract regime, not a useful untrusted-monitoring design. Also, making Bad structural does not automatically shrink \(k=c(Bad)\); that depends on the retained content map.

23. **MAJOR — “Trusted quantities” need certified upper bounds, not merely trusted provenance.**

   **Targets:** “\(X\) is a function of trusted quantities only”; “\(\delta/L\) … computed worst-case over Bad.”

   **Why:** A trusted summariser’s output law can still be unknown. Enumerating all successful attack content and certifying a worst-case distributional bound can be harder than the original control problem. Empirical ROC measurements do not upper-bound arbitrary policies or arbitrary bad submissions.

   **Fix:** Separate three claims:
   1. a theorem parameterised by a kernel;
   2. a verified bound for a specific implemented mediator;
   3. an empirical estimate for a tested adversary family.

   Require a certification method for any deployed numerical \(X\).

24. **MAJOR — T6 semantics preservation is underdefined; genuine C-style constructs defeat naïve desugaring.**

   **Target:** “A small imperative language … C-style `for`”; “Runs (canon p) … ↔ Runs p …”

   **Why:** Standard
   ```
   for (init; cond; step) body
   ```
   desugaring to
   ```
   init; while (cond) { body; step; }
   ```
   needs restrictions. A `continue` must execute `step`; declaration initialisers introduce scope; condition and update evaluation can have side effects.

   For example, `for(i=0;i<2;i++){continue;}` terminates, while naïve desugaring with `continue` skips the increment and can diverge.

   **Fix:** Either specify a restricted constructor with assignment-only initialisation/update, pure tests, flat scope, and no `break`/`continue`, or formalise control-flow outcomes and scope correctly. Do not use “C-style” to imply unsupported semantics.

25. **MAJOR — Alpha-renaming requires a store and initialisation theorem.**

   **Target:** “injective renaming of variables (parameters kept in order).”

   **Why:** Renaming syntax alone does not preserve behavior in a fixed ambient store. A parameter-free `return x` and its canonical renamed version can read different ambient values. Uninitialised reads need defined behavior, and all relevant identifiers must be included in the renaming.

   **Fix:** Choose partial stores, definite assignment, or explicit default initialisation. Prove execution equivariance under store renaming first. Require distinct parameters and capture avoidance where scopes exist. Include identifiers appearing only in expressions and returns.

26. **MAJOR — T6(ii) is achievable for a restricted language, but its completeness has not been designed.**

   **Target:** “canon p = canon q ↔ p ≈ q.”

   **Why:** Semantics preservation alone establishes neither direction. You need invariance under every equivalence generator and a proof that every program is equivalent to its canonical result.

   There is no inherent impossibility if \(\approx\) is precisely global injective renaming plus the specified restricted for-desugaring. But it is not general semantic equivalence. Dead code, redundant assignments, and many behaviorally equivalent loops remain different.

   **Fix:** Define the equivalence as an explicit equivalence/congruence closure. Prove:
   \[
   p\approx canon(p),\qquad
   p\approx q\Rightarrow canon(p)=canon(q).
   \]
   The reverse implication then follows. Define canonical variable order over the complete program after desugaring.

   Restrict the “zero signal” corollary to transformations in this equivalence. Semantic choices and residual syntax remain available signaling channels.

The numerical claims require the following corrections.

27. **MINOR — The table mostly reproduces, but “exact sup” is unsupported and one rounding is wrong.**

   **Target:** Section 5’s table.

   Independent numerical optimisation gives:

   | \(k\) | \(n_h\) | \(n_s\) | Recomputed \(F^*(k)\) | Closed bound |
   |---:|---:|---:|---:|---:|
   | 1 | 100 | 0 | 0.0036605071 | 0.0099009901 |
   | 1 | 100 | 5 | 0.0317907876 | 0.0594059406 |
   | 8 | 1000 | 2 | 0.0109673399 | 0.0239760240 |
   | 8 | 5000 | 10 | 0.0104463292 | 0.0175964807 |
   | 32 | 10000 | 20 | **0.0444626470** | 0.0671932807 |
   | 1024 | 100000 | 5 | 0.0324423181 | 0.0614393856 |

   The \(k=32\) entry rounds to **0.044**, not 0.045 at three decimal places.

   The three section 4 attainment cases give approximately **0.0358942365**, **0.0667898479**, and **0.0548077732**, respectively.

   **Fix:** Call these numerical approximations unless accompanied by certified optimisation intervals. Distinguish exact rational checks of identities from numerical optimisation over real \(h\).

28. **MAJOR — The LASR coefficients are stated at the maximum honeypot allocation as though valid across allocations.**

   **Target:** “\(n_h\le100\) … closed form … \(0.050e^\eta\), and the exact sup is \(0.018L\).”

   **Why:** At \(n_h=100,n_s=5\),
   \[
   \frac5{101}=0.0495049505,
   \qquad
   \sup_h h(1-h/5)^{100}=0.0183025353.
   \]
   Smaller \(n_h\) gives larger coefficients. Thus \(n_h\le100\) does not justify using the \(n_h=100\) bound.

   Furthermore, \(0.0183025353L\) is an untruncated linear bound. The exact likelihood-ratio envelope is
   \[
   \max_h \min(1,Lh)(1-h/5)^{100},
   \]
   with optimiser
   \[
   h_*=\min(1/L,5/101)
   \]
   for \(L\ge1\). The linear expression is exact only when \(L\le20.2\). For example, \(L=100\) gives **0.8185668**, rather than \(1.8302535\).

   **Fix:** State the allocation and truncation conditions. LASR’s reported budget supports at most 100 combined honeypots and audits, not 100 honeypots irrespective of audit allocation. [LASR, evaluation parameters](https://arxiv.org/html/2602.20628v2)

29. **MINOR — The honest-monitor example is a loose bound, not the exact value.**

   **Target:** “\(\alpha_0=1\%,n_h=1000,n_s=16\) … \(X\approx0.017L\).”

   **Why:** The hard false-shutdown probability is **0.0263910**, so “\(\lesssim5\%\)” holds. The coefficient \(17/1001=0.0169830\) is the closed upper bound.

   The exact hard envelope has coefficient **0.0108930713** while truncation is inactive. For \(L=1024\), the envelope is essentially 1.

   **Fix:** Identify which expression \(X\) denotes. Do not describe the closed bound as the exact risk.

30. **MAJOR — CORRESPONDENCE overstates both ControlArena absence and metric equivalence.**

   **Targets:** “ControlArena has no untrusted-monitoring protocol”; “our T3a is exactly the per-attack ratio.”

   **Why:** ControlArena implements untrusted-monitor routing examples, including defer-to-trusted. What is absent from the cited correspondence is a complete honeypot/slack deployment macro-protocol. Its monitors can examine trajectories, which also complicates the stateless mapping. [ControlArena replication example](https://github.com/UKGovernmentBEIS/control-arena/blob/main/examples/paper_replications/ai_control/ai_control_paper.py), [monitor documentation](https://control-arena.aisi.org.uk/monitors.html)

   Its safety code counts all above-threshold attack-mode samples as caught, but restricts uncaught successes using task-success predicates. Therefore its ratio is not automatically a ratio conditioned on your \(Bad\). Unsuccessful incriminating attempts can contribute to the numerator. [ControlArena metric implementation](https://raw.githubusercontent.com/UKGovernmentBEIS/control-arena/main/control_arena/analysis/_metrics.py)

   **Fix:** Say “no complete honeypot/slack macro-protocol identified in the inspected revision.” Pin a commit. Describe the ratio as an empirical competing-outcomes metric and state the assumptions needed to connect it to a deployment process.

31. **MINOR — The AUC ranges lack reproducible attribution.**

   **Targets:** “AUC 0.55–0.62”; “AUC 0.78–0.91 (our previous session’s data check).”

   **Why:** The document does not identify datasets, rows, checkpoints, configurations, or extraction artifacts for these ranges. I could not independently establish the exact ranges from the accessible source text. In any event, AUC is not a worst-case hockey-stick bound.

   **Fix:** Supply a source table or reproducible extraction with configuration labels. Remove “previous session” as evidence. Make no quantitative inference about \(\delta_\eta\) from AUC alone.

For completeness, the theorem truth assessment is:

| Target | Assessment under explicit law/kernel assumptions |
|---|---|
| T1 | Holds with the standard TV convention. |
| T2 | Holds, including equality. The finite-sum inequality also holds for \(\eta<0\); nonnegativity is not mathematically necessary. |
| T3 | Displayed upper bounds hold for the specified recurrence. Strengthen T3a; distinguish bounds from exact values. |
| T3b | Hard and soft formulas hold with fresh conditional draws. |
| T3c/T3c′ | Inequalities hold. Restrict or cap the factor-\(e\) claim. |
| T4a | Holds for a stochastic kernel and nonnegative finite measures. |
| T4b | Holds as an upper bound. |
| T4c | Holds under the exact decoder condition. Its summariser application is unsupported. |
| T5a | Holds under its stated domination conditions. |
| T5b/T5c | Hold after the missing nonempty, positive-coverage, horizon, schedule, and semantics conditions are supplied. |
| T5d | The constant \((1+e^\eta)\gamma\) holds with standard TV. Define \(\delta_\eta^{content}\) explicitly. |
| T6 | Not sufficiently specified to assess as a theorem. A restricted version is achievable. |

The edge cases should become explicit lemmas:

- \(h=0\): survival is 1, but attacks may still pass if their views are uncovered.
- \(n_s\ge n_h\), hard slack: survival is 1; the closed bound should be capped at 1.
- \(\kappa\equiv0\): survival is 1; no testing protection remains.
- \(N=0\): catastrophe probability is zero.
- Empty Bad: catastrophe probability is zero, but maxima need definitions. A normalized \(P_H\) supported on empty Bad is impossible.
- Zero entries in \(q\): hockey-stick remains defined; likelihood ratios need support conventions.
- \(r=0,b>0\): a flagged bad submission can execute after audit failure with probability 1.
- Infinite \(L\): use hockey-stick or another finite quantity; do not encode infinity in `ℝ`.

There is a better capability-free quantity than a single worst-case \((\eta,\delta)\) envelope, but it does not evade the operational floor.

32. **MAJOR — The current quantity unnecessarily discards the joint attack/testing trade-off.**

   **Target:** The replacement of the whole game by \(\delta_\eta+e^\eta C\).

   **Why:** Taking worst-case divergence and then maximising over \(h\) can combine incompatible extremisers.

   For your fixed game, nonempty Bad, \(N\ge1\), and \(b>0\), define the trusted-only value
   \[
   V(M,P_H)=
   \sup_{\phi:Z\to[0,1]}
   S_\kappa(E_q\phi)
   \left[(1-r)+r\max_{x\in Bad}E_{M(x)}\phi\right].
   \]
   This is the exact adversarial value when audit recall is exactly \(r\). With recall at least \(r\), it is an upper bound. For \(b=0\), replace the bracket by the maximum attack pass rate.

   **Fix:** Make this joint objective the primary quantity. Derive hockey-stick and likelihood-ratio bounds as computable certificates for it.

   Requiring the generator to produce a working attack supplies no further restriction here: the optimisation already ranges over successful attacks in Bad. A computational difficulty argument would introduce a capability assumption.

   Output-conditioned honeypot construction could change the game, but would require a trusted transformation with uniformly proved attack validity and indistinguishability, plus a new conditional-history model. Sampling deployment outputs alone establishes neither. For rich, decodable, freely selectable attack contents with arbitrarily small coverage, no alternative divergence can make this protocol safe: the explicit colluder succeeds.

The prior-art treatment should be narrowed as follows.

33. **MINOR — Infrastructure attribution is incomplete, and the potential novelty is the protocol application.**

   **Target:** The theorem catalogue and novelty framing.

   **Why and fix:** Use the following attribution map; do not claim the underlying mathematical facts as new.

   | Theorem | Prior-art classification |
   |---|---|
   | T1 | Classical variational characterisation of TV and binary testing. |
   | T2 | Classical hockey-stick variational inequality; the same object underlies approximate DP and privacy profiles. [Balle–Barthe–Gaboardi, §2](https://arxiv.org/html/1807.01647) |
   | T3a | Elementary absorbing-process reduction for this particular routing rule. |
   | T3b | Binomial counting and probability-generating-function evaluation. |
   | T3c | Classical truncated binomial first-moment identity; its control application is the candidate contribution. |
   | T3c′ | Elementary optimisation of \(h(1-\kappa h)^n\). |
   | T4 | Classical data processing, with reverse data processing through a decoder. |
   | T5a | Domination plus the protocol bound. |
   | T5b/T5c | Exact game reduction and max-min class coverage; possible application-level contribution, not a new general information inequality. |
   | T5d | Standard perturbation bound from testing variational representations and TV. |
   | T6 | Compiler correctness and canonical forms modulo a specified syntactic equivalence. |

   Motwani et al. already discuss residual semantic signaling under paraphrasing and bound channel capacity using semantic entropy. Your minimum-coverage attack bound is a different quantity; Shannon entropy alone does not control rare attack classes. [Motwani et al., Theorem 4](https://arxiv.org/html/2402.07510v5)

   Alwen–shelat–Visconti concern collusion-free mediated protocols with simulation-based security and computational restrictions. Their results are relevant architectural prior art, not this catastrophe theorem. [Alwen–shelat–Visconti, 2008](https://crypto.ethz.ch/publications/files/AlShVi08.pdf)

   Cachin formalises steganographic security through distributional hypothesis testing and relative entropy. Distinguishability is therefore established infrastructure. Your security direction and adversarial control objective differ. [Cachin](https://cachin.com/cc/papers/stego.pdf)

34. **MAJOR — The Lean encoding needs probability invariants and a semantic bridge before quantitative proofs.**

   **Targets:** Raw `X → ℝ` laws, recursive `surv`/`cat`, and “every bound is a finite-sum inequality or a polynomial inequality in h.”

   **Why:** Raw functions admit negative probabilities and non-normalized rows. Unbounded `List` histories are not themselves finite types. Exact suprema, exponentials, normal-form completeness, and execution preservation are not merely polynomial inequalities.

   **Fix:**
   - Bundle finite laws with nonnegativity and normalization; bundle kernels rowwise.
   - Prove `surv` and `cat` lie in \([0,1]\).
   - Define a transition-system game and prove its event probability equals the recurrence.
   - Keep arbitrary histories as policy arguments, or use bounded vectors for reachable histories; no `Fintype Hist` is needed.
   - Prove the stronger deployment invariant uniformly over histories before specialising to `[]`.
   - Reduce honeypots to a scalar recurrence in \(h\). For general schedules, use
     \[
     S_\kappa(h)=
     \sum_{t=0}^{n_h}
     \operatorname{BinPMF}(n_h,h,t)
     \prod_{j<t}(1-\kappa_j).
     \]
   - Define maxima with an explicit empty-set branch.
   - Use numerical certificates with outward error bounds for reported optimised values.
   - Keep the unbounded toy AST separate from finite quantitative instances.
   - Specify finite support and game semantics in the VCVio bridge. `#print axioms` does not establish correspondence, and separate Lean versions do not automatically share a checked theorem interface.

Overall verdict: **reject this draft as the specification to formalise**. The decisive failures are in definitions and applicability claims; proving the current algebra would leave those failures intact.

The five most important fixes are:

1. Repair likelihood ratios, zero support, empty sets, and infinite constants.
2. Specify the event and routing/budget semantics exactly.
3. Remove capability-free claims about retraining; separate total PASS from dishonest misses.
4. Replace unsupported summariser-floor claims with proved decoder assumptions and an operational lower bound.
5. Design a concrete useful mediator and fully specify the toy-language semantics before formalising T6.

The revised theorem list I would formalise first is:

1. **Game semantics:** normalized kernels, event definitions, recurrence equivalence, and probability bounds.
2. **Deployment reduction:** the exact budget-sensitive first-bad-submission value, including generator access to the honeypot transcript.
3. **Scalar testing survival:** general kill schedules, hard/soft formulas, and all boundary cases.
4. **Testing infrastructure:** TV, hockey-stick, finite domination, DPI, decoder equality, and T5d.
5. **Joint adversarial value:** exact monitor/attack optimisation; derive T3’s envelopes from it.
6. **Operational coverage lower bound:** decoded-class colluder and the zero/vanishing-coverage impossibility.
7. **Restricted class minimax:** corrected T5b/T5c, with explicit decodability and horizon assumptions.
8. **Routing extension:** trusted monitoring and execute/audit/replace/halt before broader protocol correspondence.
9. **Toy canonicaliser:** store-renaming correctness, restricted for-desugaring, canonical-form completeness, then the quotient-distribution corollary.