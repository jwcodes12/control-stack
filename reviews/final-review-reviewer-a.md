**I would reject STACK as an end-to-end control guarantee.** The frozen statements support conditional results about idealised models. Several prose claims exceed those statements, and SANDBOXF1’s encoding cannot establish the claimed protection of host files.

I accept the stipulated kernel gate. “FATAL” below means fatal to the claimed operational guarantee, not a contradiction in the Lean theorem. This audit covers the seven supplied frozen CIDs; the earlier N1/N1b, K5, CLK and LURE statements were not supplied.

1. **FATAL — SANDBOXF1: pathname confinement does not establish file confinement.**

   **Exact claim:** “A read-only-root fixed policy confines host writes to scratch and the declared state directories”; conjunct (b) concludes `W <+: hp ∨ ∃ d ∈ stateDirs, d <+: hp`.

   **Why:** `WritesHost` identifies the modified object with a lexically constructed pathname. Linux files can have multiple names. Suppose scratch contains a pre-existing hard link to a file also named outside scratch. Writing through the writable scratch mount changes that file’s contents, including contents visible through the outside name. The theorem reports only the scratch pathname.

   The same trap affects (c): a readable alias outside a hidden directory can reveal a file also named inside it, while `ReadsHost` supplies only the outside name. Its antecedent therefore never recognises the disclosure.

   This counterexample respects access through the mount table and requires no `/proc/<pid>/root` escape. Linux explicitly treats hard links as names for the same file; read-only bind mounts constrain access through a mount rather than making the underlying object globally immutable. [Linux `link(2)`](https://man7.org/linux/man-pages/man2/link.2.html), [Linux `mount(8)`](https://www.man7.org/linux/man-pages/man8/mount.8.html).

   **Fix:** Describe the result as confinement of *modelled pathname resolutions*. For host integrity/confidentiality, model file identities and aliasing, state an initial filesystem separation invariant, and preserve it under allowed operations. A verified resolution model must also address symbolic links and actual mount topology. `--unshare-pid` alone does not discharge these obligations. Conjunct (a) remains a counterexample inside the stated model; no supplied statement connects `currentPolicy` to the actual dispatcher or gate execution.

2. **MAJOR — STACK’s assertion that domination is false for every honeypot law is false in its finite model.**

   **Exact claim:** Under “Assumptions still unproved,” item 1: for rich content-preserving mediators, the trusted-component hypothesis “is false for every honeypot law: UMHSF1’s maximal-leakage floor and UMNOGOF1.”

   **Why:** For any finite kernel and a honeypot law with positive mass on every bad submission,
   \[
   q(z)=\sum_y P_H(y)M(y,z)\ge P_H(x)M(x,z).
   \]
   Consequently \(M(x,z)\le Lq(z)\) with
   \[
   L=\max_{x\in Bad}1/P_H(x).
   \]
   Uniform honeypots over a nonempty finite bad set give \(L=|Bad|\).

   Content preservation can force a large minimum \(L\). UMNOGOF1 gives a finite-sample lower bound. Neither establishes nonexistence of a finite domination constant. Its lower bound also tends to zero as \(n_h\to\infty\) for fixed \(k>1\).

   **Fix:** Replace the sentence with: “Content preservation can prevent sufficiently small domination constants and impose large honeypot requirements.” Specify the target constant or risk threshold being ruled out.

3. **MAJOR — UMSTRATF1’s counting bound is overclaimed as attained.**

   **Exact row:** “risk ≤ \((1-r)+r(s_c+1)/(m+1)\) … Attained by an explicit colluder.”

   **Exact statement:** The second conjunct establishes
   \[
   \operatorname{risk}=\operatorname{binCDF}(m,s_c,t)(1-r+rt),
   \]
   and the accompanying comment explicitly says it “does not assert tightness of the first conjunct.”

   **Why:** The attainable curve differs from the counting bound. With one class, \(r=1\), \(m=1\), \(s_c=0\), and one deployment round with an audit available, risk is \(t(1-t)\), whose maximum is \(1/4\). The advertised counting bound is \(1/2\).

   Moreover, the attainment conjunct assumes an exact decoder for \(K\); the upper-bound conjunct does not.

   **Fix:** Write: “An explicit colluder attains the displayed curve under exact class decoding; the counting upper bound is not claimed tight.”

4. **MAJOR — UMHSF1’s approximate-decoder floor loses an essential error term in English.**

   **Exact row:** “A content-preserving mediator cannot reduce it below the content-level value (exact or approximate decoder).”

   **Exact statement:** The approximate case concludes
   \[
   hs_\eta(c_\#P_A,c_\#P_H)
   \le hs_\eta(M_\#P_A,M_\#P_H)+(1+e^\eta)\gamma.
   \]

   **Why:** Approximate decoding permits distinguishability to fall below the content-level value. For two content classes transmitted through a binary symmetric channel with error \(\gamma<1/2\), opposite point masses have content TV \(1\), while mediated TV is \(1-2\gamma\).

   **Fix:** State the penalised floor explicitly. Also retain the hypothesis’s strength: decoder error is bounded **on every submission**, rather than merely on average under the honeypot law.

5. **MAJOR — UMPROTF1 formalises exact constant audit recall, whereas A6 assumes a conditional lower bound.**

   **Exact statements:** A6 requires recall “≥ \(r\) … conditional on the flag and the reached history.” In `cat`, every flagged bad submission with an available audit contributes exactly `1 - r`.

   **Why:** The frozen theorem quantifies one scalar audit coin. It does not quantify an operational auditor whose recall varies with submission, view and history.

   Using the lower bound \(r\) should give a conservative comparison for this absorbing protocol. But that comparison is an additional theorem. The documented simulation does not make it a Lean consequence.

   **Fix:** Introduce an audit kernel and prove that the operational event probability is bounded by `cat ... r ...` under the stated conditional recall hypothesis. The hypothesis must remain valid after honeypot survival and every other relevant selection event.

6. **MAJOR — “The first bad submission decides” depends on an incompletely stated shutdown assumption.**

   **Exact statement:** In `cat`, an audited bad submission contributes `1-r`; the caught branch has zero future catastrophe probability.

   **Why:** Catching a bad submission therefore ends the adversary’s opportunity permanently. A1–A10 explicitly specify halting on audit exhaustion, but do not explicitly require absorbing shutdown after catching an attack.

   Blocking the caught submission and continuing changes the result. With an always-FLAG monitor, recall \(r=1/2\), two attacks and two available audits, continuing after a successful catch gives catastrophe probability \(3/4\). The advertised bound with \(h=0\) is \(1/2\).

   **Fix:** Add an explicit assumption that catching a bad submission causes absorbing shutdown. Define separately the protocol that merely rejects the submission and continues.

7. **MAJOR — UMPROTF1 does not formalise LASR Eq. (1) with only the advertised substitutions.**

   **Exact protocol column:** “LASR Eq. (1) with ε = 0 and shutdown in place of retraining.”

   **Why:** LASR’s equation contains upfront audits, an attack-attempt rate, finite-horizon attempt probability, and execute/audit/defer dynamics. Its honeypot term uses a Poisson approximation to a speculative retraining model. These are material differences from `protocolCat`.

   Greenblatt §3.4 also uses combined suspicion scores and additional shutdown checks. The supplied statements neither instantiate that protocol nor establish a conservative refinement from it. [LASR, Eq. (1) and Appendix B](https://arxiv.org/html/2602.20628v1), [Greenblatt et al., §3.4](https://arxiv.org/html/2312.06942v2).

   **Fix:** Change the column to “motivated by the upfront-honeypot mechanism in these protocols.” List the additional conditions required for applicability. Reserve a claim about Eq. (1) for an explicit reduction or comparison theorem.

8. **MAJOR — CANONF1 does not establish removal of the marker in LASR’s actual language and pipeline.**

   **Exact protocol column:** “LASR’s For/While marker survived their minifier; this class is provably erased.”

   **Why:** The proved equivalence concerns a toy language with global numeric variable identities, zero-initialised locals, mathematical integers, pure conditions, and a stipulated `for` expansion. Its observable semantics is terminating input/output behaviour.

   LASR’s evaluated programs are Python. There is no verified parser, Python semantics, translation, serializer, or connection to the complete monitor input. Thus the theorem establishes erasure of the analogous toy-language syntactic freedom. [LASR, §4.2 and §5.4](https://arxiv.org/html/2602.20628v1).

   **Fix:** Say “erases an analogous For/While channel in the specified toy language.” A deployed claim requires a verified language frontend and an observation-level preservation theorem.

9. **MINOR — UMSURVF1’s English bound needs a schedule qualifier.**

   **Exact row:** Survival “is a binomial CDF (hard slack) or \((1-\kappa h)^n\) (constant schedule), and \(h\cdot survival\le(n_s+1)/(n_h+1)\).”

   **Why:** The displayed bound is proved for hard slack. For a constant schedule, the statement proves
   \[
   h(1-\kappa h)^{n_h}\le\frac1{\kappa(n_h+1)}
   \]
   under \(0<\kappa\le1\). An arbitrary constant schedule does not satisfy the hard-slack bound: \(\kappa=0,h=1\) gives survival \(1\).

   **Fix:** Attach each bound to its schedule and parameter restrictions. For `softKill ns`, state the \(n_s/(n_h+1)\) bound and \(n_s\ge1\).

10. **MINOR — the deployment bounds are unconditional from before testing.**

    **Exact definitions:** `protocolCat` and `stratProtocolCat` multiply test survival by deployment catastrophe probability.

    **Why:** These bound the joint event “survives testing and subsequently causes catastrophe.” They do not bound deployment risk conditional on observed test success.

    For example, take \(L=r=1\), a fixed monitor with pass probability \(1/2\), no slack, twenty honeypots, and one immediately bad deployment submission. Joint catastrophe probability is \(2^{-21}\); catastrophe probability conditional on surviving testing is \(1/2\).

    **Fix:** State the event and starting point in the rows. A conditional guarantee needs a separate argument; dividing by survival probability requires a certified positive lower bound.

11. **MINOR — UMSTRATF1 removes the class count from a bound parameterised by per-class expenditure.**

    **Exact row:** “m honeypots per bad class … with no class-count factor.”

    **Why:** With \(k\) tested classes, total testing expenditure is \(n_h=km\). Substitution gives
    \[
    (1-r)+r\,\frac{k(s_c+1)}{n_h+k}.
    \]
    The dependence on class count reappears under a fixed total budget. This is compatible with the Lean statement, but limits the recommendation’s significance.

    **Fix:** Say “no additional class-count factor at fixed per-class testing budget.” Include class coverage, total construction cost, and per-class shutdown counters in comparisons.

12. **MINOR — “capability-free” needs a qualified label, and the trusted quantities need sharper separation.**

    **Exact wording:** STACK’s title and DESIGN’s “no assumption on what U can do.”

    **Why:** The universal quantification covers arbitrary policies within a finite model with a stateless, frozen monitor and enforced sampling interfaces. It does not cover arbitrary stateful deployed systems.

    The guarantee additionally depends on the implemented mediator and complete observation boundary, honeypot construction and coverage, shutdown enforcement, and worst-case audit recall. \(L,\delta,\gamma\) are properties requiring certification. \(h\) and \(a\) are adversary-induced rates. CANONF1 supplies a toy transformation theorem; it supplies no numerical domination certificate over a deployed catastrophe set.

    **Fix:** Use “capability-independent adversary bounds under explicit scaffold, audit and construction assumptions.” Keep mathematical parameters, implemented trusted components, and certified numerical bounds distinct.

Two further fidelity qualifications matter.

UMHSF1’s likelihood-ratio floor is over the chosen nonempty set \(B\). The sum \(\sum_z\max_{x\in B}M(x,z)\) is **exponentiated** maximal leakage; the conventional leakage is its logarithm. Its attainment theorem ranges over arbitrary output laws \(Q\), without requiring \(Q=M_\#P_H\) for a constructible honeypot law. That does not invalidate the floor, but it prevents reading the optimum as a honeypot construction. [Issa–Wagner–Kamath, Theorem 1, arXiv:1807.07878](https://arxiv.org/html/1807.07878).

UMNOGOF1 has the intended quantifier order: for each \(P_H\), one deterministic pair exists and works uniformly across the listed valid settings. It is an existential attack in the free-submission model. It does not guarantee the attack’s availability on an exogenous task stream. For \(k=1,n_h>0\), its stated lower bound is zero.

The novelty assessment is mostly infrastructure and modest protocol composition. UMHSF1’s testing inequality and data processing belong to established hypothesis-testing/divergence theory; the maximal-leakage expression is published prior art. [Balle–Barthe–Gaboardi, arXiv:1807.01647](https://arxiv.org/html/1807.01647), [Issa–Wagner–Kamath](https://arxiv.org/abs/1807.07878).

UMSURVF1 is classical binomial algebra. Its counting inequality follows from
\[
h\,\Pr[\operatorname{Bin}(n,h)\le s]
=\frac{\mathbb E[Y\,1_{\{Y\le s+1\}}]}{n+1},
\qquad Y\sim\operatorname{Bin}(n+1,h).
\]
This is a novelty diagnosis, rather than a claim that a particular paper previously printed the exact inequality. The distributional ingredients are standard. [NIST binomial distribution](https://www.itl.nist.gov/div898/handbook/eda/section3/eda366i.htm).

UMNOGOF1 combines a least-mass class argument with the probability of missing that class in iid samples. The underlying collusion strategy and importance of catching the first attack already appear in the untrusted-monitoring literature. Its universal finite formulation should not be marketed as a deep impossibility discovery. [Shlegeris, “How to prevent collusion…”](https://www.alignmentforum.org/posts/GCqoks9eZDfpL8L3Q/how-to-prevent-collusion-when-using-untrusted-models-to).

**Significance:** the package supplies conditional algebraic bounds whose assumptions can be inspected. Its contribution to AI control remains limited by the lack of an operational probability bridge, a deployed mediator certificate, and a theorem connecting action-layer enforcement to the catastrophe set. No result establishes useful work alongside safety. Early shutdown can make safety easy, and several parameter settings produce bounds of at least one. Formal control games and explicit safety/usefulness objectives also predate this package. [Griffin et al., arXiv:2409.07985](https://arxiv.org/abs/2409.07985).

**The single most valuable next formalisation step is an operational refinement theorem for UMPROTF1.**

Define a finite probabilistic protocol with explicit test/deployment phases, traces, audit budget, absorbing shutdown and an audit kernel. Define catastrophe as a trace event: execution of a bad submission before shutdown. Prove, under the actual conditional recall hypothesis and sampling/interface assumptions,
\[
\Pr[\text{operational catastrophe}]
\le
\operatorname{protocolCat}_{r}
\le
(1-r)+rL\frac{n_s+1}{n_h+1}.
\]

The first inequality should be derived from the transition semantics, rather than assumed as correspondence with `cat`. This closes the exact-recall/lower-recall gap and forces the shutdown and observation assumptions into a reviewable statement. VCVio provides relevant machinery for probabilistic computations and event semantics. [VCVio framework](https://github.com/Verified-zkEVM/VCVio), [Tuma–Hopper, ePrint 2024/1819](https://eprint.iacr.org/2024/1819).

The table labels mathematical novelty separately from the existence of a new Lean artifact. I verified the identity of every arXiv reference cited above.

| CID | Fidelity verdict | Novelty label | References |
|---|---|---|---|
| **UMHSF1** | Mostly faithful; approximate floor needs its penalty; leakage terminology and attainment domain need qualification | **known** | [Balle et al., 1807.01647](https://arxiv.org/abs/1807.01647); [Issa et al., 1807.07878](https://arxiv.org/abs/1807.07878) |
| **UMSURVF1** | Faithful with schedule-specific bounds and probability restrictions | **classical** | [NIST](https://www.itl.nist.gov/div898/handbook/eda/section3/eda366i.htm); [LASR Appendix B.5](https://arxiv.org/html/2602.20628v1) |
| **UMPROTF1** | Faithful to its recursion; conditional-recall refinement and operational applicability remain unproved | **modest** | [Greenblatt et al., 2312.06942](https://arxiv.org/abs/2312.06942); [LASR, 2602.20628](https://arxiv.org/abs/2602.20628); [Shlegeris](https://www.alignmentforum.org/posts/GCqoks9eZDfpL8L3Q/how-to-prevent-collusion-when-using-untrusted-models-to) |
| **UMSTRATF1** | Upper bound supported; claimed attainment of that bound unsupported; per-class expenditure needs emphasis | **modest** | [NIST counting ingredients](https://www.itl.nist.gov/div898/handbook/eda/section3/eda366i.htm); [Shlegeris, mechanism context](https://www.alignmentforum.org/posts/GCqoks9eZDfpL8L3Q/how-to-prevent-collusion-when-using-untrusted-models-to). No exact published counterpart located |
| **UMNOGOF1** | Faithful finite, decodable-class, free-submission lower bound; broader impossibility inference unsupported | **classical** | [NIST iid/binomial ingredients](https://www.itl.nist.gov/div898/handbook/eda/section3/eda366i.htm); [Shlegeris, selective collusion](https://www.alignmentforum.org/posts/GCqoks9eZDfpL8L3Q/how-to-prevent-collusion-when-using-untrusted-models-to) |
| **CANONF1** | Faithful toy-language quotient and input/output preservation; deployed Python-marker claim unsupported | **classical** | [Leroy, verified compiler back-end, 0902.2137](https://arxiv.org/abs/0902.2137); [α-equivalence canonical representations](https://doi.org/10.1145/3656459) |
| **SANDBOXF1** | Faithful lexical mount model; insufficient for host-object confinement or confidentiality | **modest** | [Anderson’s reference-monitor requirements](https://csrc.nist.gov/files/pubs/conference/1998/10/08/proceedings-of-the-21st-nissc-1998/final/docs/early-cs-papers/ande72a.pdf); [Linux mount semantics](https://www.man7.org/linux/man-pages/man8/mount.8.html); [seL4 verification](https://sel4.systems/Verification/proofs.html) |

**Overall verdict:** retain the results as conditional infrastructure, correct the prose, and withhold deployed-system assurance. The supplied results do not warrant an “apparently open” novelty label. The package’s strongest potential contribution is a precise composition argument; that argument currently stops at recursions and abstract encodings.