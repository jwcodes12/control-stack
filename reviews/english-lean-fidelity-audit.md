# Adversarial English-to-Lean fidelity audit

**Audit date:** 2026-10-09  
**Repository:** jwcodes12/control-stack  
**Source under review:** main at **083874048518b68d754f0c392ad0cb84f01174ba** (resolved via GitHub git/ref/heads/main before the audit).  
**Review artifact:** reviews/english-lean-fidelity-audit.md  
**Review type:** independent assistant source-semantic adversarial review, **not** a kernel replay, external human attestation, or deployment certification.

## 1. Executive verdict

**No deployment-wide, adversary-independent bound on real-world catastrophe is established by the reviewed material.** This is principally an **applicability/composition gap**, not evidence that the proved Lean implications are logically false. Indeed, ROADMAP.md:3-20, PRIMITIVES-AND-SCENARIOS.md:3-13, CATASTROPHE-SPEC.md:1-14, ADVERSARY-CLASSES.md:1-27, and trusted_stack/README.md:1-23 already warn against that inference. Do not retroactively label these explicitly qualified documents as falsely advertising deployable assurance.

**Headline results that survive at their actual level of abstraction:** Gate.Spec.trace_safe is a sound *invariant preservation interface provided its Spec fields hold*; GatewayCore.core_bound limits exact recovery from its **finalView only**; refusal_blanks and close_freezes hold for the modeled event machine; sc01_case is a conjunction of conditional mathematical facts; covert_seq_seed bounds a **uniform secret independent of the seed** under per-seed domination; Lease.lease_safe and revoke_absorbing constrain their durable, charged model-log entries; GateClients.Artifact.deployed_is_reviewed proves equality of modeled contents subject to run-restricted hash injectivity; Approval.approval_safe establishes membership/expiry/nonrepetition in a modeled approval ledger; PolicyTamper.policy_preserved_if_protected assumes attackerCanWrite=false; GateComposition.shared_invariants is a correct generic two-invariant induction **when every joint step preserves both**; TMCERT abstraction results follow from their stated coverage/supermartingale premises; UMPROT/UMCERT and UM-adaptive results address their specified protocol, rather than the whole runtime.

**Material gaps:** (i) no proven complete external-effect mediation; (ii) no demonstrated complete receiver observation boundary for SC-01; (iii) the catastrophe/survival event for auditing is not damage-before-catch; (iv) monitor-composition probabilities rely on joint sampling or a strong bad-row premise; (v) the eight families are not shown to compose on one real shared causal state. Most are candidly acknowledged. The audit adds a sharper **event-semantics countermodel** for F6, and makes the quantified distinction between *a modeled effect log* and *actual effects* mechanically explicit.

**Severity interpretation:** HIGH below means a consequential **unverified applicability premise or an interpretation that would be false if promoted**, not a claim that the Lean theorem has a counterexample satisfying all its Lean hypotheses. No CRITICAL finding is awarded without such a contradiction or a genuinely unqualified central claim. No theorem compilation or fresh #print output was obtained in this environment; confidence is **source-conditional** pending kernel elaboration.

## 2. Scope, audit procedure, and limits

Read the repository's 865-entry THEOREM-REGISTRY.json and the headings/signatures in LEAN-STATEMENTS-NORMAL-FORM.md as an **inventory**, not as proof of completeness of elaborated binders. Cross-checked the named source files in ControlStack/Core/, ControlStack/Families/, ControlStack/GatewayCore.lean, SafetyCaseSC01.lean, HaltLiveness.lean, PolicyTamper.lean, GateComposition.lean, ComposeGame.lean, ComposeAvg.lean, ComposeCoverage.lean, ComposeBlindSpot.lean, MultiStep.lean; the UMPROTF1, UMADAPTF1/2, UMCERTF1 and TMCERTF1 proof ports; the scenario index and selected SC-01/03/13 manifests; trusted_stack/controller.py, server.py, README.md, STATUS.md; ROADMAP.md, STACK.md, CATASTROPHE-SPEC.md, ADVERSARY-CLASSES.md, PRIMITIVES-AND-SCENARIOS.md; and the earlier adversarial disposition. Earlier reviewers' dispositions were used **only to distinguish disclosure**, not accepted as independent validation.

The Lean toolchain is pinned as **leanprover/lean4:v4.34.0** (lean-toolchain:1). The available execution container had neither Lean/lake nor network access to clone this private repository. GitHub connector reads were pinned to the SHA above. Consequently **no fresh lake build, kernel #print, #check, #print axioms, or executable Lean countermodel was run**. The repository has prior CI/axiom records, but these were *not independently rerun*. Claims about implicit elaborated binder completeness remain **INCONCLUSIVE** and should be rechecked with the script in §9 on an authorized Lean host. Source-level types quoted here are **declared types**, not purported fresh elaborated outputs. All numerical/mathematical witnesses below are hand-inspectable, not falsely described as Lean-executed.

The inventory includes helper lemmas and many SOURCE_ONLY/UNKNOWN items. It is **not accurate** to say all 865 declarations were audited individually. Coverage is targeted at advertised security results. Unreviewed signatures, detailed scope, and verification backlog appear below.

### Compact fidelity matrix

| Theorem | English claim location | Fidelity verdict | Hidden/load-bearing premise | Counterexample / scope test | Required repair |
|---|---|---|---|---|---|
| ControlStack.Gate.Spec.trace_safe | Core/Gate.lean:46-63; PRIMITIVES:53 | **PASS** as conditional lemma; **HIGH** as universal physical-effect interpretation | Spec.inv_ok, step_inv, complete effects log | Harm bit changes while effects log is empty (§F01) | A concrete effect abstraction and exclusive-mediation refinement |
| ControlStack.Gate.withHalt_spec, halt_absorbing | Core/Gate.lean:82-124 | PASS modeled, HIGH physical HALT interpretation | HALT in action stream; no external pending work | Unmodeled queued effect commits after HALT (§F02) | Delivered kill + asynchronous-effect semantics |
| ControlStack.HaltLiveness.liveness_if_delivered | HaltLiveness.lean:34-47 | PASS conditional | DeliveredWithin is a premise | No HALT event means no conclusion | Scheduler/service liveness or bounded-delivery premise certified externally |
| ControlStack.GatewayCore.core_bound | GatewayCore.lean:263-295; SC-01:14-32 | PASS finalView; HIGH for total observations | Receiver sees only finalView; finite fixed length; uniform independent secret | Receiver sees close timing/one extraneous bit (§F03) | Sound complete-view refinement or certified side kernel |
| GatewayCore.refusal_blanks / close_freezes | GatewayCore.lean:82-96,150-181 | PASS for modeled finalView | Prior to first close; snapshot is entire delivered observation | External refusal latency remains visible | Include event timing/refusal outside finalView |
| ControlStack.SafetyCaseSC01.sc01_case | SafetyCaseSC01.lean:91-109; SC-01 manifest | PASS conjunction; HIGH if called integrated deployed case | Side mass, binomial sampling, no restore, exact nine-view charges | All five conjuncts true while unrelated runtime channel leaks (§F04) | Single joint protocol/correspondence theorem |
| ControlStack.Leakage.covert_seq_seed | Core/Leakage.lean:268-287 | PASS | Secret sampled uniformly independent of shared seed; per-seed K domination | Secret = receiver seed reveals secret even with zero transcript (§F05) | State secret/seed independence; correlated-secret bound |
| Leakage.audit_leak_bound | Core/Leakage.lean:418-427,576-613 | PASS for survInd; **HIGH** for harm-before-detection safety | Success = k attacks with **zero** audited attacks | N=B=k=1: audited irreversible attack causes harm, survInd=0 (§F06) | Define pre-effect Harm and prove interception theorem |
| Leakage.audit_adaptive_hidden | Core/Leakage.lean:633-668 | PASS ideal hidden schedule; MEDIUM deployment reading | Schedule secret; feedback only via modeled flags, sound perfect catches | External leak revealing next audited round | Quantify schedule observation and recall |
| Artifact.deployed_is_reviewed | Families/F4/GateClients.lean:192-206 | PASS model; HIGH deployed-bytes interpretation | Hash InjOn all final run contents; reviewer is trusted; deployed list is effect | Reviewer approves malicious payload; real deploy bytes differ (§F07) | Attested hash-to-bytes adapter, trusted review semantics |
| Approval.approval_safe | Families/F4/GateClients.lean:305-311 | PASS model; HIGH real authorization reading | .approve only by trusted principal; trusted clock; durable used list | Compromised approver issues exact harmful approval (§F08) | Cryptographic principals, revocation, real authorization policy |
| Lease.lease_safe / revoke_absorbing | Families/F5/Lease.lean:201-250 | PASS model; HIGH real resource reading | Cost represents resource; tick trusted; restart is identity; one global ledger | Zero clock advances despite real elapsed time; external work unmetered (§F09) | Trusted clock/meter/rollback-anchor/refinement |
| PolicyTamper.policy_preserved_if_protected | PolicyTamper.lean:21-43 | PASS conditional; MEDIUM if shortened | attackerCanWrite=false is embedded as run false | run true changes policy | Surface trust bit in all headlines; prove real policy protection |
| EgressGate.trace_safe | EgressGate.lean:38-92,126-130 | PASS transition invariant; HIGH if read as general network safety | safe topology is Boolean flags; policy tamper is stutter; immediate peer only | Tunneling via permitted peer, forged topology assertion (§F10) | OS/network confinement and policy integrity |
| GateComposition.shared_invariants | GateComposition.lean:16-27 | PASS conditional; HIGH as composition result | **Every** joint step preserves P and Q | Deputy uses A's credential to bypass B (§F11) | Discharge hJoint for each real transition incl. deputies |
| Compose.composedEndToEnd | ComposeGame.lean:24-30,90-103 | PASS under sampling model; HIGH if monitors correlated | M and T sampled independently, worst-case bad-row τ, r, L | Shared coin correlates pass verdict with dangerous view (§F12) | General joint-kernel theorem/conditional miss bound |
| ComposeAvg.composedPop_end / ComposeCoverage.composedCov_end | ComposeAvg.lean:113-155; ComposeCoverage.lean:87-105 | PASS for population-selection protocol; MEDIUM for arbitrary bad content | Attack content drawn from Apop; a(x) ≤ Kq(x)+e(x) | Red targets unseen blind spot (§F13) | Per-history, content-adaptive law coverage |
| PLDep_UMPROTF1.prot_bound, PL_UMCERTF1.claim_R/claim_C | proofs/UMPROTF1.lean:108-125; proofs/UMCERTF1.lean:315-353 | PASS conditional; INCONCLUSIVE full elaboration | Arbitrary Bad *predicate*, per-bad-row upper bound, scoped protocol | Real bad act not in X or Bad; coverage absent | Map actual effect event to Bad and certify domination/recall |
| PL_TMCERTF1.claimS / claimAbsV | proofs/TMCERTF1.lean:2-27,374-398 | PASS conditional; INCONCLUSIVE full elaboration | RiskCertUpTo; CoveredV simulation inequality | Abstraction omits a harmful concrete transition (§F14) | Machine-check a nontrivial concrete coverage relation |
| trusted_stack broker (not a Lean theorem) | trusted_stack/README.md:1-23; controller.py:222-252 | PASS **documented reference-only boundary**; HIGH if deployed controls claimed | OS UID integrity, SQLite persistence, external adapter absent | Agent effects external system while broker records zero releases (§F15) | Reference-monitor adapter and observational refinement |

Paths in the matrix are relative to repository root. “PASS model / HIGH interpretation” is *not* two contradictory assessments: the first concerns the source theorem's faithfully worded condition, the second the larger assurance claim someone might try to derive.

## 3. Findings with witnesses, corrections and formal repairs

### F01 — HIGH applicability, ALREADY ACKNOWLEDGED: generic Gate trace-safety can coexist with real harm

**Location.** ControlStack/Core/Gate.lean:35-58. The declared type of ControlStack.Gate.Spec.trace_safe accepts G, an entire Spec G, initial s and proof S.Inv s. The Spec has fields step_inv, log_prefix and inv_ok; in particular inv_ok is *already* “each logged effect is ok” under Inv. The conclusion merely propagates Inv, prefix and ok along the foldl trace.

**Mathematical witness.** Take St=Bool, Op=Bool, Eff=Unit; G.step(s,o)=o; G.effects(s)=[]; S.Inv(s)=True, S.ok(s,e)=True. All Spec fields are satisfiable. The trace [true] from false reaches the distinguished harmful Boolean true, while Spec.trace_safe still concludes its empty effect log is safe. This is **not a Lean counterexample**: it satisfies the theorem, demonstrating why it cannot imply safety of *unlogged* effects.

**Corrected statement.** “For every modeled finite operation trace from an Inv state, if the supplied state predicate is inductive, effect list append-only, and every Inv-state logged effect is ok, the final modeled effect list remains ok.” **Repair.** Give a semantics for all concrete harm-bearing transitions, define a total abstraction from concrete events to G.effects, and prove a forward simulation and no-bypass property. Avoid defining ok to be True as the only guarantee.

### F02 — HIGH applicability, ALREADY ACKNOWLEDGED: halt is absorbing by step definition, not a kill guarantee

**Location.** ControlStack/Core/Gate.lean:82-124; ControlStack/HaltLiveness.lean:34-68. withHalt's true flag makes later G.step a stutter. DeliveredWithin n ops explicitly requires an HOp.halt in the trace before index n. **Nothing proves the scheduler delivers it** or that an externally scheduled effect is canceled. Ordinary-operations-never-halt acknowledges this.

**Witness.** The broker authorizes queue entry q at time t0; at t1 a trusted HALT transitions the *model* to true; at t2 an external queue consumer commits q. The modeled after-HALT log is frozen but actual harm happened. No theorem hypothesis is falsified because that consumer is outside Op/effects.

**Corrected statement.** “Once a trusted halt operation has been processed by withHalt, subsequent operations of *that modeled machine* stutter; if a halt is delivered in a bounded trace the model's flag becomes true.” **Repair.** Include pending/outstanding effects and commit acknowledgements, trusted cancellation or compensating semantics, OS process termination liveness, and ordering guarantees for nonreversible effects.

### F03 — HIGH applicability, ALREADY ACKNOWLEDGED / EMPIRICALLY REFUTED IN ONE HARNESS: finalView is not all observations

**Location.** GatewayCore.lean:27-68 and 263-295. core_bound sums over randomized encodings of exactly L raw Ev events but the decoder input is only finalView(runG ...). Its image size is at most viewSpace = product of prefix counts. It does not prove that L, close arrival, refusal, CPU/cache state, worker timing, syscall outcomes, or external observations are secret-independent.

**Witness.** One allowed finalView value can be constant, while a shared cache line is set to secret bit m[0]. A receiver with the cache observation learns that bit deterministically. For a full 32-bit recovery countermodel, allow the receiver to read 32 side bits; P(exact recovery)=1 despite an unchanged nine-view transcript. These are outside the **Lean receiver input**, so they do not refute core_bound. The SC-01 manifest:43-52,64-78,113-125 candidly reports single-host cache-channel failure and VM usefulness failure.

**Corrected statement.** “For a uniform independent secret and a decoder whose complete input is the finite finalView and common seed, exact recovery is at most number-of-possible-views divided by number-of-secrets.” **Repair.** Sound abstract-observation coverage or history/seed-conditional side-channel kernel certificate including clocks, failure/refusal indicators, episode scheduling and all colluding receiver memory. Do not infer a deployed bound from JSON fields alone.

### F04 — HIGH applicability, ALREADY ACKNOWLEDGED: sc01_case is five implications in a product, not one instantiated safe execution

**Location.** SafetyCaseSC01.lean:91-109, Scenario manifest:14-32,55-103. The type is a conjunction of (i) a universally quantified **conditional** sideSuccess inequality given a side-mass certificate, (ii) a binomial false-pass inequality, (iii) numerical endpoint and threshold facts, (iv) 9 and 9^5 cardinalities, and (v) a no-restore, k=9 per-charge ledger lemma. These clauses refer to different abstract systems and do not supply a single value of W/c/enc/dec tied to the gateway's execution/side observations.

**Witness.** Choose a real execution with a second unmediated channel copying the entire secret. The finite combinatorial identities and conditional implications in sc01_case remain true: the second channel was never shown to meet the side-certificate premise. Its real recovery probability is 1. This is a **failure to instantiate**, not a false theorem. Numerically 9^5=59049 and 59049/2^32 is approximately 1.375e-5; the 2^-16 target allows side mass up to 65536/59049, but the theorem does not measure it.

**Corrected statement.** “SC-01 packages independent conditional safety, statistical, view-count and restore-free ledger facts; applying all facts to a single deployed receiver requires separately demonstrated correspondence, independence, observations and side mass.” **Repair.** Define a single lifetime process, event and observational refinement, prove that measured receiver observations refine the joint kernel, and carry the ledger and usefulness premises over that *same execution law*.

### F05 — MEDIUM mathematically; HIGH if independence suppressed, ALREADY ACKNOWLEDGED: covert_seq_seed bounds a fresh uniform secret

**Location.** Core/Leakage.lean:245-287. In ControlStack.Leakage.covert_seq_seed the risk expression explicitly averages (1/card M) over m **inside each seed ω**. Thus the source type prescribes the product secret–seed prior, not a correlated prior. The decoder may know ω and the visible transcript; domination c may depend on ω.

**Witness.** M=Ω=Bool, shared seed ω fair and secret m=ω. Let visible output be constant, and decoder report ω. Exact recovery is 1, exceeding the one-view independent-secret expression 1/2. No conflict: the changed prior violates the modeled independent sampling. **Corrected statement.** “Per-seed dominated finite-history observations bound exact recovery of an independently uniform secret, even with a shared seed and feedback.” **Repair.** Either attest secret independence or use an explicit joint prior P(m,ω) and a bound depending on best blind guessing probability conditional on ω.

### F06 — HIGH event-semantics gap; SHARPENED HERE (general damage-bound gap previously acknowledged): audit survival is not harm before detection

**Location.** Core/Leakage.lean:401-427, 518-533, 576-613 and 633-668. ControlStack.Leakage.survInd k S t = 1 exactly when the attackSet contains at least k rounds and is **disjoint** from audit set S. Consistent catch flags are defined to equal (attack && audited). Theorem audit_leak_bound upper-bounds this *survival event*, not the event “irreversible harm occurred,” nor “harm occurred before a catch could stop it.”

**Minimal exact witness.** Set N=B=k=1 and S={0}. At the only round the adversary chooses attack=true, and the catch flag is true; a concrete irreversible effect occurs before a detector consumes the audit verdict. The attack set is {0}, so Disjoint(S,attackSet) is false and survInd=0. Harm=1. With the only schedule audited, the combination ratio C(N-k,B)/C(N,B) is 0; hence a zero upper bound on survInd **coexists** with probability-one irreversible harm. Perfectly matches the model event; does not contradict audit_leak_bound.

**Corrected statement.** “The probability of at least k modeled attacks with no attacked round selected for audit is bounded under the stated hidden-schedule, flag-consistency and domination hypotheses.” **Not:** “the chance of harmful action before intervention is bounded.” **Repair.** Add an effect-causality semantics with states (pending, audited, denied, committed), require audit verdict before any irreversible commit, and prove P(Harm ∧ ¬Authorized) using a sound pre-effect audit predicate. If catch-after-effect is permitted, bound damage separately; never identify ‘caught’ with ‘prevented.’

### F07 — HIGH applicability, ALREADY ACKNOWLEDGED: reviewed digest is not safe deployment

**Location.** Families/F4/GateClients.lean:110-136,186-206. In Artifact.deployed_is_reviewed, trusted review is a constructor Op.review(c); set injectivity is on **store ∪ reviewedContent in the final run**. It proves modeled deployed c was among modeled reviewedContent. No semantic benignness, secure reviewer authenticity, external binary or fetch semantics follows. Collision breaks witness at :208-213 is genuine and material (not merely a tautology).

**Witness.** Trusted reviewer approves an artifact c containing a harmful shell script, hash uniquely identifies c, and modeled deploy c executes. The theorem is true while harmful behavior occurs. Alternatively external adapter deploys c'≠c after the modeled effect record; theorem is true because external bytes are not modeled. **Corrected statement.** “Subject to run-local hash injectivity and trusted reviewer operations, deployed *model-list contents* belong to the modeled review list.” **Repair.** Attested reviewer identity and byte-level deployment equivalence; separately prove policy/semantic safety of approved content or state that review is only an authorization control.

### F08 — HIGH applicability, ALREADY ACKNOWLEDGED: any modeled trusted approval is accepted

**Location.** Families/F4/GateClients.lean:240-271,305-345. Approval.approval_safe requires exact Tx membership, expiry by s.now and used nonce distinctness, but never states an approval is prudent or the approver uncompromised; .approve is a constructor outside agentOp. The clock advances only on .tick, and restart/rollback do not appear.

**Witness.** A compromised signer emits .approve for a destructive Tx(p,n,e), followed by .execute while now≤e; safety theorem holds (membership, time, unique nonce) while destruction is authorized by the model. **Corrected statement.** “Modeled executions require an earlier matching approval record, logical unexpired time and unused nonce.” **Repair.** Signer-key trust, custody and compromise model; durable nonce storage, rollback-resistant time, semantic policy and a formal delegate authorization graph.

### F09 — HIGH applicability, ALREADY ACKNOWLEDGED: Lease costs/time/restart are modeled, not measured

**Location.** Families/F5/Lease.lean:45-105,201-271. spend and total sum the cost field of *admitted .work events*; the model refuses c<1, unexpired lease requires s.now≤expiry, and .restart is exactly identity. .fork creates only fresh holders. This supports genuine nontrivial unit-count bounds for the model and fixes previous zero-cost/fork weaknesses, but says nothing about actual CPU, remote API costs or power failures.

**Witness.** Initial trusted issue lease(id=0,budget=1,expiry=0) at now=0; arbitrarily much external computation elapses without .tick; one .work(worker,1) can still be admitted at modeled now=0. Or real background worker consumes resources without submitting Op.work: log cap holds while physical spend is arbitrarily high. **Corrected statement.** “Serialized, positive-cost modeled work entries obey per-lease/global recorded caps and never append under a revoked lease.” **Repair.** A trusted meter maps actual effects to costs, monotonic time, global identity/counters, append-only cross-restart/anti-rollback store, and race/crash refinement.

### F10 — HIGH applicability, ALREADY ACKNOWLEDGED: egress confinement assumes the very topology it needs

**Location.** EgressGate.lean:38-92,126-130 and PolicyTamper.lean:21-43. Topology.safe computes AND of five supplied Boolean flags including noExternalRoute, protectedPolicy, noHostDeputy. Under safe, .directAttempt stutters; .tamperPolicy always stutters. PolicyTamper separately demonstrates a write action changes activePolicy when attackerCanWrite=true. Egress events are *immediate peer attempts*; tunnel payload/destination beyond a permitted peer are out of the event semantics.

**Witness.** A permitted CONNECT proxy routes an unauthorized byte stream; the only logged peer is the permitted proxy. The immediate-peer invariant holds, confidentiality and distal destination restrictions fail. Or in a real host policy is writable despite a modeled safe Boolean. **Corrected statement.** “Under an asserted safe topology and fixed policy, this transition system only logs gateway-origin attempts to pinned immediate peers.” **Repair.** Validate flag predicates against OS states; link actual sockets and inherited descriptors to effects; model destination behind proxy and tamper authority explicitly.

### F11 — HIGH if sold as an F1–F8 composition certificate, ALREADY ACKNOWLEDGED: hJoint is the work

**Location.** GateComposition.lean:16-49. shared_invariants requires hJoint : ∀x a, P x→Q x→P(step x a)∧Q(step x a). That is **the desired joint step preservation assumption**. It does not follow merely by applying two separate gate invariants to unrelated states. The module itself proves confused_deputy_counterexample in :38-49.

**Witness.** Set gate A approved=true, gate B approved=false and invokeTrustedDeputy; the unsafe deputy sets externalEffect=true although B refuses direct requests. This is a verified source witness (the proof is rfl); not a claim that shared_invariants is false. **Corrected statement.** “Two invariants are preserved by arbitrary finite traces provided their conjunction is inductive under the same actual transition relation.” **Repair.** A concrete single-state action alphabet, authenticated deputy authority, global principal and budget ownership, interleaving/race/rollback analysis, and checked hJoint for every joint transition.

### F12 — HIGH applicable only if sampling assumptions fail, PARTLY ACKNOWLEDGED: joint monitor independence is by construction

**Location.** ComposeGame.lean:24-34,68-103. jointView samples z from M(x), then t from T(x) with fresh ProbComp coins; joint_pass_prob factorizes the pass probability using that construction. htm bounds T(x) for each Bad x, hdom bounds each bad mediated view, and hrec bounds an audit catch probability for every bad history/view.

**Countermodel to a stronger claim (not to Lean).** Let marginally Z=Bool and trusted PASS T=Bool each have probability 1/2. Take untrusted D(z)=z. Under independent draws P(Z=true ∧ T=true)=1/4; under common coin Z=T, P(joint PASS)=1/2. Marginals and worst-case row means are unchanged, but factorization fails. **Corrected statement.** “The composed bound holds for the specifically independent joint sampling law and the per-bad-content domination, trusted-miss and catch premises.” **Repair.** Replace product sampling with a general joint J and establish a conditional joint bad-row bound as in ComposeAvg.composedJ_end; certify correlated-randomness behavior or avoid using factorization.

### F13 — MEDIUM; PARTLY ACKNOWLEDGED: population composition does not grant arbitrary content-adaptive attack selection

**Location.** ComposeAvg.lean:113-155, ComposeCoverage.lean:25-37,87-105, ComposeBlindSpot.lean:19-41. The generator π chooses when to output none (“attack”), but popJ none then samples content independently from a fixed Apop. Coverage requires pointwise Apop(x)≤K·Cal(x)+e(x) with Σe≤ε. That is not a theorem about all possible history-dependent conditional attack-content distributions. The repository's blind_spot_risk explicitly demonstrates an adverse population gap.

**Witness.** Calibration concentrates on safe x0; the adversary intentionally chooses x1 with trusted-miss 1 and Cal(x1)=0; without a K/ε that covers x1, population-average recall is not a worst-case bound. **Corrected statement.** “The population-average bound permits history-dependent attack timing while content for each attack is drawn from a fixed, coverage-certified attack population.” **Repair.** Require coverage of every conditional content law given the attacker's observation history, or return to a per-bad-x bound.

### F14 — MEDIUM/INCONCLUSIVE elaboration: TMCERT certificates are conditional value upper bounds

**Location.** proofs/TMCERTF1.lean:2-27,374-415. claimS assumes AdmKNonneg, RiskCertUpTo, IsPolicy and SelectorUpTo; claimAbsV assumes concrete nonnegative K, CoveredV and RiskCertUpTo. CoveredV is the consequential simulation/upper-bound premise. The theorem *does* quantify every policy within its finite game and action space; it does *not* prove that real harm maps to Gc.cat or that actual transitions satisfy CoveredV.

**Witness.** A concrete game with an extra irreversible operation not in the abstract action/effect relation has no established CoveredV instance; one cannot conclude its risk is bounded by an abstract certificate. **Corrected statement.** “Any finite concrete game satisfying the stated coverage and risk-certificate inequalities inherits their risk upper bound.” **Repair.** A constructive CoveredV proof for a nontrivial admitted concrete system; inspect all implicit typeclass assumptions using #print.

### F15 — HIGH for production, PASS on documented reference scope, ALREADY ACKNOWLEDGED

**Location.** trusted_stack/controller.py:140-154,222-252,254-264; server.py:20-56,73-92; trusted_stack/README.md:1-23,44-50. Peer UID from SO_PEERCRED is used in server.py, role sets required disjoint, release checks exact approval/digest/nonce/lease/global cap in BEGIN IMMEDIATE, then appends an SQLite releases row. It does not execute or intercept any external harmful action. The service serializes one request loop, has no actual distributed resource meter, and assumes host/database/clock integrity. These documented checks are substantial, but **the only committed effect is a record**.

**Witness.** Agent runs an unmediated process, network operation or privileged deputy call; releases table remains empty. The broker has not failed any of its documented predicates; it was simply never in the causal path. **Corrected statement.** “The reference broker atomically authorizes and records a one-unit release under stated OS/database assumptions; no external effect is created or exclusively mediated.” **Repair.** Define and deploy a real sole-entrypoint effect adapter; capture denied and authorized external effects, test bypass, race, kill and restart; establish a refinement across returned record IDs and actual commits.

## 4. Coverage across eight primitive families

| Family | Reviewed evidence | Verdict at mathematical level | Deployment/composition status |
|---|---|---|---|
| F1 capability | Gate, NoAgentEffects, EgressGate, PolicyTamper, AuditDispatch | Model transition invariants; conditional PASS | No universal OS mediation / tamper proof; HIGH applicability |
| F2 observation | GatewayCore, CovertChannel linkage, Leakage.covert_seq_seed, sc01_adaptive_target, SC-01 | Finite-output and dominated-side-kernel bounds; conditional PASS | Receiver's complete lifetime view unproved, cache refutation; HIGH |
| F3 time/halt | withHalt, HaltLiveness, AuditDispatch, LifetimeLedger linkage | Model halt absorbing; DeliveredWithin conditional; PASS | Asynchrony, crash, termination, rollback open; HIGH |
| F4 integrity | Artifact.deployed_reviewed/is_reviewed, collision_breaks | PASS subject to on-run injectivity | Reviewer trust, content safety, deploy byte correspondence open; HIGH |
| F5 leases | lease_safe, revoke_absorbing, work_count_le, fork_without_lease_accounting | PASS positive-cost modeled units | Clock, restart, true metering, cross-service global budgets open; HIGH |
| F6 monitoring | UMPROT/UMCERT, UMADAPT sources, MultiStep, Leakage auditing, Compose*, TMCERT | Conditional row-wise and finite-game guarantees; PASS scoped / INCONCLUSIVE exhaustive | Real Bad coverage, worst-case recall, content adaptivity, audit before harm open; HIGH |
| F7 approval | approval_safe, agent_cannot_approve, replay_if_nonces_lost | PASS exact modeled approval/nonce | Signer trust and clock/nonce persistence open; HIGH |
| F8 composition | GateComposition, ComposeGame/Avg/Coverage, Leakage.seq_transfer | PASS respective shared-state or probabilistic law | No common production F1–F8 operational semantics; HIGH |

**Inventory handling:** the 865 indexed declarations were consulted to select security-facing claims, not kernel-printed in bulk. TECHNICAL HELPERS were grouped by their role (cardinality/finite mass, induction, combintorics, game-value recursion, simulation, witnesses). **Not fully reviewed:** all numbered helper declarations not explicitly discussed; detailed theorem bodies in UMADAPTF1/UMADAPTF2 beyond identified claims/witnesses; exact elaborated PL_UMADAPTF1/2.Claim records; UMSTRAT, UMDEFER, UMSURV, UMLOWER, UMNOGO, UMHS, UMUSE, CANON, TMGAC, TMLIP, TMCERTUS, TMGAC subresults; broad proofs/ source library; all 28 manifests (only index and SC-01/03/13 inspected); exhaustive per-file proof imports; all scenario/ receipt contents; detailed external code of egress/auditgate/gateway VMs; complete trusted_stack test execution. Those are **INCONCLUSIVE**, not silently PASS. The most significant next checks are any user-facing “end-to-end,” “catastrophe,” “sharp converse” and “safe” theorems in these modules; compare declared Claim record elaborations and exact Bad/cat/event meanings.

## 5. Composition and countermodel summary

**Genuinely supported:** Gate.withHalt_spec lifts an existing gate's *same* spec into its product with a flag; Leakage.seq_transfer chains dominated observation kernels on a *common visible-history type*; the composition lemmas compose untrusted and trusted monitors when the modeled joint law, recall and bad-row bounds hold; GateComposition.shared_invariants composes arbitrary predicates *once a shared step relation proves hJoint*; the SQLite transaction composes checks before a **release-row append**.

**Not established:** deriving hJoint from separate F1/F4/F5/F7 results; identifying a finite receiver view with all machine observations; treating one model's worker ID as a globally exclusive OS principal; per-worker limits as per-system limits; combining shared-seed, population, and audit sampling while preserving independence; applying a bound under fixed Apop to an attacker selecting arbitrary new content; treating checked approvals as independent of compromise; allowing deferred or irreversible effects after modeled HALT without additional semantics.

**Minimal conflicting composition:** an authorized A-principal triggers a deputy's effect in B's namespace. Each local model may preserve its own allowed-ops invariant while the global desired B predicate fails. GateComposition.confused_deputy_counterexample explicitly witnesses that failure. The repair is a joint authority semantics, not multiplication of separate failure probabilities.

## 6. Strongest warranted English guarantees

1. **SC-01 confidentiality:** “For an independent uniformly random 32-bit secret, five episodes with nine receiver-visible values each, and a fully bounded additional side-observation kernel satisfying the specified mass certificate, the modeled exact-recovery probability is at most 2^-16. The real environment has **not** demonstrated that complete observation certificate.” No broader anti-collusion or low-bit command prevention follows.
2. **Gate/confinement:** “The modeled effect log meets the declared invariant under all modeled operations if that invariant and the step/link premises hold.” Actual exclusive interception remains a separate obligation.
3. **HALT:** “Modeled operations after a *delivered* HALT do not change modeled state/effect list.” Not physical kill or reversal of queued effects.
4. **Artifact/approval:** “A model release corresponds to modeled reviewed content / approved exact transaction given trusted reviewer/signature and durable nonces/time.” Not proof that approved content is harmless or actual bytes match.
5. **Lease:** “Recorded positive-cost work never exceeds modeled per-lease/global caps; revoked lease IDs admit no new modeled entries.” Not physical resource caps.
6. **Audit/honeypots:** “The probability of the specified modeled uncaught/surviving bad event is bounded for the stated Bad predicate, observation distribution, calibration coverage, audit timing, recall and independence assumptions.” Not general harm prevented.
7. **Full stack:** “There are conditional component theorems and a reference SQLite release recorder; there is not yet an end-to-end deployment theorem spanning real effects, total observations, all agent principals, and timing.”

## 7. Reproduction and independent-check instructions

**Source commit pin:** 083874048518b68d754f0c392ad0cb84f01174ba. **Toolchain:** leanprover/lean4:v4.34.0. **Acquisition:** authenticated GitHub connector fetch_file with ref set to the pin; GitHub ref/heads/main resolved this SHA at audit start. **Observed results:** source retrieval succeeded for cited paths; typed Lean execution, #print elaboration, #print axioms and test execution were **NOT RUN**. Prior GitHub workflow evidence cited in ROADMAP/reviews is not a new test here. No existing source theorem or receipt was modified.

On a host with repository access and the pinned Lean toolchain:

    git fetch origin main
    git checkout --detach 083874048518b68d754f0c392ad0cb84f01174ba
    cat lean-toolchain
    lake build ControlStack
    mkdir -p /tmp/control-stack-fidelity
    cat >/tmp/control-stack-fidelity/PrintFidelity.lean <<'EOF'
    import ControlStack
    #check ControlStack.Gate.Spec.trace_safe
    #print ControlStack.Gate.Spec.trace_safe
    #print axioms ControlStack.Gate.Spec.trace_safe
    #print ControlStack.GatewayCore.core_bound
    #print axioms ControlStack.GatewayCore.core_bound
    #print ControlStack.SafetyCaseSC01.sc01_case
    #print axioms ControlStack.SafetyCaseSC01.sc01_case
    #print ControlStack.Leakage.covert_seq_seed
    #print ControlStack.Leakage.audit_leak_bound
    #print ControlStack.HaltLiveness.liveness_if_delivered
    #print ControlStack.GateClients.Artifact.deployed_is_reviewed
    #print ControlStack.GateClients.Approval.approval_safe
    #print ControlStack.Lease.lease_safe
    #print ControlStack.Lease.revoke_absorbing
    #print ControlStack.PolicyTamper.policy_preserved_if_protected
    #print ControlStack.GateComposition.shared_invariants
    #print ControlStack.Compose.composedEndToEnd
    #print ControlStack.ComposeAvg.composedPop_end
    #print ControlStack.ComposeCoverage.composedCov_end
    #print axioms ControlStack.GateComposition.shared_invariants
    EOF
    lake env lean /tmp/control-stack-fidelity/PrintFidelity.lean

For proof ports also read/show the fully qualified structures PL_UMPROTF1.Claim, PL_UMADAPTF1.Claim, PL_UMADAPTF2.Claim, PL_UMCERTF1.Claim and PL_TMCERTF1.Claim after importing their corresponding modules in a separate scratch file. If imports fail, find the module names in lakefile.lean and report unresolved instead of silently skipping. For each theorem, turn on Lean's elaborator display options when useful, expand definitions and inspect all bound instances and typeclasses.

**Countermodel 1 (F01), model-theoretic, reproducible:** Bool state, Bool action, empty List Unit effects, Inv=True, ok=True, step(s,a)=a. A dangerous state value true is reachable and the empty effects list remains “safe.” Implement as an isolated file importing ControlStack.Core.Gate, not as a modification to existing proofs.

**Countermodel 2 (F06), exact finite enumeration:** N=B=k=1, S={0}, observation sequence t=[(attack=true, side=(), caught=true)]. attackSet(t)={0}; Disjoint(S,attackSet(t))=False; survInd=0. Independently attach a concrete harm flag H(t)=True when any attack commits before detection; then H(t)=True while survInd=0. Implement with a finite enumerated state machine and use #eval/decide where supported; compare all events before a catch.

**Countermodel 3 (F12), elementary joint table:** two Bernoulli(1/2) marginals; product law table P(0,0)=P(0,1)=P(1,0)=P(1,1)=1/4 versus common-coin law P(0,0)=P(1,1)=1/2, off diagonal 0. D(z)=z and trusted PASS=t: product joint acceptance 1/4, correlated acceptance 1/2. This tests exactly why jointView's conditional independence is indispensable.

**Nonvacuity tests to add:** for each advertised bound, give a **nonempty** concrete satisfying model with nonzero relevant bad-event probability and a bound strictly below 1; also give a negative test mutating one premise (unmediated effects, dishonest clock, correlated seed, coverage hole, audit-after-effect, duplicate nonce after rollback). Verify both that the first model discharges assumptions and that the second cannot be inadvertently certified.

## 8. Prioritized repairs by real assurance gain

1. **P0 — Real harm/event interface and exclusive mediation.** Define and measure pre-effect commit semantics, pending/async operations, external system responses, deputies, and trace completeness; link gateway/SQLite to real effects. This would change safety meaning most.
2. **P0 — End-to-end SC-01 full receiver observation.** Isolate receivers; measure clocks, cache, host, feedback, status and schedule observations; bind side certificates to the same lifetime as the 9^5 gateway trace; preserve the failed original protocol receipts.
3. **P0 — F6 damage-before-catch event.** Differentiate audit *selection*, effective detection, and physical prevention. Verify a stopping/cancellation theorem for catastrophic effects or explicitly price harm already incurred.
4. **P0 — Single joint F1/F3/F4/F5/F7/F8 transition semantics.** Prove hJoint by checking every transition, including delegated and concurrent effects. Discharge common principal and shared-budget obligations.
5. **P1 — Clock, resource meter, crash and durable anti-rollback anchors.** Connect lease cost, lifetime and approval expiry to trusted physical measurements, not counters the adversary can skip.
6. **P1 — Cryptographically rooted provenance and approval.** Bind reviewer identity and exact deployed bytes; include compromised signer and malicious approved content as distinct threat models.
7. **P1 — Worst-case/adaptive monitoring evidence.** Require per-bad-row or per-history coverage of content and side observations, imperfect conditional catch rates, false-positive audit budget and fresh held-out measurements.
8. **P1 — Kernel-elaborated goal review.** Execute every #print/#print axioms command at pinned SHA, expose implicit binders and audit selected UMPROT/UMADAPT/UMCERT/TMCERT proof records with explicit threat/event mapping.
9. **P2 — Fill scenario portfolio.** The current scenario index records 3 CONDITIONAL and 25 DRAFT; produce independent usefulness and negative controls rather than treating manifest coverage as runtime completion.

## 9. Sign-off

**Verdict:** meaningful conditional formal work, no demonstrated false Lean theorem from the material inspected, and no operational F1–F8 assurance certificate. **The biggest danger is promoting a correct theorem about a restricted event space into a real-world universal catastrophe bound.** Earlier repository documents mostly resist that promotion; keep those disclaimers. The F06 irreversible-harm-versus-survival witness is a concrete reason any future deployment headline must state *what the bad event is and when the effect occurs*.

**Limitations of this artifact:** This is a substantial source-level adversarial audit, not the complete 865-declaration kernel-elaborated review demanded by the original ideal methodology. Unexecuted repro snippets and unreviewed modules are clearly flagged; no independent human, runtime or Lean acceptance claim is made.
