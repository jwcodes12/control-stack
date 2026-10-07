# Related-work audit for the control-stack programme, 2026-10-07

Scope: six requested sources, plus the neighbours I found while searching. Read-only with respect to the rest of
`control-stack/`. Nothing was built and no Lean was run. Clones are in `<scratch>/` (`formal-confinement`,
`aisec-via-fm`, `control-tower`, `lagi-hackathon`, `legitimacy`, `soundgate-paper`) with PDFs and text extractions
beside them (`g4c.txt`, `sg.txt`, `mol.txt`, `lasr.txt`, `ac.txt`, `toy.txt`).

Evidence tags used below:
- **[R]** I read the primary text or source files.
- **[S]** I saw only a search-result or abstract snippet.
- **[I]** My inference; not stated by the source.

## 0. Honesty ledger: what I could and could not verify

| # | Source | Found? | What I read |
|---|---|---|---|
| 1 | Formal Confinement (Quinn Dougherty) | yes | repo `for-all-dev/formal-confinement` (clone; HEAD `42b95c9`, 2025-06-26): readme, agent-instructions file, `fcp/` protocol code, `imp/` Lean sources, `comms/odyssey/main.typ` (the whitepaper source, not the PDF), `comms/lesswrong/post.org`; the LessWrong linkpost (24 Nov 2025) |
| 2 | "AI Control via Proof-Carrying Code" agenda | yes, but thin | AF/LW sequence page (4 entries); text of 3 posts (linkpost, "Beliefs about formal methods and AI safety", "Please Measure Verification Burden"); repo `for-all-dev/aisec-via-fm` problem statement `paper/problems/ai-control-proof-carrying-code.typ` (read in full) |
| 3 | "Legitimacy" repo | yes | `abenenson/legitimacy` (clone; HEAD `0a1b2b1`, 2026-09-17): README, `papers/05-structural-audits.md`, `lean/Legitimacy/Audits/AIControl.lean` (UM and defer fixtures), `audits/ai-control/untrusted-monitoring-graph.json`, claim ledger C15, `FRAMEWORK-LIMITS.md`, axiom-footprint script. I only skimmed `Behavioral/AIControlLineage.lean` (declaration names) |
| 4 | SOUNDGATE / Stop Means Stop (arXiv 2607.14166) | yes | full paper text (v3, 8 Aug 2026), repo `sajjadanwar0/soundgate-paper` (clone; HEAD `bf79b29`, 2026-10-02): `formal/README.md`, `formal/verus/gate_model.rs` (head), `formal/tla/SoundGate.tla` invariants, receipt tails (`verus.txt`, `tlapm.txt`, `tlc_4x3.txt`). I did not run Verus/TLC/TLAPS/Loom |
| 5 | Games for AI Control (arXiv 2409.07985) | yes | PDF v2 (7 May 2026): main text, Appendix B (full TM game), Appendix C.1 (Prop 4.1 recursion), appendix headings; the author's LessWrong post. I did **not** read Appendix A proofs line by line |
| 6 | Molnar, Reliability Theory for AI Control (arXiv 2609.26419) | yes | PDF: abstract, intro, §2–3, reference list; grep over the whole text for Lean/Coq/UM/honeypot terms (none) |

Things I could not do or did not do:
- **Quinn's "Cruxes" post itself.** The AF sequence called "Cruxes for AI Control via Proof Carrying Code at the End of
  2025" has only the description "What does a high quality, cheap, and binary grader add to a control protocol?" plus
  three posts. I found no standalone "Cruxes" post. The sequence says 1-2 more posts are planned. [R]
- **No control-protocol language exists in what I found.** The "resampling, deferral, trusted editing" language is a
  single speculative paragraph (§2 below), not an artifact.
- **greaterwrong.com** was unreachable from this box (curl timeouts). I used lesswrong.com and alignmentforum.org instead.
- **GitHub API repository search returned empty results** (no error text). The negative finding "no Lean/Coq/Isabelle
  repository for untrusted monitoring or honeypots" therefore rests on several web searches plus the author lists
  of the papers, not on an exhaustive code search. Absence of evidence only.
- **Not read:** Greenblatt et al. 2312.06942 (cited only via LASR/Games), Appendix C of that paper (slack test),
  Korbak et al. 2501.17315, Mallen et al. 2412.12480, Towards Guaranteed Safe AI 2405.06624, Perrier 2506.17846
  (abstract snippet only), TraceGuard 2604.03968 (abstract only), Alignment Contracts 2605.00081 (abstract, intro and
  the Lean-artifact appendix only).
- **N1/N1b/K5/CLK/LUREF judgements** rest on the STACK.md one-liners; I did not open the earlier trusted-monitoring project.

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

## 2. Per-source audit

### 2.1 Quinn Dougherty, Formal Confinement (FC)

**Citation.**
- Repo: https://github.com/for-all-dev/formal-confinement (HEAD 2025-06-26; the repo previously lived under
  `quinn-dougherty/` and `Beneficial-AI-Foundation/`; the files name all three).
- Whitepaper "Formal Confinement" (Odyssey draft), `comms/odyssey/main.typ`/`main.pdf` in the repo.
- Linkpost: https://www.lesswrong.com/posts/yZvrRWM5DE58CzHpZ/formal-confinement-prototype (24 Nov 2025); part of the
  sequence https://www.alignmentforum.org/s/f9ewpmtz8AogLxvqx. The linkpost says the whitepaper was "a preliminary
  approach ... last summer", so the artifact is June 2025 and the write-up is Nov 2025.

**What it builds.** [R]
- A Python box (`fcp/`, MCP client/servers, litellm). A "programmer" LLM writes a program in `imp`: integer-valued
  skip / sequence / assign / if / while. A "prover" LLM loops (bounded by `MAX_ITERATIONS`) to produce a Lean proof of
  the user's Hoare triple `{P} c {Q}`. `multipolarity` runs a positive and a negated proof attempt concurrently.
- The boundary executes the code only if Lean accepts (exit code 0). The whitepaper suggests GPG-signing the Lean
  file plus exit code and toolchain version as an attestation.
- Lean side (`imp/`, toolchain v4.20.1, forked from David Christiansen's SSFT24 tutorial): big-step semantics, Hoare
  triples, rules skip/seq/assign/consequence/while, tactic `auto_hoare_pos`.
- Experiments: 4 models x 3 specs (`gt8`, `swap`, `facto`); "verification burden" 1.5-4.2 (LW post).

**What is machine-checked.**
- Only the object-level Hoare-logic rules. There is no Lean theorem about the *protocol* (such as "every executed
  program satisfies its spec"). That property holds by construction of the gate plus Lean's kernel soundness.
- `imp/Imp/Hoare/Rules.lean` lines ~82-100: `hoare_while` is proved via `hoare_while_aux_left` and
  `hoare_while_aux_right`, each containing a `sorry`. [R]
- [I] The first aux lemma, as stated (`while b c / sigma -> sigma'` implies `c / sigma -> sigma'`), looks false for loops
  with two or more iterations, so the while rule's proof is not just incomplete.
- [I] `imp/Check.lean` detects sorry with `Expr.hasSorry` on the theorem's value term only. A proof that merely *calls*
  `hoare_while` would not show `sorryAx` in its own term. I did not run it; this is a reading.
- Net: a prototype, as the author says. It is not a trusted artifact for loops.

**In scope / out of scope** (the paper says so itself). [R]
- In: a deterministic spec gate on a toy language. Lampson's confinement rules "almost for free" because the language
  is so restricted.
- Out: side channels, non-toy languages, probabilistic semantics (explicitly deferred to Safeguarded AI), any
  untrusted-monitor / honeypot / collusion model. "Demonstrate subversive code getting caught by the protocol" is listed
  as future work. A hardened-MCP leak (log permissions) is flagged.

**Overlap with our results.**
- UMHSF1 / UMSURVF1 / UMPROTF1 / UMSTRATF1 / UMNOGOF1 / UMLOWERF1: **disjoint.** The gate is deterministic and sound;
  there is no statistical monitor and no test slack.
- CANONF1: **adjacent.** Both are Lean treatments of a toy imperative language.
  - FC has Hoare logic and no `for`.
  - Ours has the canonicaliser plus semantics preservation.
  - No shared definitions.
- SANDBOXF1/2F1: **adjacent.** Same genre (confinement) at a different layer: FC confines the *output language*,
  ours confines *file writes by a sandboxed process*.
- UMDEFER (in progress): a contrast, not an overlap. [I]
  - FC's boundary replies "try again, I'm not executing that" and asks for a new program, which is retry/resample.
  - With a *sound deterministic* check, retries cost no safety.
  - Our variant-D result says the opposite for a *statistical* flag: K unincriminated retries inflate risk to up to
    `1-(1-h)^K`-style amplification.
  - The sharp statement is that retry is free iff the check has no false passes.

**Cite / reuse.**
- Cite as the nearest "proof-gated output" prototype, with the sorry caveat if anyone relies on it.
- Reuse the *verification-burden* reporting format from Quinn's companion post (proof tokens / implementation tokens,
  with variance and metadata). It fits the ledger directly and costs little.
- Reuse nothing from the Lean code (our toy language is further along).

**Novelty labels.** No change.

### 2.2 "AI Control via Proof-Carrying Code" agenda (Quinn / Forall)

**Citation.**
- AF sequence "Cruxes for AI Control via Proof Carrying Code at the End of 2025":
  https://www.alignmentforum.org/s/f9ewpmtz8AogLxvqx (sequence dated 24 Nov 2025). Posts:
  - "Formal confinement prototype" (24 Nov 2025);
  - "Beliefs about formal methods and AI safety" (23 Oct 2025),
    https://www.lesswrong.com/posts/CCT7Qc8rSeRs7r5GL;
  - "Please Measure Verification Burden" (23 Nov 2025), https://www.lesswrong.com/posts/SG82BkTDQDAjANRWj.
- Repo https://github.com/for-all-dev/aisec-via-fm (HEAD `33179cd`, 2026-10-02; README: "DRAFT PREALPHA NOT PUBLIC IN
  PROGRESS"; no LICENSE file). The agenda text is `paper/problems/ai-control-proof-carrying-code.typ` (author tag:
  quinn).

**What it is.** [R] A *problem statement*, not a protocol or a theorem. The argument:
- PCC (tag every action with a checkable certificate) and AI Control (a weaker trusted monitor plus a scarce audit
  budget on a safety-usefulness frontier) are two answers to the same interface problem. Their "deterministic
  midpoint" is FC.
- The open question is whether it pays for itself, via the verification burden `k`.

Three subproblems:
- **Graded gatekeeping.** Replace the binary "proof closes or not" with a "warmness" signal. This is a *learned
  value function over tactic sequences* feeding a control protocol, evaluated "in a backdoored-code testbed in the
  style of Greenblatt, with a published ROC curve on audit-budget-vs-catastrophe-rate".
- **Specialist blue-team checkers.** Small models with custom tactics.
- **Upfront vs ongoing investment.** The blue-team/red-team budget asymmetry changes sign if the red team pays for proofs.

**The protocol-language idea.** [R] One paragraph, labelled "Speculative and out-of-scope for the near-term":

> "An AI-control analogue [of Dolev-Yao] -- a process calculus in which resampling, deferral, and trusted-editing
> primitives have first-class semantics and attacker capabilities are syntactic -- would let protocol designers
> discharge parts of the soundness argument at design time rather than per deployment."

It cites Dolev-Yao 1983. There is no syntax, no semantics, no theorem, and no code. I searched for a built version
(process calculus / Dolev-Yao for AI control) and found none; the nearest hit, "Formal Semantics for Agentic Tool
Protocols: A Process Calculus Approach" (Schlapbach, 2603.24747), concerns MCP versus SGD tool protocols, not control
protocols. [S]

**What is machine-checked.** Nothing here. (Companion repos `lagi-hackathon` "Verified Egress Inference" and
`control-tower` (a fork of LinuxArena's Control Tower) are system/eval repos. I looked only at READMEs.)

**Overlap.**
- UM* CIDs: **disjoint.**
- UMUSE: **adjacent.** "Graded gatekeeper with an audit-budget-vs-catastrophe-rate ROC" is a safety/usefulness-style
  frontier with a proof-closeness score as the monitor signal.
- VCVio protocol refinement (in progress): **adjacent, and the only place anyone names it.** A ProbComp-level protocol
  with a universally quantified adversary is a concrete instance of "protocols as programs with attacker capabilities
  as syntax". Ours is not a process calculus and has no resampling/trusted-editing primitives yet.

**Cite / reuse.**
- Cite the paragraph as the statement of intent that a machine-checked protocol semantics is wanted. [I] Hedged claim
  we may make: "to the best of a limited search we found no built machine-checked control-protocol semantics".
- Reuse the "warmness" observation as a design hook for UMUSE: a non-binary monitor signal from a certificate checker.

**Novelty labels.** No change. The VCVio bridge could be described as "first operational probabilistic model of a
control protocol in a proof assistant that I could find", with the search limits above stated.

### 2.3 "Legitimacy" (Adam Benenson)

**Citation.** https://github.com/abenenson/legitimacy (HEAD `0a1b2b1`, 2026-09-17; Apache-2.0 OR MIT; Lean + Rust).
Title: "Legitimacy: Checkable Rules for AI Agents"; GitHub description "Machine-checked governance for AI agents:
legitimacy kernels, impossibility theorems, and capability-scaling bounds in Lean 4 and Rust". Found at the first
search; **I can confirm this is the repo you described.**

**What it builds.** [R]
- A framework of "governance graphs", a nine-check structural audit (consistency, solidarity, monotonicity,
  strategyproofness, certifiability, observability, corrigibility, compositional safety, non-vacuity), an
  impossibility theorem for scarce-resource allocation rules, a "consistency vulnerability" cv / critical-capability
  C* = tolerance/cv result, and an executable Rust composition experiment ("approved separately, unsafe together":
  a guard that remembers what reached the public output).
- Size and trust base: 269 Lean files; 848 grep hits for `native_decide` under `lean/`. The axiom footprint script
  allows `{propext, Classical.choice, Quot.sound, Lean.ofReduceBool}`; `FRAMEWORK-LIMITS.md` states this.
  By our gate's "standard axioms only" rule, the `native_decide` theorems would not pass.

**The five AI-control protocols.** [R]
- `lean/Legitimacy/Audits/AIControl.lean` hand-models Upfront Auditing, Trusted Monitoring, TM + Defer-to-Trusted,
  Untrusted Monitoring and Trusted Editing as `AuditGovernanceGraph` literals. The UM fixture
  (`audits/ai-control/untrusted-monitoring-graph.json`, `aiControlUntrustedMonitoringGovernanceGraph`) has four binary
  nodes:
  - `monitor_validation` (a threshold gate on a field `monitor_validation_failure` with min 1.0);
  - `untrusted_policy` (U writes code, no gates);
  - `redacted_untrusted_monitor`;
  - `human_audit`;

  and one edge. The only quantities are thresholded fields (e.g. `combined_untrusted_suspicion`) in rational arithmetic.
- The theorems (`aiControl_protocol_untrustedMonitoring_legitimate`, etc.) are `native_decide` equalities that the
  nine-check audit returns the tag `AuditVerdict.legitimate`. The paper itself says this tag is "not a substantive
  legitimacy property of the AI Control protocol". The bridge theorem
  `ai_control_fixture_graphs_receive_legitimate_verdict` ranges over the same five-element enum.
- Stated limits (`papers/05-structural-audits.md` §7): deterministic substrate only; **defer-to-resample has no extracted graph**
  (theorem `defer_to_resample_has_no_current_extracted_graph`, which the paper calls a bookkeeping witness, "not a
  non-trivial unrepresentability proof"); no composition; "this is
  not a verified parser from the source papers' protocol text ... no theorem here proving full faithfulness"; the
  fixture says nothing about the empirical safety case. The text-to-fixture mapping is a trusted modelling step.
- The fixtures encode no honeypot count, no slack, no collusion or Schelling-signal behaviour and no probability.
  Their "monitor validation" is a Boolean field.
- `Behavioral/AIControlLineage.lean` (skimmed names only) adds a five-role graph with a "trusted-monitor capacity"
  subcritical/critical-capability statement in the same spectral framework; it says it "does not prove [the] empirical
  control-evaluation results".

**Overlap.** UM* CIDs: **disjoint.** The same word ("untrusted monitoring") names an unrelated object. The five
protocols are structural typed-graph fixtures; our theorems are probabilistic worst-case bounds. CANONF1,
SANDBOXF1/2F1, VCVio bridge: **disjoint.** Composition (STACK "min, not product"): **adjacent.** Their stateful guard
experiment is a deterministic cousin of "stateful monitors / composition" that we list as out of model.

**Cite / reuse.**
- Cite **as a disclaimer**: "AI-control protocols have been represented in Lean as typed governance-graph fixtures
  (Benenson 2026); those results are deterministic structural audits and give no safety bound." This pre-empts the
  claim "protocols are already formalised in Lean".
- Reuse: nothing mathematical. The claim-ledger format (status / scope / Lean evidence / reviewer note per claim) is
  similar to ours. The axiom-footprint script is a model for gating `native_decide`.

**Novelty labels.** No change. Do **not** claim "first Lean formalisation of AI control protocols". The defensible
claim is about probabilistic worst-case bounds for UM with honeypots.

### 2.4 SOUNDGATE / "Stop Means Stop" (Sajjad Khan)

**Citation.** S. Khan, "Stop Means Stop: Measuring and Repairing the Enforcement Gap in Agent-Framework Control
Primitives", arXiv:2607.14166 (cs.SE), submitted 15 Jul 2026, v3 8 Aug 2026,
https://arxiv.org/abs/2607.14166. Artifact: https://github.com/sajjadanwar0/soundgate-paper (MIT; HEAD `bf79b29`,
2026-10-02; the paper says "public upon acceptance" but it is public now); `pip install soundgate` (PyPI 0.1.3).

**What it builds.** [R]
- **Measurement (primary contribution).** On six frameworks, "barrier semantics" of approval gates / cancellation /
  timeouts fail. Five of six leak a sibling effect during an approval pause. Also replay double-execution,
  cancellation orphans, timeout zombies. Frontier models emit the leak-triggering plan shape at up to 14%; driving
  unmodified frameworks, 215 of 1,200 live runs leaked.
- **Repair.** SOUNDGATE, a Rust external gate, line-delimited protocol; every side effect must be *admitted* before it
  touches the world. State: `released`, `rejected`, `pending`, `cancelled`, `closed` sets keyed by (run, key). Four
  properties:
  - P1 hold-until-decided;
  - P2 reject-cancels (sticky);
  - P3 dedup-on-replay (per identity);
  - P4 fence-on-cancel.

  Proved invariants: I1 released/rejected disjoint, I2 pending undecided, I3 fence compaction.
- **Complete mediation** is an explicit *assumption* ("reference-monitor contract"), discharged operationally by
  placement discipline, a linter, a loopback network namespace, a cgroup eBPF route, a seccomp deny-by-default
  profile and Landlock write allow-listing (Table 6). Network-complete, environment-complete only under the placement
  contract.

**What is machine-checked** (all over a *model* of the admission core). [R]
- Verus: 11 items verified (`formal/verus.txt`, "11 verified, 0 errors"; 250-line `gate_model.rs`).
- TLA+/TLC exhaustive: 729 / 804,357 / 74,805,201 states (2x2, 3x3, 4x3 runs x keys). I read the tail of the 4x3
  receipt (complete search, depth 17).
- TLAPS: 68/68 obligations, unbounded runs and keys.
- Loom on the deployed Rust at bounded interleavings.
- Model-to-code: differential conformance over 1.2x10^7 operations and an exhaustive 729-state / 14,580-transition
  check. The paper says plainly this is "refinement evidence, not a mechanized refinement proof" and "not Lean".
- Liveness is explicitly not part of the contract (a held effect can starve; fail-closed).

**Out of scope** (stated by the paper). Probabilistic reasoning of any kind; whether the *approver's* decision is good;
the approver's integrity; covert channels; privilege-escalating tools; effects that bypass mediation; rollback.
The only AI-control content is one sentence in §7: control protocols that "review actions before they land ...
presuppose ... a mechanism that actually withholds the action pending review -- the admission layer the gate
supplies and the frameworks, as measured, do not".

**Overlap with our results.**
- UM* CIDs (UMHSF1, UMSURVF1, UMPROTF1, UMSTRATF1, UMNOGOF1, UMLOWERF1): **disjoint at the theorem level**
  (deterministic admission state machine vs probabilistic test bounds). **Complementary at the assumption level:**
  - A4 (the honeypot test completes before any deployment output executes) and "decide before execute" are the sibling
    leak, measured and then fixed under P1.
  - A5 ("flags are audited while u < b"; flagged item withheld pending the audit) is hold-until-decided.
  - A11 (a caught attack is absorbing shutdown; no further deployment) is P4 fence-on-cancel *if* the protocol driver
    issues `CANCEL(run)` on a confirmed attack. [I]
  - DESIGN's "A1-A4 are scaffold engineering, not proved" gets an empirical datapoint: 5 of 6 production frameworks
    fail the barrier contract as shipped. Cite this when arguing that A4/A11 are not free.
- Variant D (defer without incrimination) [I]: P3 is per-identity. The paper states that "a fresh key per attempt makes
  P3 vacuous". A colluding generator that submits a *new* attack after a deferral gets a new identity, so SOUNDGATE
  gives no retry bound. The UMDEFER lesson (flags must lead to incrimination or halt) is not covered by the gate; it
  needs run-level cancellation driven by the protocol.
- SANDBOXF1/2F1: **adjacent.** Both are about enforcing a mediation boundary at the OS level. SOUNDGATE uses seccomp,
  Landlock and eBPF; ours models bubblewrap mount tables. SOUNDGATE's Landlock demo runs a **positive-control
  self-test** (grant nothing, confirm the write is denied) so a non-enforcing kernel cannot report a false pass.
  That is precisely the step that turns a mount-table model theorem like SANDBOXF1 into a system claim.
- Coverage / B-bar: SOUNDGATE supplies *mediation* (every effect is admitted), **not** *classification* (which
  effects are bad). It does not supply a structural B-bar for A9. Only half of "the action layer should supply B-bar
  structurally". [I]

**Cite / reuse.**
- Cite for A4/A11 engineering plausibility and as the nearest verified "admission layer".
- Reuse `formal/verus/gate_model.rs` and `formal/tla/SoundGate.tla` (MIT) as a ready specification of a five-set state
  machine plus invariants I1-I3 to port to Lean (see direction 2 below).
- Reuse the canary-write self-test pattern for any system claim built on SANDBOX2F1.

**Novelty labels.** No change to any CID. STACK's assumption table could add a pointer: "A4/A5/A11: discharge by an
admission gate (cf. SOUNDGATE P1/P4) under complete mediation".

### 2.5 Games for AI Control (Griffin, Thomson, Shlegeris, Abate)

**Citation.** C. Griffin, L. Thomson, B. Shlegeris, A. Abate, "Games for AI Control: Models of Safety Evaluations of
AI Deployment Protocols", arXiv:2409.07985 (v1 12 Sep 2024; v2 7 May 2026; IASEAI'26, AAAI OJS 43025),
https://arxiv.org/abs/2409.07985. Author post: https://www.lesswrong.com/posts/Yu8jADLfptjPsR58E/games-for-ai-control-1
(in the "AI Control" LessWrong sequence; updated for the arXiv version). No code repository found (searches and PDF text).

**What it proves / builds.** [R]
- **Definition 3.1, AI-Control Game.** A two-player, two-objective, partially observable, finite-horizon stochastic
  game. Blue (protocol designer) has history-dependent behavioural policies. **Red is memoryless** (acts on its last
  observation; in TM Red gets only a null observation, so it cannot condition on time or the audit counter). Honest
  vs attack mode. Leader-follower (Blue commits first, Red best-responds), a multi-objective Stackelberg notion.
- Props 3.2/3.3/3.5: continuity, attainment of Red's minimum, existence of an "AI-Control Equilibrium".
- Lemma 5.1, Lemma 5.2, Thm 5.3: an equilibrium is a maximin point of a weighted-sum zero-sum POSG.
- Prop 5.4: a counterexample to equivalence of Red's behavioural and mixed policies, so a minimax theorem does not hold
  straightforwardly.
- Prop 5.5: an adapted double-oracle algorithm returns an epsilon-equilibrium.
- **Trusted Monitoring only.** State `(m, c, b)` (problems left, audit coins, backdoored?) plus an absorbing
  "caught/safety mode" state `s_T` and an absorbing "unacceptable" state `s_bot`. Actions Audit / Defer / Run.
  Memoryless threshold protocols have safety given by an O(MC) recursion (Prop 4.1, App. C.1); Red's best response is
  the minimiser over the backdoor rate beta of a degree-M polynomial. Human auditor false-negative/-positive rates are
  allowed (App. B, Fig. 3).
- **Empirics from fitted laws.** Beta(7.39, 6.86) vs Beta(8.91, 2.82) for "original" safe vs backdoored suspicion
  scores; a "weak" monitor Beta(7.51, 4.22). Results: raising the audit FPR above 2% Pareto-improves Greenblatt's
  protocols (3% small gain in the original case, 5% large in the weak case); a first approximate Pareto frontier for
  mixtures of fixed-FPR protocols; Greenblatt's closest policy is 0.0042 from the frontier (original) and >= 0.0200
  (weak); mixed policies make up most of the weak frontier.

**Machine-checked?** **No.** Proofs are on paper in the appendices; results are numerical (grid and ternary search,
double oracle). My grep over the PDF text for Lean / Coq / Isabelle / "machine-check" / "verified" found nothing.

**Untrusted monitoring and honeypots.** **Absent.** The Games author's post lists "Modelling other protocols, such as
untrusted monitoring ... allows us to model new important interactions, such as collusion/steganography" under future
work. "Upfront auditing" appears only as a TM special case (audit the first 2%). The same post concedes: the game "has
to be redesigned each time a new protocol is modelled". The LASR UM paper (2602.20628) is by an overlapping group
(Abate, Griffin) and uses GAC's double-oracle solver (§2.7), so UM modelling in that line is statistical and not
machine-checked.

**Overlap with our results.**

| ours | vs GAC | one-line justification |
|---|---|---|
| UMHSF1, UMSURVF1, UMSTRATF1, UMNOGOF1, UMLOWERF1 | disjoint | no honeypots, slack, mediators, collusion, decoders or class counts in GAC |
| UMPROTF1 | adjacent | same genre: finite-horizon safety recursion with budget and an absorbing catch; different protocol (UM + upfront test, ∀ history-dependent generators, stateless monitor with shared seed) vs TM + memoryless iid-rate Red |
| N1/N1b (audit-game structure, saddle point, dual certificate) | **overlaps** (judged from STACK.md only) | TM audit game with Stackelberg structure and numerically solved equilibria is GAC's object; ours is Lean-checked structure/duality |
| UMUSE (in progress) | **overlaps** | the safety/usefulness Pareto framing and leader-follower inf-sup are GAC's (already conceded in the critique disposition) |
| UMDEFER (in progress) | overlaps in setting | GAC's Defer is a non-absorbing Blue action; nothing in GAC distinguishes defer with vs without incrimination because Red is memoryless and has no retry learning. The honeypot-gated retry amplification is UM-specific |
| VCVio protocol refinement | adjacent | GAC's POSG semantics is a paper formalism; ours would be an executable ProbComp semantics inside a proof assistant |
| r (constant audit recall) | same modelling choice | GAC's human FNR is a constant (`p_FNR`), matching our constant-r recursion |
| A11 absorbing shutdown | same modelling choice | GAC's caught state `s_T` "ends the opportunity for future backdoors" |

**Adversary class difference** [I]. GAC's Red is time-blind and memoryless, which keeps the problem tractable and is
weaker than ours on the generator side (we quantify over every history-dependent generator). Where GAC's Red is
stronger is in the *joint optimisation of an attack rate against a budget-dependent Blue policy*, which our one-shot
reduction sidesteps for the UM test.

**Cite / reuse.**
- Cite GAC as the formal-game prior art for TM (Pareto frontier, Stackelberg, audit coins), and in UMUSE/UMDEFER as the
  framework we instantiate.
- Reuse Prop 4.1 / App. C.1 recursion (explicit lambda coefficients) and Definition 3.1, and the Beta fixtures, as a test
  target (direction 1 below).

**Novelty labels.** UMUSE: label "instance of GAC's framework; value is a closed-form frontier for the hard-slack UM
family and Lean-checking". N1/N1b: "machine-checked rendition of the TM audit game" if any novelty text exists.

### 2.6 Molnar, Reliability Theory for AI Control

**Citation.** G. Molnar, "Reliability Theory for AI Control", arXiv:2609.26419, 22 Sep 2026,
https://arxiv.org/abs/2609.26419.

**What it does.** [R] Applies classical reliability theory (coherent systems, minimal paths and cuts, Birnbaum
importance, common-cause failure domains) to Reviewer C family DeepMind's AI-control roadmap against rogue deployment (the
route-level model `phi = A or (M and R) or (V and T and Q)`, cited as GDM AI Control Roadmap arXiv:2607.13087). The
headline: the same stack can have cubic, quadratic or linear rare-failure suppression depending on shared failure
domains. A LinuxArena example shows a monitor can fire 36/51 times and still be pivotal in only 2/51 to 8/51
trajectories. Recovery is separated from prevention (`P(L_tau) = P(E)(1 - P(H_tau | E))`). It says "the mathematics
below is deliberately standard". Not machine-checked (grep: no Lean/Coq/Isabelle, no theorem environment). It does not
discuss untrusted monitoring, honeypots or collusion, though it cites a frontier-lab report of "chain-of-thought monitor recall
conditional on successful honeypot attacks" as a precedent for conditioning on the relevant subset.

**Overlap.** UM* CIDs: **disjoint.** STACK's composition remark ("composition with trusted monitoring: a min, not a
product, absent conditional independence"): **adjacent.** Molnar gives the standard vocabulary (structure function,
minimal cuts, exponent determined by the smallest cut) and the "pivotal" notion, which says the useful contribution of
a monitor is the event "needed and catches". The latter is a cleaner framing of our caveat that "bounds measure the
adversarial gain over the always-flag baseline". [I]

**Cite / reuse.** Cite for the composition caveat and for the common-cause point (shared weights between UM and U is
a failure-domain statement). Reuse the pivotality definition when stating UMUSE's honest-monitor contribution.
**Novelty labels:** no change.

### 2.7 Other work found while searching (2025-2026)

| Work | What it is | Machine-checked? | Relevance |
|---|---|---|---|
| Gardner-Challis, Bostock, Kozhevnikov, Sinclaire, Velja, Abate, Griffin, "When can we trust untrusted monitoring? A safety case sketch across collusion strategies", arXiv:2602.20628 (v2 21 Sep 2026) | statistical model; honeypot slack n_s is a parameter justified by a *retraining* assumption; App. E: answering it "would require a learning theory we do not yet possess"; uses GAC's double oracle (its App. B.1) | no (no Lean/Coq/Isabelle hit in text) | the closest *object* to UMPROTF1/UMSURVF1; our existing audit already says UMPROTF1 is "motivated by", not a formalisation of Eq. (1). Same group as GAC. Adjacent |
| Roger and Shlegeris, "Toy models of AI control for concentrated catastrophe prevention" (LessWrong, https://www.lesswrong.com/posts/MDeGts4Aw9DktCkXw) | analytic toy games with code: catch-then-shutdown, "audit at least a few examples from the category of data on which AIs plan to escape", coordinated escape via a shared random feature; assumes a stateless AI and Blue-first Stackelberg | no | **closest informal anticipation of UMSTRATF1/UMNOGOF1's heuristic** (budget per class). No honeypot-test slack, no decodable mediator, no converse for all designs. [R: head and the "coordinated escape" section] |
| David, Guarnieri, Gervais, "Alignment Contracts for Agentic Security Systems", arXiv:2605.00081 | contracts over observable effect traces; finite-trace semantics, refinement and one-way composition rules, decidable admissibility, "enforcement soundness for monitor-realized traces" under an Effect Observability Assumption (all effects mediated) | **yes**: a Lean 4 artifact for the formal core | **the closest Lean-checked "action layer"**: same complete-mediation assumption as SOUNDGATE, deterministic, covert channels out of scope. I did not find the artifact's public repo. [R: abstract, intro, Lean appendix; S otherwise] |
| Najmul Hasan, "Honeypot Protocol", arXiv:2604.13301 | tests whether a model behaves differently across system prompts (context-dependent behaviour); empirical, 8 pages | no | **name collision** with our upfront monitor-validation honeypots |
| Nguyen et al., TraceGuard, arXiv:2604.03968 | empirical collusion-resistant structured monitoring on BashArena | no | empirical UM-adjacent only. [S] |
| Doll and Shames, "Foundations of Machine-Checked Control Theory in Lean", arXiv:2607.19727 | classical control theory (Lyapunov, small gain) in Lean | yes | **name collision** ("control"), unrelated to AI control |

No source I found machine-checks a probabilistic UM bound (see the limits in section 0).

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
| SANDBOXF1 / SANDBOX2F1 | no change; cite SOUNDGATE and Alignment Contracts as neighbouring effect-layer work; adopt SOUNDGATE's canary self-test idea | different object (pathname resolution of one sandbox policy) |
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
  ledger's campaign reports.
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

## 5. Source list (all URLs fetched or cloned this session)

- Formal Confinement: https://github.com/for-all-dev/formal-confinement ;
  https://www.lesswrong.com/posts/yZvrRWM5DE58CzHpZ/formal-confinement-prototype
- PCC sequence: https://www.alignmentforum.org/s/f9ewpmtz8AogLxvqx ;
  https://www.lesswrong.com/posts/CCT7Qc8rSeRs7r5GL ; https://www.lesswrong.com/posts/SG82BkTDQDAjANRWj ;
  https://github.com/for-all-dev/aisec-via-fm
- Legitimacy: https://github.com/abenenson/legitimacy
- SOUNDGATE: https://arxiv.org/abs/2607.14166 ; https://github.com/sajjadanwar0/soundgate-paper ;
  https://pypi.org/project/soundgate/
- Games for AI Control: https://arxiv.org/abs/2409.07985 ;
  https://www.lesswrong.com/posts/Yu8jADLfptjPsR58E/games-for-ai-control-1
- Molnar: https://arxiv.org/abs/2609.26419
- LASR: https://arxiv.org/abs/2602.20628
- Toy models: https://www.lesswrong.com/posts/MDeGts4Aw9DktCkXw
- Alignment Contracts: https://arxiv.org/abs/2605.00081 ; Honeypot Protocol: https://arxiv.org/abs/2604.13301 ;
  TraceGuard: https://arxiv.org/abs/2604.03968 ; Doll-Shames: https://arxiv.org/abs/2607.19727
