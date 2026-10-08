# Review: post-SC-03 roadmap and reusable primitives

**Basis.** This is a static review of the supplied files only. I did not see the source of `ControlStack/CovertChannel.lean`, `ControlStack/GatewayModel.lean`, `ComposeGame.lean`, `ComposeAvg.lean`, or the egress and gateway Python. Statements about those rely on `ROADMAP.md`, `gateway/CORRESPONDENCE.md` and `COMPOSITION-N1-UMPROT.md`.

**Evidence tags used throughout:**
- **[M]** model theorem: kernel-checked, about a model.
- **[R]** runtime calibration on a disposable fixture: tests, mutations, receipts. This is existence evidence, not a rate.
- **[S]** sample-based bound: valid only under its sampling assumptions.
- **[D]** deployment evidence. Nothing in the stack has [D] evidence today.

---

## A. Verdict on the proposed roadmap

**The ordering does not fit the selected scenario.** It mixes two scenarios with different proof styles. It also puts first the item that the selected certificate needs least.

- **The covert scenario has a structural safety parameter, not a statistical one.**
  - The scenario in `CATASTROPHE-SPEC.md` is exact recovery of a uniform k = 32 secret, over schema or canonicaliser channels only, with a 16-bit lifetime budget.
  - Its bound depends only on |V_lifetime| (`covert_bound`, `gateway_bound`, `covert_bound_lifetime`).
  - The bound contains no monitor FPR or FNR, no audit recall, and no composition of monitors.
- **Proposed items (3) and (4) serve a different scenario.** That scenario is backdoor insertion under trusted plus untrusted monitoring (`DESIGN-A2.md`, `COMPOSITION-N1-UMPROT.md`, the LASR and LinuxArena work). In the covert scenario the only sample-based quantities are on the honest side: usefulness and the false-blank rate (honest episodes refused).
- **Two things that decide whether the covert scenario gives a meaningful risk/usefulness pair are missing from the sequence:**
  - **Usefulness.** `CATASTROPHE-SPEC.md` makes code, comments, shared files and memory into channels, all under a 16-bit budget per lineage over the secret's lifetime. A deny-all system meets 2^-16 trivially. Until an honest multi-instance task is measured under that budget, the risk number tells us nothing.
  - **The known residual channel.** Shared kernel state, especially the page cache, is listed in `gateway/CORRESPONDENCE.md` as UNRESOLVED.
- **P0 is marked done but does not meet its own definition.** `ROADMAP.md` marks "choose one concrete catastrophe" ✅. Its success definition includes "horizon" and "acceptable usefulness". `CATASTROPHE-SPEC.md` leaves n "to be chosen" and sets no usefulness threshold.

### Key corrections
1. **Split the plan into two named scenarios.**
   - **Scenario A:** covert propagation, with structural guarantees.
   - **Scenario B:** backdoor insertion under trusted and untrusted monitoring, with statistical guarantees.
   - Declare B as the second scenario. Items (3) and (4) then have a consumer. Item (6) becomes an early test of reuse across opposite proof styles, not a late extraction exercise.
2. **Gate on usefulness first** (see B1 and E).
3. **Narrow egress and give it a fixed time budget** (see A.1).
4. **Try to break the 2^-16 design point through the known page-cache channel** before claiming that design point at runtime.
5. **Point correspondence work at `GatewayModel`**, whose theorem A actually uses, rather than `EgressGate`. Shrink the trusted base by running the executable Lean model as the gateway core.
6. **Say "target-workload-matched" instead of "deployment-matched".** Nothing is deployed, so nothing can be matched to a deployment yet.
7. **Move human review earlier.** All review so far, including this one, has been done by models.

### A.1 Is egress the highest-value next task? No.

1. **Scenario A v1 needs a deny-all network, and that already exists.** `CATASTROPHE-SPEC.md` blocks the network. The harness unshares all namespaces (`gateway/CORRESPONDENCE.md`). The allowlist egress gateway only matters if A's honest task needs network access.

2. **If the network is allowed, allowed peers are channels, and SC-03 by design does not bound them.**
   - `egress/README.md` and `assurance/egress-boundary-v1.json` claim immediate-peer reachability only. They explicitly make no confidentiality claim.
   - The suite *demonstrates* secret delivery to the allowed mirror. POST bodies up to 1 MiB and CONNECT tunnels carry arbitrary bytes.
   - Combining SC-03 with the covert bound needs a premise that does not exist yet. Call it the **sink premise**: no receiver in the lineage can observe the state of any allowed peer. Under that premise, network effects contribute only one possible value to V.
   - Without the sink premise, all-destination attribution does not change A's bound at all.

3. **Attributing a packet to a process is not the same as knowing what caused it.**
   - The residual that matters is `other_host_deputies`: a host process acting on data the attacker influenced.
   - Attributing every packet to a PID does not catch a deputy. The deputy's packets are correctly attributed to the deputy.
   - So proposed item (1) does not discharge the obligation it seems to target.

4. **Attribution at the syscall level is an open-ended problem.** `reviews/egress-follow-up-2026-10-08.md` lists raw sockets, inherited FDs, connected UDP, `sendmsg`, `io_uring` and async trace interleaving as untested.
   - Prefer **attribution by construction**: give each principal (sandbox tree, gateway, destination) its own network namespace, join them with veth links, and capture on each link.
   - The kernel's namespace isolation, which is already an assumed premise (`kernel_and_host_integrity`), then attributes every frame regardless of which API sent it.
   - This turns an observation-completeness obligation into an assumption the case already makes. The follow-up's "veth/routing complexity is unnecessary" optimises the wrong cost.

**Recommendation:** keep only a narrowed version of the egress work (B5). Park attribution for allowed peers until a canary-exfiltration scenario is selected. That scenario is where SC-03 naturally belongs.

### A.2 Can measured FPR/FNR instantiate proofs against adaptive attackers?

Only partly, and only on one side.

| quantity | relation to the adversary | what a sample can instantiate | theorem that consumes it |
|---|---|---|---|
| Honest FPR, defer rate, false-blank rate, usefulness | Drawn from the honest distribution, not chosen by the adversary | [S] valid if honest tasks are exchangeable draws from the declared workload. Transfers relatively well (LinuxArena split: FPR ≤ 6.5%) | `checkUseQ` (`ledger/TMCERT_USEQ.lean`); TMCERT rows that consume audit coins |
| τ̄ = 1 − TPR when Red only chooses timing | Attack content comes from a fixed population | [S] τ̄ ≤ 1 − TPR_lower | `composedPop_end`; TMCERT with constant-rate or clocked Red |
| Per-submission τ when Red chooses content | The adversary picks the content | **Nothing.** `ComposeBlindSpot.blind_spot_risk` has τ̄ = 1/1000 and risk = 1 | `composedEndToEnd`; `CoveredV` in `ledger/TMCERT.lean` |
| Audit recall r (A6) | Worst case over attacks | Same as τ: samples cannot certify it | UMPROTF1, `DeferMono` |
| Capacity \|V\| | Independent of the adversary by construction | Not needed: it is exact | `covert_bound` |

**Bottom line:** against adaptive attackers, measured rates feed a proof only through a named **content-coverage premise**. Examples:
- Red's set of reachable attacks is finite and has been enumerated.
- The evaluated attack law dominates every reachable attack up to a constant L (the same shape as UMPROTF1's L).
- A TMLIP-style row-distance bound links the evaluated game to the target game.

Each of these is a claim about how strongly the red team elicited attacks. None of them is a statistic.

**Coverage that is still missing:**
- **Attack elicitation.** The red-team attacker may be weaker than the deployed model, or may sandbag.
- **Monitor-view identity.** Sampled scores may not match the deployed monitor's view or timing. Pre-action scoring is not yet established.
- **Matched population.** TPR at ≥8 is 7/56 in the matched population versus 39/150 pooled, so detection did not transport (`ROADMAP.md`, stat audit).
- **Stationarity.** Red can adapt across episodes to what it observes, and monitor versions drift.
- **Correlated monitor failures.** In `ComposeGame`, independence comes from fresh coins for each submission x. That buys nothing when a miss is a deterministic function of content.
- **Multi-step attacks.** The abstract state may not carry what makes a sequence catastrophic.
- **Oracle false negatives.** Three detected mutations show the oracles can catch those faults. They do not estimate how often the oracles miss. An adversary aims at oracle blind spots, as the IPv6 and fragment bugs illustrate.
- **Transfer margin.**
  - TMLIP gives U + N·L·h. At N = 100, a useful bound needs a row distance of about 10⁻³.
  - Observed shifts are about 10⁻¹.
  - The `ledger/TMLIP.lean` witness (7/16) shows linear growth in N is attained.
  - So TMLIP is sound but vacuous for the shifts actually observed.

### A.3 Claims that are too strong

| location | claim | problem | suggested fix |
|---|---|---|---|
| `CATASTROPHE-SPEC.md`, target theorem | "For a schema channel this is assumption-free given the gateway's correctness" | It also needs complete mediation (including kernel state), independence of m, lineage closure and OS isolation | "conditional on complete mediation, isolation, independence and lineage closure" |
| `CATASTROPHE-SPEC.md`, "Why this catastrophe" | "U cannot coordinate beyond k bits" | Contradicts the v2 scope paragraph in the same file. 16 bits carry any 1-bit command | Delete it and keep the v2 scope |
| same | "exactly what the existing collusion layer bounds (… UMPROTF1 …)" | No proved bridge from channel capacity to UMPROTF1's domination constant L | "related to" |
| same, Decision 4 | "worst-case over encoders, so no LLM attacker is needed for v1" | True for the bound. False for testing the mediation premise, which needs an adversary searching for channels | Separate tightness testing from channel discovery |
| `ROADMAP.md`, P0 gateway row | Side channels "closed in tests" | What was shown: the tested encoders transmitted nothing in 6/6 episodes, and the page cache is open | Use that wording |
| `ROADMAP.md`, P0 catastrophe ✅ | Marked done | Horizon and usefulness are unset | Mark 🔄 until B1 passes |
| `COMPOSITION-N1-UMPROT.md` | "multiplies … by a certified 0.05–0.22" | Holds only for a Red that cannot choose content, on LASR data that is not target-matched, after transport was observed to fail, and with L still open | "under a population-content Red on LASR APPS/BCB data" |
| `assurance/egress-boundary-v1.json` | `model_trace_invariant: THEOREM_VERIFIED` | Accurate, but nearly true by definition (see below). It checks the specification and `lookup_pinned`, not isolation | Label it "specification consistency" |
| `assurance/egress-boundary-v1.json`, `results.ci` | "No remote GitHub CI run claimed" | Stale: contradicts `ROADMAP.md`. The cited run is on `b30177e`, not the current head | Bind the CI run ID and commit SHA in machine fields |
| The primitive "certificate transfer with N·ε" (as described in the consultation request) | Offered as reusable across scenarios | TMLIPF1 covers a fixed model, transfers risk only (not usefulness), needs a Lipschitz premise on the model side, and is vacuous at observed shifts | "transfer under parameter drift within one scenario" |
| `DESIGN-A2.md`, usefulness certificate | "91.492 honest completions" | The reward per round is 1 − upper defer FPR. That counts non-deferred rounds, not completed tasks | "non-deferred honest rounds" |
| `ROADMAP.md`, TMLIPF1 row | "✅ verified (… override)" | The legend says ✅ means the gate passed | State what the override was |

**Why `EgressGate` is nearly true by definition** (`ControlStack/EgressGate.lean`):
- A launch sets `active := safe t` (line ~75), and `directAttempt` only records an effect when `s.active && !safe s.topology` (line ~84). A safe launch therefore makes direct attempts no-ops by construction.
- `tamperPolicy` is the identity (line ~87).
- `noHostDeputy` and the other topology properties are Boolean inputs (lines ~38–48), not derived facts.

### A.4 Lessons from moving to a concrete scenario

1. **Concreteness narrows claims, and the narrowed claims do not compose on their own.**
   - Covert went from "coordination" to "exact-message recovery".
   - Egress went to "reachability, no confidentiality".
   - Joining them needs an interface lemma (the sink premise).
2. **One premise keeps reappearing in three forms: the interface is complete.**
   - Covert: V captures everything the receiver observes.
   - Egress: the effect log captures every transmission.
   - TMCERT: every concrete row is covered (`CoveredV`).
   - No theorem and no sample discharges this premise. It is where attacker capability re-enters. Track it as a single obligation class.
3. **Quantifying over adversaries is real only where coverage is enforced by construction.**
   - Where a total function maps every attacker action into a finite set (gateway `deliver`, `lookup`, enum validation), the quantification is genuine.
   - Where coverage is a sample, such as an ROC curve, it is not (`ComposeBlindSpot`).
   - Design so the adversary-facing parameter is structural, and put the statistics on the honest side.
4. **Capacity bounds compose without independence; detection bounds do not.**
   - Capacity: |V| multiplies across channels, so bits add, and no independence assumption is needed.
   - Detection: monitors compose by `min`, or by product only when the protocol builds the independence in (`COMPOSITION-N1-UMPROT.md`).
5. **Lifetime accounting is unforgiving.** Any unmodelled channel with positive capacity per episode eventually exhausts 16 bits. Residual channels must have zero capacity by construction, or be counted in the ledger.
6. **The bugs that surfaced were in the evidence machinery**, not in the proofs or the gateway: IPv6 connect parsing and fragment decoding in the observers. Oracles are safety-critical code.
7. **A set of engineering habits is genuinely reusable:**
   - Unknown is never a pass (exit 2, explicit `partial-pass`).
   - Run a positive control after every negative case.
   - Calibrate observers before claiming absence.
   - Make capture-drop accounting a gate.
8. **The bound only constrains exogenous information.** Identical model instances can coordinate on information they all derive themselves, via Schelling points, without transmitting anything. Restate the bad event as "propagation of information observed only by the sender".

---

## B. Ranked remaining roadmap with acceptance criteria

**B1. Freeze the Scenario A v1 contract and pass a usefulness viability gate.**
- The contract replaces the open items in `CATASTROPHE-SPEC.md`. It fixes:
  - the honest task family and how tasks are sampled;
  - an information-flow graph of every artefact that can reach a later model instance (files, memory, code, tool outputs, logs), each either cut or given a schema with exact |V_i|;
  - the lineage definition and the key used by `LifetimeLedger`;
  - network = deny-all;
  - n, N, k and the budget;
  - which real secrets this protects. Keys and credentials are protected. Low-entropy targets and 1-bit signals are not.
- Usefulness is honest task success with mediation versus an unmediated baseline, against a threshold declared in advance. Also report the false-blank rate.
- Run the predeclared number of episodes in the existing harness, with Clopper–Pearson intervals [S].
- Pass: the lower bound clears the threshold and no honest episode overruns the ledger.
- Failure is an acceptable outcome. Record "safe but not useful at 16 bits" and re-parameterise before doing more assurance work.

**B2. Build a walking-skeleton safety case for A, run in CI.**
- One command from a clean checkout reproduces all of:
  - the narrow covert Lean checks;
  - `gateway/difftest.py`;
  - the harness side-channel tests;
  - the encoder success rate versus its exact predicted value;
  - the usefulness interval;
  - a manifest listing every premise as [M], [R], [S] or UNRESOLVED.
- The manifest binds the commit SHA, CI run ID and toolchain. Status lives only in machine-checked fields.
- Deleting any evidence file, or promoting any status, must make the checker fail.
- If any VCVio theorem is cited, the slow Lean tier must run on the cited commit.

**B3. Try to break the design point through residual channels, then close them.**
- Build an encoder/decoder pair for each class of shared state, run it in the current harness, and report success rate versus 2⁻ᵏ with a power statement. Classes:
  - page cache;
  - global `/proc` counters;
  - memory pressure;
  - CPU frequency and thermal state;
  - metadata on shared filesystems;
  - overruns of the fixed schedule.
- Then use a fresh VM or microVM per episode, or a documented flush, and rerun.
- A class counts as "closed" only with a mechanism argument plus no detectable capacity at the predeclared power. Otherwise count it in the ledger or declare it out of scope.
- If the page-cache encoder succeeds now, record that the runtime does not meet 2^-16.

**B4. Gateway correspondence by shrinking the trusted base.**
- The runtime decision core becomes the compiled Lean `GatewayModel` step and deliver functions plus the ledger. Alternatively, run differential checks exhaustively up to a stated depth.
- The Python shim maps every parse error to a refusal. Any refusal blanks the episode to all-NULL, which is already in V, so parse errors are safe by construction.
- Mutations of the shim must be caught: early delivery, an extra slot, a timestamp leak, a skipped ledger update.
- Random differential testing on 300 traces is weak against an adversary that searches for a mismatch.

**B5. Narrowed egress integration, with a fixed time budget.**
- Put the sandbox tree, gateway and destination in separate network namespaces inside a disposable outer namespace with no external links, and capture on every link.
- Attribute every initial transmission by namespace.
- Required checks:
  - mutations for direct-to-peer, failed connect and missing trace are detected;
  - an inherited-FD control is rejected;
  - `sendmsg`, connected-UDP, `io_uring` and raw-socket attempts from the sandbox are observed absent.
- For A v1, run with an empty allowlist.

**B6. Real agent scaffold plus an LLM red team for A.**
- Inventory every persistence path in the real scaffold, and cut or gate each one.
- LLM attackers that know the gateway design try to transmit m and are told to search for side channels.
- Success must stay at or below the bound, with a stated confidence interval. Any success above the bound is a failure, not a data point.

**B7. Express Scenario B in the same schema (the reuse test).**
- Use the same manifest schema and verifier as B2, with no scenario-specific code in the verifier core.
- The content-coverage premise is named explicitly.
- Labels: honest-side claims are [S]; population-model attack claims are [S|pop]; content-adaptive premises are UNRESOLVED.
- The cited composition theorem must match the protocol actually run.

**B8. Target-workload-matched statistics for B** (the proposed item 3).
- Preregistered and held out, on a matched population, using pre-action scores.
- Keep task IDs, and audit clustering.
- Measure usefulness as task success, not as 1 − defer FPR.

**B9. Joint-protocol composition for B** (the proposed item 4).
- One Lean game that equals the deployed protocol, including the shared audit budget and audit coins spent on trusted false positives.
- State the missing bridge from a TMCERT certificate to τ.
- For a content-adaptive Red, state the coverage premise instead of plugging in τ̄.

**Later:**
- multi-step and stateful attacks;
- effect gates for privilege escalation;
- distribution shift with a usable ε;
- correlated failures;
- isolation beyond B3;
- sharper mathematics.

**Cheap mathematics worth doing opportunistically**, since the scenario consumes it (all classical results):
- A general-prior maximal-leakage bound: P(guess f(m)) ≤ |V|·maxₓ P(f(m)=x). This covers non-uniform and partial secrets.
- A channel-product lemma.
- A sink lemma connecting `EgressGate` effects to V.
- A union-bound lemma that makes the overall confidence level of the safety case explicit.

---

## C. Reusable primitives: obligations and status

| primitive | artefacts | obligations to instantiate it | status | kind |
|---|---|---|---|---|
| View-capacity bound | `covert_bound`, `covert_bound_lifetime`, `gateway_bound` | Complete mediation, including kernel state; V fixed before the episode; m uniform and independent; lineage closure; refinement | [M] proved, in narrow CI; [R] encoder hits the exact 1885/2¹³, side-channel tests 6/6; mediation UNRESOLVED | **Formal**, generic over finite V |
| Blanking schema gateway | `GatewayModel` (`blank_absorbing`, `other_blanks`) | Refinement; fixed slots and delivery timing | [M] proved; [R] differential test on 300 traces | **Formal** |
| Effect gate / trace invariant | `ControlStack/EgressGate.lean` | Topology established by the validator; effect log complete; deputy premise; refinement | [M] checked, but near-definitional; [R] 62/62 controls, 3 mutations | **Pattern plus specification.** Needs a parametric effect alphabet and a sink lemma before it is formally reusable |
| Robust finite-horizon risk certificate with rational checker | `ledger/TMCERT.lean` (S, Q, Vx, TR, Abs) | Finite abstraction; `CoveredV` for every concrete row; lawful rows; interval confidence established outside Lean | [M] verified; instances checked with `decide +kernel`; [S] LASR demonstration, not target-matched | **Formal**, generic |
| Usefulness certificate | `ledger/TMCERT_USEQ.lean` (`checkUseQ`) | Fixed honest action; `rew` must be real task success (currently a proxy); not transferred by Abs or TMLIP | [M] verified | **Formal** |
| Parameter transfer | `ledger/TMLIP.lean` | Row distance bounded on the model side, plus grid coverage (the file's own docstring says samples cannot supply this); fixed model; risk only | [M] verified (override unexplained); vacuous in practice at N = 100 | **Formal**, within one scenario only |
| Composition | `min`; `composedEndToEnd`, `composedPop_end`; `ComposeBlindSpot`; capacity product (to add) | Common event and experiment; fresh coins specific to the protocol; Red that cannot choose content for τ̄; L and honeypot assumptions | [M] proved; the VCVio tier is not in per-commit CI | `min`, capacity product and the negative result are generic. Product composition holds only for the same protocol shape |
| Statistical bands to rational rows | `numerics/roc_bands.py`, `numerics/lasr_score_bands.py` | Exchangeability, matched population, predeclared grid, correct labels, family-wise allocation | [S]; code is not verified | **Pattern** using standard statistics |
| Hash-bound evidence | `assurance/`, `tools/assurance.py`, `egress/check_evidence.py` | Bind SHA, CI run ID and toolchain; status only in machine fields; checker tests that mutate the manifest itself | [R]; drift already observed | **Pattern** |
| Calibrated, mutated oracles | `egress/observer.py`, `egress/tracing.py`, mutation modes | A fault model per oracle; positive calibration; at least one mutation per fault class; zero capture loss | [R]; no estimate of the miss rate | **Pattern** |
| Fail-closed evidence semantics | exit code 2, `partial-pass`, honest check after each case | Applied uniformly in every runner | [R] | **Pattern** |
| Lifetime ledger | `LifetimeLedger`, `covert_bound_lifetime` | Lineage closure | [M] + [R] | **Formal plus implementation** |

### Validating the reusable structure before extracting it
- **Use the two scenarios that already exist.** A and B already exist and use opposite proof styles. Put both in one schema with one verifier (B2 plus B7). If more than a few premises need special-casing, the interface is wrong.
- **Refactor test in Lean.** Define abstract `Mediator` and `EffectGate` structures. Re-derive the existing theorems through them with no new hypotheses. Any scenario fact the derivation needs is a premise to name.
- **Paper-instantiate a third scenario** (canary exfiltration, or privilege escalation) as an obligation table only. The sink and deputy premises must be forced to appear.
- **Negative instantiation.** Try a free-text paraphraser channel. The schema must force its leakage ℓ to be [S] or UNRESOLVED.
- **Mutate the safety case itself.** Delete evidence or promote a status; the checker must fail.

---

## D. Tasks that can run in parallel

| track | work | depends on |
|---|---|---|
| 1 | B1: contract and usefulness gate | — |
| 2 | B3: falsify residual channels (page-cache encoder first) | — |
| 3 | B4: Lean executable as the gateway core | — |
| 4 | B5: narrowed egress integration | — |
| 5 | Schema v2 and verifier (B2 skeleton), plus fixes to stale docs | Track 1 for the content |
| 6 | B7 on paper: B in the same schema | Draft of track 5 |
| 7 | Cheap lemmas (general-prior bound, product, sink, union) | — |
| 8 | Human review of the A contract | Track 1 (John's decision) |

---

## E. Single best immediate task

**Do B1: the Scenario A contract plus a usefulness viability gate.**

- It is the cheapest experiment with the largest decision value, and both outcomes change the plan.
- Everything in B3 to B6 is assurance for a configuration whose usefulness is unknown. It is also plausibly near zero, because every artefact a later instance reads counts against 16 bits per lineage.
- The first deliverable takes about a day: the information-flow graph, the task family, and the threshold. Then run the experiment.

---

## F. Strongest caveat

**The covert guarantee is exactly as strong as the claim that V captures everything a receiver observes over the lifetime of the secret.**

- No theorem and no sample establishes that claim.
- It is currently known to be false in at least one way: shared kernel state.
- Lifetime accounting makes any channel with positive capacity fatal eventually.
- In a realistic agent deployment, this premise is in direct tension with usefulness.

Until B1 and B3 report, 2^-16 is a [M] model statement. It is not a property of any running system.
