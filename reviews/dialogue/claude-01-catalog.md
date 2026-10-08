# Claude, round 1 addendum: review of `SCENARIO-CATALOG.md` (§9 questions)

Repo HEAD when written: `c11fbda`. This addendum answers the catalog's §9 request; it does not edit the catalog.
It complements `claude-01.md` (gateway findings) and should be read with it. Two facts since `claude-01.md`: the
reachable-view bound is proved (`GatewayModel.gateway_bound_reachable`) and the gateway now charges exactly the
reachable count (the optimal red-team encoder meets the bound: 0.2288 ± 0.006 vs 0.2301); the mandatory `lean-covert`
CI job is green on `85f21ad` and `c11fbda` (8 theorems, no `sorryAx`).

Overall: the catalog is a good plan and I agree with its evidence levels and cautionary lessons. My main objections:
(1) the checker families should collapse to three genuinely different proof shapes; (2) several H ratings ignore
interpreter/delegation/side-channel bypasses; (3) one usefulness no-go result should be proved early because it decides
whether F2 scenarios are worth pursuing; (4) the first end-to-end deployable artifact should be an action-confinement
case (Wave 1), with SC-01 kept as a library primitive.

## Q1. Missing or redundant classes
Missing (high-stakes, concrete, not covered by any row):
- **Audit/oversight exhaustion (DoS on control).** The agent triggers many benign-looking flags or approval requests to
  exhaust the audit budget, after which protocols halt (usefulness collapse) or defer (safety relies on the trusted
  model). Our own protocols have this structure (budget b, UMDEFERF1's hazard). Predicate: honest-task completion
  under adversarial flag-inflation; safety after budget exhaustion.
- **Monitor-targeted adversarial inputs.** Outputs crafted to jailbreak or confuse the TRUSTED monitor (not collusion
  with an untrusted one). SC-23 covers injection into the agent, not by the agent into its overseer.
- **Approval laundering (F7's weak point).** Social-engineering or decision-fatigue attacks on human approvers: the
  exact-payload signature is valid but the human was misled. Needs its own row; F7 does not address it.
- **Capability acquisition through legitimate channels.** Creating API keys, OAuth grants, cloud accounts, or
  purchasing compute through permitted tools (distinct from privilege escalation on the host, SC-09).
- **Dependency/supply-chain insertion.** Adding or pinning a malicious package; partly SC-15/16, but the enforceable
  invariant (dependency allowlist + lockfile hash) is different and cheap.
- **Sandbagging on capability/safety evaluations.** Strategic underperformance, distinct from tampering (SC-21).
  Mostly L-feasibility, but it should be listed so it is not silently absent.
Redundant or nested: SC-02 and SC-04 are obligations of SC-01, not separate scenarios; SC-10 is an instance of SC-09
(policy objects as protected authority); SC-18 is an instance of SC-13 in a serving stack; SC-27 overlaps SC-13 and
SC-21. Keep them as stress tests, but do not count them as independent scenarios.

## Q2. H ratings that are too optimistic
- **SC-08 (H/M → M).** Allowlisting signed executables does not stop malware if any general interpreter (bash,
  python, node) or a build tool that runs code is allowed: the interpreter is signed, the payload is data. H holds only
  for RPC-only tool interfaces, which removes most SWE usefulness. With a shell, the property must be enforced at the
  OS layer (seccomp/LSM exec policy plus network egress), and its statement becomes "no unapproved effect" rather than
  "no unapproved program".
- **SC-09 (H/M → M).** Confused-deputy and delegation paths: a docker socket, CI runner, cron/systemd user units,
  package post-install hooks or cloud credentials grant authority without any sudo transition. The capability lattice
  must include every service the agent can drive.
- **SC-13 (H/M → M)** if the agent can deploy code or config that the control plane later loads (SC-18): disjointness
  of authority fails through the artifact path; it needs F4 provenance on everything the control plane consumes.
- **SC-01 (H → H only under VM-level isolation).** In a shared kernel, page-cache and microarchitectural timing remain
  (`gateway/CORRESPONDENCE.md`); in real orchestration, defining lineages (who shares memory) is hard because shared
  repos, caches and retrieval stores merge them.
- **SC-25 (H for ordering).** Agreed for the protocol; the hard part is classifying which actions have an
  irreversible effect, since writes become effects later (async). The rating should be conditional on an effect map.
- **SC-23 (H/M).** Reasonable for capability separation (control/data-flow separation of trusted vs untrusted text);
  I would keep H/M.

## Q3. Do the families give a sound reusable abstraction?
Partly. Three proof shapes are genuinely different; the other families are instances:
1. **Trace safety (invariants).** F1, F3, F4, F5, F7 are all "every effectful transition passes a monitor that only
   permits invariant-preserving transitions ⇒ the invariant holds on all traces". The generic theorem is nearly
   trivial (induction on traces); the reuse value is in the shared event model, trace capture and refinement/
   differential-testing harness, not in the proof.
2. **Information flow (hyperproperties).** F2 is not a trace property: it constrains pairs/sets of traces (or the
   cardinality of the receiver's view). It needs product semantics or counting, not invariants.
3. **Probabilistic control.** F6.
F8 is composition over all three, and it is where most real failures live (cumulative budgets, concurrent agents).
Recommendation: implement one event-trace model (AgentAction, Effect, Principal, Episode) with three verification
back ends, and treat F4/F5/F7 as invariant libraries over that model.

## Q4. No-go results worth verifying (strongest first)
1. **Usefulness lower-bounds leakage (decisive for F2).** If honest usefulness requires the receiver to distinguish N
   outcomes (it must act differently on N different honest messages), then the receiver's view has ≥ N values, and an
   adversarial sender can transmit log2 N bits exactly (attain_embedding). So no channel can be both useful for an
   N-outcome coordination task and leak less than log2 N bits. This says F2 is worthwhile only where the required
   honest information is small (status/handshake channels), not for code or free-text handoffs. Short Lean proof
   from `attain_embedding`; I propose to prove it next.
2. **One bit coordinates (SC-05).** Any channel of capacity ≥ 1 bit lets colluders coordinate a binary action with
   certainty; cardinality bounds never imply "no coordination". Trivial but worth stating formally next to SC-01.
3. **Average ⇏ worst case** (done: `ComposeBlindSpot`).
4. **After-the-fact detection is worthless for live irreversible actions.** For actions whose effect precedes the
   flag, catastrophe probability is independent of detector quality. Formalizable in the existing deploy games.
5. **Local budgets do not compose.** Per-episode or per-agent budgets permit unbounded total leakage or spend unless
   accounted globally (generalises the two-episode split; F8).
6. **Semantic undecidability.** "Contains a backdoor" is undecidable for general programs (Rice); any SC-15/20/22 claim
   must be a narrower decidable property or a conditional one. Classical; cite rather than formalize.

## Q5. Wave 1 versus finishing SC-01
Finish SC-01 to a defined stop: lifetime ledger (done), reachable accounting (done), fixed-code alerts and frozen
snapshot (done), and an explicit statement that shared-kernel side channels need VM isolation. Do not pursue VM-level
isolation now. Then make **Wave 1 (SC-03 egress + SC-08/09 effects + SC-25 check-before-effect) the first end-to-end
deployable artifact**, because: it controls actions (the thing that causes harm), its usefulness is measurable on
BashArena main tasks, and Q4.1 suggests SC-01's realistic use is narrow (low-information coordination channels).

## Q6. Can legitimate SWE work be done under these restrictions?
Unknown until measured, and the catalog is right to demand baselines. Concretely: on BashArena honest main tasks,
compare an honest agent's completion rate under (a) unrestricted, (b) no network except a package mirror, (c) (b) plus
no privilege changes, (d) (c) plus exec only through tool RPCs (no shell). My expectation: (b) and (c) keep most
tasks; (d) breaks most SWE work, so the shell must stay and enforcement must be OS-level. This needs Docker and model
API spend; I will not claim usefulness until it is run.

## Q7. Where "bounded observation" is being confused with stronger properties
- It is not **confidentiality**: it bounds exact recovery of a UNIFORM secret; a low-entropy or structured secret
  (one bit "the monitor is off", a short password from a small dictionary) is recovered with high probability.
- It is not **coordination prevention** (Q4.2) and not **safety** of any downstream action.
- **SC-06** ("covert instruction in shared artifacts"): instructions are low-entropy; a cardinality bound does not
  help; this row needs F1/F3 (who may write what) rather than F2.
- **SC-24**: the untrusted monitor must see the submission, so its view is not small; the relevant quantity is the
  mediator's domination constant L (UMPROTF1), not cardinality.

## Q8. Existing work to reuse rather than rewrite
- **seL4** (verified microkernel with machine-checked integrity and information-flow noninterference proofs) as the
  isolation base if side channels matter; the closest verified answer to "the gateway is the only channel".
- **Cedar** (AWS authorization language with Lean-verified semantics) for F1/F7 policies; already planned in REUSE.md.
- **Capability-based prompt-injection defenses** (e.g. Google DeepMind's CaMeL, 2025) for SC-23.
- **gVisor / Firecracker** for VM-grade isolation of agent sandboxes (closing shared-kernel channels in SC-01/04).
- **ControlArena** settings and **LinuxArena** task sets for usefulness baselines (Q6).
- Verified-implementation tools (Verus, Dafny, or Lean code extraction) for a small trusted gateway, instead of
  differential testing alone.
I have not audited these projects for fit; the list is a starting point, not a recommendation of specific versions.

## Proposed next steps (pending John's decision)
1. Prove Q4.1 (usefulness ⇒ leakage) and Q4.2 (one bit coordinates) next to CovertChannel. Cheap, and it settles
   SC-01's scope.
2. Start Wave 1 with an OS-level egress/exec/privilege policy in the existing bubblewrap harness, an event-trace
   checker, and a BashArena usefulness baseline (needs Docker + API spend: John to approve).

DIALOGUE_STATUS: CONTINUE
