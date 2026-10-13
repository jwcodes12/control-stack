# Flexibility test: can canonical AI-control protocols be expressed in this framework?

Date 2026-10-13. Run in a throwaway worktree of `audit/r2-v8-trusted-code-20261013`; the SC-90 file now lives in `docs/flexibility-test/` (see its README).
This is a measurement by one agent session. Nothing here is evidence, a review, or a deployment claim.
"Reuse" and "new work" estimates marked (est.) are my extrapolations, not measurements.

## 1. Verdict

Partly met, and unevenly.

- **Researcher, deterministic gate-shaped protocols (human approval, audit log integrity, monitor flag plus audit
  budget as an admission rule):** met. A new scenario, SC-90 (trusted monitoring with a finite audit budget), went from
  a JSON spec to a file that compiles with standard axioms, no `sorry`, 18 headline theorems and witnesses, in about 6.5 minutes of
  wall time and 437 non-comment Lean lines. The generator plus `Core/Gate.lean` plus SC-26 as a pattern made this
  cheap. Necessity witnesses (one per check) fell out almost for free.
- **Researcher, probabilistic protocols (threshold defer, resampling, new untrusted-monitoring variants):** not met.
  Each existing result is a bespoke VCVio or real-valued-recursion file (335 lines for `DeferGame`, plus about 2200 lines of
  Refinement/Compose/Adaptive/Honeypot/Stratified machinery), with no generator, and no protocol vocabulary shared with the gate scenarios.
  Resampling and trusted editing are not formalised at all; the repo's own notes say so
  (`reviews/related-work-2026-10-07.md`: "no resampling/trusted-editing primitives yet"; `ledger/UMDEFER.lean` line 35:
  not a formalisation of suspicion-band defer nor of Ctrl-Z resampling).
- **The two halves do not compose in Lean.** SC-90 proves "every harmful effect is a monitor miss or an audit miss".
  `DeferMono`/`AuditBudget`/`ReservedRecall` bound the probability of misses. No declaration connects them, because
  the gate side uses `Gate.System` over lists and the probability side uses `Hist X Z`/`ProbComp`/`Finset (Fin N)`.
  A practitioner therefore cannot get "P(harmful effect reaches the ledger) <= f(recall, budget, N)" for a
  concrete gate.
- **Practitioner deploying a protocol:** not met. All premises that matter (recall, credential separation, hidden
  schedule, monitor statelessness) are docstring-level or runtime-checker-level. No tool takes a configuration and
  returns a bound with its premises checked. The runtime link is a trace checker, not a refinement proof, and the
  generated Python mirror does not know about hand-added state.

## 2. Table: six canonical protocols

Declarations named are those I read the statements of. File names are under `ControlStack/` unless noted.
"Spec?" asks whether `tools/new_scenario.py` (bad_event, roles, ops, checks, effect; arg types Nat/Bool/Payload only) can
express it.

| Protocol | Existing declarations | What they prove (one sentence) | Baked-in premises | Not covered | Spec? |
|---|---|---|---|---|---|
| (a) Trusted monitoring + audit budget | `AuditBudget.random_survival_le_pow`, `observable_schedule_nogo`, `budget_example`; `Families/F6/ReservedAudit.reserved_adaptive`; `F6/ReservedRecall.adaptive_recall_bound`; `F6/DamageBound.damage_bound`; `F6/MonitorEnsemble.blind_spot_escape`; `DeferGame.deployV_eq_catVE`; `DeferMono.defer_mono`; `AuditGate.invariant_preserved`; new `Scenarios/SC90TrustedMonitorAudit.sc90_safe` | A k-step attack survives a uniform random B-of-N audit schedule with probability C(N-k,B)/C(N,B) <= ((N-B)/N)^k; with a hidden reserved schedule and recall >= r this holds for every adaptive attacker (hypMiss); `defer_mono` bounds the catastrophe probability of the operational audit-then-defer game by the `catV` recursion; SC-90: after any legal trace every ledger entry was monitor-PASSed or flagged-and-audited-clean, flagged effects <= B, caught implies HALT. | Perfect or recall-r audits, per-history recall; catch is absorbing shutdown; schedule hidden and uniform; fixed N rounds; monitor stateless with fresh coins; `AuditBudget` is stated only for a fixed attack set (adaptivity argued in prose); in SC-90 the monitor is an arbitrary oracle and audits only cover flagged requests. | Suspicion-score/threshold trade-off and false-positive cost (only `ReservedAudit` has adversarial FPs); trajectory-level monitors; measuring recall; random audits of PASSed requests in SC-90; link between SC-90 and the probability files. | Gate half: yes (done in SC-90, with manual edits). Probability half: no. |
| (b) Defer-to-trusted at a threshold | `DeferGame.deployV`, `catV`, `DeferGame.defer_bridge` (the equality form, `DeferBridgeClaim`), `DeferMono.defer_mono`; `ledger/UMDEFER.lean` (UMDEFERF1, per `STACK.md` and `fidelity/UMDEFERF1.md`, separate Lake project) | After the audit budget is exhausted, a flagged bad item is halted w.p. >= eta or sent to a trusted service that neutralises it w.p. >= a(h,x,z), else the run continues; the operational catastrophe probability is <= `catV`. | Defer happens only at an exhausted budget (a fallback, not a threshold policy); the trusted replacement is "complete and safe"; uniform conditional floor on the service catch rate (UMDEFERF1) ; unmetered deferred-audit service; Bad is a predicate on submissions; first PASSed bad item is catastrophe. | A suspicion score, a threshold or defer fraction, and anything about the quality or cost of the trusted replacement. Availability exists (`UMUSEF1`, `OutcomeProof.lean`) but is full-run completion, not task usefulness. The ledger project is not importable: `catV` is linked by textual copy. | No for the threshold (no scores, no probabilities). A deterministic "defer" op is expressible but the threshold collapses to a Bool. |
| (c) Resampling / defer-to-resample | None. `ledger/UMDEFER.lean` l.35 and l.81 and `fidelity/UMDEFERF1.md` l.42 explicitly exclude it. | Nothing. | n/a | Everything: re-draw from U, incrimination by repeated suspicious resamples (Ctrl-Z), cost in extra U calls, adaptivity of U to resampling. | No. Needs a sampling op with a kernel and a counter over draws; probabilistic. |
| (d) Trusted editing | None as an action rewriter. Nearest: `Scenarios/SC26Transaction.sc26_safe` (exact payload bound to approval, so an edited payload needs a new approval); ledger T4b/T4c mediators rewrite the monitor's VIEW, not the action (`CORRESPONDENCE.md` l.19). | Nothing about editing. | n/a | A trusted edit step, "the executed payload is the editor's output", the editor's capability loss. | Provenance half: yes (an `edit` op by a trusted role plus a "payload came from the editor" invariant, est. 100-150 lines starting from SC-90). Safety-vs-quality half: no, it is capability-dependent. |
| (e) Untrusted monitoring, collusion/signal defences | `Refinement.lean` + `RefinementProof.lean` (`EndToEndClaim`); `HoneypotBridge*.lean`; `Families/F6/MonitorCollusion.pass_transfer`, `stego_fools_honeypots`, `canon_channel`, `canon_restores`, `phase_learning`; `ComposeGame.lean`; `StratifiedGame.stratifiedSurvives_binomial`; `AdaptiveGeneric.sharp_uniform_cat`, `AdaptiveUMADAPT.sharp_uniform_seed_risk`; `Scenarios/SC05Signal.lean` | For every colluding pair (shared seed, stateless monitor, adaptive generator), P(pass the upfront honeypot test, then uncaught catastrophe) <= (1-r) + r*L*(n_s+1)/(n_h+1) when bad views are L-dominated by the honeypot view law; trusted+untrusted composition multiplies by tau; per-class honeypot blocks give a product of binomial CDFs; a canonicalised view carries at most log2 K covert bits per item. | Monitor sees only (seed, view), no call index or counter (a call-counting monitor reaches probability 1); test before deployment; absorbing shutdown on catch; mediated view complete; L is a hypothesis; r STANDING; finite rational kernels. | Side channels outside the view (timing, metadata); an untrusted monitor that is better than a trusted class rule is NOT established (`STACK.md` l.42); real LLM collusion capability. | No. This is the part of the repo furthest from the generator. |
| (f) Human approval gate before side effects | `TrustedBroker.trace_preserves`, `halted_absorbing`, `committed_nonce_unusable`; `Scenarios/SC26Transaction.sc26_safe`, `safe_of_sound`, `sc26_once`, `halt_freezes`, `inflight_after_halt`, 8 necessity witnesses; `Core/Gate.Spec.trace_safe`; `Families/F7/Approvals.lean` is only a facade import | After any legal trace every bank entry has a request with exactly that payload and an approval of exactly that payload by an approver who is not the requester; keys unique; total <= cap; halt freezes new sends. | Credential separation; "an op carrying an approver's UID is that approver's consent"; idempotent receiver; atomic storage; no clock rollback; role disjointness for `sc26_safe_disjoint`. | Approver attention budget, rubber-stamping, the harm of an exactly-approved payload, content leakage via payload. | Yes. This is the generator's native shape (`--example-spec`). |

Observations on the table.
- (f) and the gate half of (a) are the same transition system with different admission rules. SC-90's `audit` is
  SC-26's `approve` plus a counter cap and a flag precondition. Nothing in the repo exposes that as one parametrised gate.
- Row (a) is the best covered; I count 8 files that say something about it, and the registry (2237 declarations; 2196
  SOURCE_ONLY; 2162 with adversary class UNKNOWN) cannot answer "what exists about audit budgets" without reading files.

## 3. Attempt: SC-90, trusted monitoring + audit budget as a gate

Artifacts (new, untracked): `ControlStack/Scenarios/SC90TrustedMonitorAudit.lean`, `docs/flexibility-test/sc90.json`.

**What was modelled.** Roles agents/monitors/auditors/admins. Ops: request, monitor (records an arbitrary flag per
request, first verdict wins), audit (spends one unit of a total budget `B` on a FLAGGED request; `caught` is the finding;
a catch halts), execute, directCall, halt. Seven checks: monitorGate, auditGate, budget, haltOnCatch, auth, dedup,
haltCheck. Payload has a ground-truth `harm` bit that no check reads.

**What was proved** (all from `init`, all legal traces, `Sound` configurations):
- `sc90_safe`: ledger entries have a matching request and were Cleared (PASS, or FLAG plus an audit with no finding);
  ledger keys unique; `(flaggedEffects s).length <= B` (flagged effects inject into audits, which are key-unique and
  capped); a caught audit implies halted.
- `harmful_effect_is_a_miss`: a harmful effect is monitor-PASSed or audited-clean. `only_monitor_misses_escape`: with
  perfect audit recall (a hypothesis on the audit log), only monitor PASSes reach the ledger.
- `exhausted_blocks`: once `B <= #audits`, a flagged unaudited request never executes on any legal continuation.
- `halt_freezes`: with haltCheck and auth, after a halt the whole state is frozen.
- `spec`: a `Gate.Spec` instance (reuses `Core/Gate.lean`). Non-vacuity: `honest_trace_effects`, `budget_zero_blocks`,
  `caught_halts_and_blocks`, `monitor_miss_escapes`. Necessity: `no_<check>_breaks` for all 7 checks.

**What this does and does not say.** The deterministic statement is "a harmful effect needs a monitor miss or an audit
miss, and the number of audit-cleared effects is at most B". It does not bound the probability of a monitor miss, so it is
not a safety bound by itself. The `harm` bit is never read by the gate, so `harmful_effect_is_a_miss` is really
"every effect is Cleared"; the label only gives the sentence its meaning.

**Numbers.**

| Quantity | Value |
|---|---|
| Wall time, spec written to first fully compiling file (clock) | 376 s (about 6.3 min). Reading the repo beforehand took about 15 min and is not counted |
| `lake env lean` runs | about 10 (the first: skeleton as generated, 4 s; final 5.1 s) |
| Compile errors fixed along the way | about a dozen across 5 rounds (wrong lemma names `List.inj_on_of_nodup_map`, `Cleared.mono` implicit unification, one `split_ifs` ordering, `simp` made no progress x2, one leftover Bool goal) |
| Generated skeleton | `.lean` 211 lines; also `model.py` 169, `check_trace.py` 169, `run_sc90.py` 167, `prereg/SC90-DRAFT.md` 125 |
| Final `.lean` | 614 lines, 437 excluding blanks, comments and `#print`; about 55 of those lines are skeleton lines kept (Payload, Roles, Op, Checks, full, Sound, init, R0) |
| Declarations | 57 top-level (defs, structures, lemmas, theorems), 0 `sorry` |
| Largest proof | `step_inv`, about 75 lines; `flagged_le` 20; `ledgerAppend_inv` 20 |
| Axioms (`#print axioms`) | all `propext`/`Quot.sound`, and `Classical.choice` for `no_budget_breaks` and `no_auth_breaks` (all standard). No `sorry`, no `native_decide` |
| Existing Core declarations reused | `Gate.System`, `Gate.Spec` (structure and one instance, 8 lines plus `step_ledger_prefix`, 17 lines) |
| Existing Core lemmas reproved instead | trace induction (`run_inv`, 7 lines, instead of `Spec.trace_safe`), absorbing halt (`halt_freezes`, 25 lines, instead of `withHalt`/`halt_absorbing`), plus SC-26's `reqOf_append` and its `bankAppend_inv` pattern (about 30 lines) |
| Reuse by name of any lemma from `AuditBudget`, `DeferGame`, `Core/Compose`, `Core/Cert`, `Core/Leakage` | 0 |
| Python mirror, difftest, prereg, scenario bundle, runtime harness | not written (see below) |

`check_scenarios.py` exits 1 as soon as the generator output sits in the tree without a bundle (`scenarios/SC-90/threat.md`
missing; the generator warns about this). I moved the generated `scenarios/SC-90/` and `prereg/SC90-DRAFT.md` out of the
tree so the repository checks stay green; they are not part of the result.

**Places the framework resisted.**
1. **No numeric parameter slot.** The spec has only Bool checks. The budget `B` had to be threaded by hand through
   `step`, `run`, `sys`, `Good`, `Inv` and every theorem. `sys` in the skeleton hard-wires `full`. The Python mirror and
   harness have no `B` either, so they would not be a mirror of the final Lean.
2. **State fields.** The skeleton's `St` has only `ledger`. Requests, verdicts, audits had to be added by hand.
3. **`legal : Op -> Prop` is state-independent.** "The auditor reports harm when the payload is harmful" cannot be a
   `legal` premise. I stated it as a hypothesis on the final audit log (`AuditRecallPerfect`), which is weaker than a
   per-step premise and does not compose across traces.
4. **Monitor quality cannot be stated.** The monitor is an arbitrary Bool-valued op. That is the worst-case monitor, which
   makes the theorem sound for every monitor but loses recall and false positives entirely.
5. **`Spec.trace_safe` is stated over `{o // legal R o}`.** To use it for `sc90_safe` I would have had to convert
   `List Op` with `hops` into a list of subtypes. I reproved the induction (7 lines). A `trace_safe_legal` lemma is missing.
6. **`withHalt` was not usable.** Like SC-26, the gate keeps its own `halted` bit and `halt` is a gate op, so
   `halt_absorbing` was reproved for the product-free case.
7. **Atomic delivery.** The skeleton's own lessons say to model in-flight effects at HALT; I did not. `halt_freezes` is
   therefore stronger than the real system can claim (SC-26's `inflight_after_halt` shows why).
8. **Mixed list-log lemmas are copy-pasted.** Key-uniqueness, append monotonicity, and "injects into a capped list"
   have no shared kit. `flagged_le` (the budget statement) is the only novel piece of combinatorics and took 25 lines.

**Not done in the timebox:** the differential test against `model.py`, the harness, a preregistration, any link to
`AuditBudget.lean`. `AuditBudget.lean` compiles standalone in 4.6 s (Mathlib only), so an import is feasible; a bridge
would need a map from `Fin N` rounds to request ids and a statement that FLAG-triggered audits and hidden-schedule audits
are different budgets (`ReservedAudit` already splits Bh/Bf).

## 4. Ranked list of missing abstractions and tooling

1. **A stochastic gate / bridge lemma.** A `Gate.System` whose oracle ops (`monitor`, `audit`) are sampled from kernels
   with stated recall and false-positive rates, and a theorem that turns `Good` plus kernel bounds into
   `P(harmful effect) <= ...`. Without it, SC-90 and `AuditBudget`/`DeferMono` cannot be combined. This is the largest
   gap for both audiences.
2. **Protocol combinators with lifted specs**, in the style of `withHalt`: `withAuditBudget B`, `withMonitor`,
   `withDefer`, `withEdit`, `withResample`. Today the budget logic is inlined into each `step`.
3. **Parameters in the generator.** Numeric config (budget, cap, threshold), extra state fields, and matching Python
   mirror and difftest. Right now every nontrivial scenario starts with hand edits to all five generated files.
4. **A shared append-only-log invariant kit in `Core/`.** `Ext`/`inv_of_ext`/`reqOf_append`/`ledgerAppend_inv`,
   key-nodup, and "count of keyed entries <= capped key list". SC-26 and SC-90 both re-derive them.
5. **State-dependent premises about trusted roles.** `legal : St -> Op -> Prop` or an explicit role-behaviour predicate
   over logs, so that "auditor recall = 1" or "monitor is stateless" can be part of a trace theorem.
6. **Missing primitives:** resampling, trusted editing, suspicion score and threshold, and a defer fraction with a cost.
   None exist in any form.
7. **A safety/usefulness frontier object.** Only availability (completion probability) exists. A practitioner choosing
   B and a threshold needs a curve or at least a cost term for audits, defers and resamples.
8. **Cross-project import.** `ledger/` (UMDEFER, UMUSE; Lean v4.35 Mathlib) and `ControlStack/` (VCVio) are linked by
   textual copy of `cat`/`catV`. Any theorem there is unavailable to a new scenario.
9. **Discoverability.** The registry classifies 75 of 2237 declarations by adversary class; searching it for a
   protocol name finds nothing. A protocol-to-declarations index (what this report's table does by hand) would help.
10. **A practitioner front door.** Input: protocol parameters. Output: bound, list of premises with their runtime
    checker, and what is unmodelled. `tools/cstack.py` shows status of existing scenarios; I did not test whether it
    can do this for a new one.

## 5. Reproduction

```sh
export PATH=$HOME/.elan/bin:$PATH
mkdir -p .lake && ln -s /home/opc/projects/control-stack-r2v8/.lake/packages .lake/packages
cp -r /home/opc/projects/control-stack-r2v8/.lake/build .lake/build      # only Core/Gate is prebuilt
python3 tools/new_scenario.py SC-90 docs/flexibility-test/sc90.json      # skeleton; the committed .lean is the hand-finished one
lake env lean ControlStack/Scenarios/SC90TrustedMonitorAudit.lean        # 5 s; ends with 18 `#print axioms` lines
```

Do not re-run the generator over the finished `.lean`: it refuses to overwrite and the finished file is not a skeleton.
