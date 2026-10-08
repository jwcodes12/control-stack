> **SC-03 egress slice (2026-10-08, Sol).** Implemented `egress/` launcher, strict pinned-peer gateway, adapter,
> actual namespace validator, independent packet/syscall observers, bounded attacker suite and pinned wheel usefulness task.
> Final serial runs: 62/62 full cases pass; namespace, failed-SYN and direct-mirror mutations detected; 34 parser-only cases
> are an explicit partial pass; unprivileged full mode exits 2/blocked (CAP_NET_RAW absent). Zero packet drops, no orphan
> mirror SYNs. Seven oracle regressions pass; `egress/check_lean.sh` checks six theorems with standard axioms;
> `lake build ControlStack` passes (existing VCVio deprecation warnings). `egress/check_evidence.py` validates source hashes
> and stored receipts. An early concurrent fixture run contaminated observation windows; it was discarded, a host-wide
> abstract-socket serialization lock was added, and all recorded final receipts were rerun serially.
> R10 source fetched from jwcodes12/control-stack; tracker #1. Astra and approved Opus 5.5 reviewed an earlier snapshot;
> dispositions are in `egress/REVIEW-DISPOSITIONS.md`. Strict response/task completion, packet-loss checks, complete mountpoint
> allowlist, namespace-wide socket-FD checks, absolute header deadline, host strace and SYN provenance were added.
> `.github/workflows/egress.yml` configured; no remote CI run or production sandbox deployment claimed. Auditgate untouched.
> Next: all-destination process-attributed accounting in a disposable outer topology; remote publication/CI remains pending.
> A bounded independent CLI follow-up timer is active for 2026-10-08 09:30:31 UTC; prompt/log directory:
> `/home/opc/handoff/control-stack-egress/`. This is five hours after scheduling, not a confirmed account reset timestamp.

> **SESSION 8 FINAL (2026-10-08).** See ROADMAP "Session 8 status note". Latest export commit 4a6cbeb (CI green:
> fast, lean-covert, auditgate-db). SC-03 and SC-16 paused; next external-review round to answer is chatgpt-10.md.
> **SESSION 8 RESULTS (2026-10-07).** Export fixed: root `ControlStack.lean` imports every proof module; full `lake build` passes; pushed (`feefc34`).
> - `DeferMono.lean`: monotone defer bound (lower bounds on recall/halt/service ⇒ catastrophe ≤ catV).
> - `ComposeGame.lean`: trusted+untrusted composition, product bound (1−r)+r·τ·L·(n_s+1)/(n_h+1) with fresh trusted coins; tight at n_h=0.
> - UMADAPTF2 verified (frozen cf874653d2fa; sol-high + flash pass).
> - TMCERTUSF1 verified (frozen 3b0cda8ceba9). Opus subagent reviews forced v2 (non-degenerate witness) and v3 (admissible-row check; v2 accepted vacuous floors); v3 passed flash + Opus. `UseQ.lean` ported; LASR fixture re-checks.
> - Blocked on John: item 1 needs deployment-matched held-out data; TMLIPF1 needs a v2 reformulation (gaps listed in ROADMAP) and a decision on overriding the novelty `kill`.
> - Leak found: Luna's export `a3e86e1` had a "proofledger" comment (fixed forward; remains in private history).
> **SESSION 8 (2026-10-07).** The `a3e86e1` export push now succeeds (DNS recovered). The four game modules (SoftSlack, SoftHockey, StratifiedGame, DeferGame) built, so they move to ROADMAP's Completed table. Audit of these modules: no `sorry`/axioms; DeferGame's `catV` matches the frozen UMDEFERF1 definition verbatim. Limitation: `defer_bridge` assumes *exact* recall, halt and service rates (equalities), so it gives no safety bound when recall is only bounded below. Fixed: `ControlStack/DeferMono.lean` proves `defer_mono` (recall ≥ r, halt ≥ η, service ≥ a ⇒ operational catastrophe ≤ `catV`), standard axioms; not ledger-gated. Also removed a leaked "proofledger" comment from the export (it had been pushed in `a3e86e1`; fixed forward in `a140197`).
> **SESSION 7 CONTINUATION (2026-10-07).** Added `catVE_toReal_eq_catV` and `defer_bridge`, completing the calibrated real-valued bridge from the VCVio operational game to ledger `catV`. `lake build ControlStack.DeferGame` passes; `#print axioms` for both bridge theorems reports only `[propext, Classical.choice, Quot.sound]`. TMLIPF1 review returned Reviewer A `kill` (classical Bellman stability) and Reviewer C `revise` (witness/formulation drift); no restatement or freeze was made because the witness repair does not answer the substantive `kill`.
> **SESSION 6 CONTINUATION (2026-10-07 ~19:22 UTC).** `ControlStack/AdaptiveGeneric.lean` and `AdaptiveUMADAPT.lean` compile the sharper adaptive survival bound and seed-risk composition. The separate proofport `proofledger/campaigns/UMADAPT/forms/UMADAPTF1/proofs/sharp-conv-port.lean` proves `conv_a_sharp` against the actual campaign `Setup`, `cat_ge`/`pass_eq`, `adProtocolCat`, and `seedLaw`; direct gate assembly passed, and a separate axiom check reports only `[propext, Classical.choice, Quot.sound]`. No ledger event or frozen statement changed. Next: decide whether to register a separate campaign strengthening and red-team its statement.
> The anonymized private export was refreshed with these modules and pushed as snapshot commit `98fe35f`.
> **SESSION 6 STATUS (2026-10-07).** Stratified VCVio survival, seeded factorization, and classwise end-to-end safety compile with standard axioms.
> The LASR interval fixture now has a `checkUseQ` certificate and full-history soundness floor `22873/250`; deployment-matched held-out data remain missing.
> The anonymized private export is refreshed and pushed. UseQ awaits second-family review; automatic review rejected Anthropic statement egress pending user approval.
> TMLIPF1 Claim and Witness local proofledger gates pass (standard axioms); the two-family review is complete (OpenAI: `kill` on novelty; Google: `revise` on formulation). It remains a draft and unfrozen. Sandbox red-team attempts failed. The usefulness checker still awaits second-family review; its external dispatch has not been approved.
> `DeferGame.lean` proves operational equality with an exact `ENNReal` recursion and one-step expansion. `catVE_toReal_eq_catV` now proves the calibrated real bridge, packaged as `defer_bridge : DeferBridgeClaim`. Frozen statements were not changed.
> `AdaptiveBalance.lean` and `AdaptiveSharp.lean` prove the balancing and weighted-path cores; `AdaptiveGeneric.lean`/`AdaptiveUMADAPT.lean` and the checked proofledger proofport now connect the adaptive tester to the sharp aggregate bound. The frozen UMADAPTF1 claim remains unchanged at `t(1 − tn/k)`; the sharper result is an auxiliary proof, not a registered statement.

# Session 5 continuation (2026-10-07). Added exact-rational simultaneous ROC bands and a LASR archive converter. Generated an eight-vertex, 100-step/two-coin interval table; `checkRiskQ`, `checkLawfulQ`, and the TMCERTF1 full-information risk bound compile by `decide +kernel`, with standard axioms only. This is a real-data pipeline demonstration, not deployment certification (the sample's held-out/IID/deployment match is unestablished). Added the VCVio soft-hazard honeypot survival bridge in `ControlStack/SoftSlack.lean`; it compiles with standard axioms. Added `COMPOSITION-N1-UMPROT.md`: still design-stage pending a common protocol/event and adversary intersection; only the `min` corollary is currently justified. TMLIPF1 remains a local draft pending the user's decision on external review. The anonymised private export was refreshed with these results.

> **SESSION 5 CONTINUATION STATUS (2026-10-07).** `SoftSlack.lean` proves exact survival, seed factorization, first moment and end-to-end domination bound `(1-r)+r·L·ns/(nh+1)`. `SoftHockey.lean` proves the finite hockey-stick pass bridge and end-to-end bound `(1-r)+r·(δ+e^η·ns/(nh+1))`; both compile with standard axioms. Stratified and defer game variants remain. Next: implement the stratified game bridge, then refresh the anonymised export.

> **SESSION 5 STATUS (2026-10-07 ~16:00 UTC).** Opened draft campaign TMLIPF1, depending on TMCERTF1: certificate inflation by row L1 error, plus finite-grid confidence-box transfer.
> Statement compiles; local claim and witness gates pass with standard axioms; exact N=1 and finite-grid witnesses are included.
> External formulation/red-team transmission was rejected by automatic review; user approval is pending. No freeze, final gate, or theorem promotion yet.

> **SESSION 4 STATUS (2026-10-07 ~15:45 UTC).** Added DESIGN-A2 and an exact-rational 100-problem/2-coin fixture; 101 certificate rows, 1,200 checker inequalities.
> Illustrative full-information risk bound ≈0.45051; honest used-solutions estimate ≈52.464/100. The ROC endpoints are synthetic, not empirical confidence bands.
> Next: obtain labelled validation data, derive simultaneous rational bands, then run the concrete `checkRiskQ`/`decide +kernel` fixture; no theorem was added.

> **SESSION 3 STATUS (2026-10-07 ~15:20 UTC).** TMCERTF1 and TMGACF1 frozen; both reviewer families pass; claim/witness gates pass with standard axioms.
> Research and proofledger records committed; private export `d320fa9` pushed to `jwcodes12/control-stack` main; both new CIDs pass independent ledger-check.
> Session 3 tasks 1–4 complete. Task 5 skipped as instructed.

> **SESSION 3 STATUS (2026-10-07 ~14:45 UTC).** Precursors 1–3 DONE (UMCERTF1, UMADAPTF1 verified; Outcome game proved).
> Direction (A) remaining steps (all mechanical):
> 1. TMCERTF1: sol-high PASS; flash pending. Then `pl freeze TMCERTF1`, `pl gate TMCERTF1 /var/tmp/opus-provers/TMCERTF1/proof.lean
>    --actor anthropic:claude-opus-5-5` (dry-run gate already PASSES), copy proof to proofs/, ledger/TMCERT.lean from
>    ledger-drafts/TMCERT-v2.lean, fill the hash in fidelity/TMCERTF1.md (drafted), STACK row, ROADMAP.
> 2. TMGACF1: red team (sol-high, flash) runs after TMCERT's. Proof ready: /var/tmp/opus-provers/TMGACF1/proof.lean (554 lines;
>    needs TMCERTF1 verified before gating). Same steps; fidelity/TMGACF1.md drafted.
> 3. Refresh the private GitHub export (/var/tmp/cs-export; anonymise; ledger-check the 2 new CIDs; push).
> 4. Then disable routine trig_01RsgfEAcQ1rDt5TZLo2tLMp. John said tokens are low: be economical.

# Session 2026-10-07: a Lean-verified, capability-free control stack, layer 1 (collusion) plus action-layer step 1

Prompt: `~/research/proofledger/prompts/` (next-session control stack); skill `/safety-theory-sprint` with John's
overrides (classical lemmas allowed as infrastructure; no GPU work). Nothing was sent to anyone.

## Deliverables (in the prompt's order)
1. **REUSE.md** (decisions, costs) and **CORRESPONDENCE.md** (ControlArena / LASR mapping).
   - VCVio builds cleanly in `~/research/control-stack` (Lean v4.34.0; 11.5 GB; about 10 min). It gives T1 for
     arbitrary `ProbComp` distinguishers in two lines (`ControlStack/Spike.lean`).
   - The quantitative core is real-valued finite sums in the shared 4.35 project, ledger-gated.
   - Nothing was vendored: the Atlas repos have no TV or hockey-stick material; TestingLowerBounds is a
     correspondence target.
   - Cedar (pinned `3f51c8f7`) is planned for a later action-layer step; Veil was rejected (sorry-based SMT trust).
2. **DESIGN.md v1.** The model, the full assumption list (TRUSTED-COMPONENT / MODELLING / STANDING) and the theorem
   list. v0 was hostile-reviewed *before* any Lean (Sol xhigh: "reject as spec"; Sonnet: "major"), and every point is
   dispositioned in §8.
3. **Verified CIDs** (proofledger, `pl headline` OK; two foreign red-team passes each, no overrides; standard axioms):
   see the table below.
4. **STACK.md.** Maps each guarantee to its assumptions and to real protocols, and lists what is still unproved.
5. **Honest significance and next step:** below. The final review is in `reviews/final-review-{sol,sonnet}.md`.

## Verified results
| CID | plain-English guarantee | proof |
|---|---|---|
| UMHSF1 | hockey-stick pass bound (attained), TV bound, kernel DPI, content factorisation, exact and approximate decoder floors, perturbation, maximal-leakage floor (attained), domination from class coverage | 348 lines |
| UMSURVF1 | honeypot-test survival depends only on the pass rate h; binomial CDF / (1−κh)^n; h·S ≤ (n_s+1)/(n_h+1), and ≤ n_s/(n_h+1) for soft slack | 200 lines |
| UMPROTF1 | **for every colluding pair** (shared seed, stateless monitor, adaptive generator): P(uncaught catastrophe) ≤ (1−r) + r·L·(n_s+1)/(n_h+1) when bad views are L-dominated by mediated honeypots (also hockey-stick and soft forms); the first bad submission decides; one-shot attainment | 276 lines |
| UMSTRATF1 | stratified honeypots with class-aware shutdown: ≤ (1−r) + r(s_c+1)/(m+1), with no class-count factor; attained by a decodable colluder | 218 lines |
| UMNOGOF1 | a content-preserving mediator with k decodable bad classes: **one deterministic colluder** beats every iid honeypot law, every shutdown schedule and every budget, with probability ≥ (1−1/k)^{n_h}; exact attainment curve | 244 lines |
| CANONF1 | a verified canonicaliser for a toy imperative language: semantics preserved; unique normal form modulo for→while, `;`-association and local renaming; class-agreeing laws give identical mediated laws | 757 lines |
| SANDBOXF1 | the proofledger sandbox (bwrap mount table): (a) the current policy lets a sandboxed process write the host `~/.elan`, which the gate executes; (b) a read-only-root policy confines host writes to scratch plus declared state directories; (c) the current hiding works at mount level, outside the stated `/proc` boundary | 91 lines |

## Harness work (proofledger)
- `a637fac`, `a08075e`: stack statements may reference transitive dependency definitions (check_statement, gate,
  auto_probe, red-team prompts); `tests/test_deps.py`.
- `6ea98c5`: red-team verdicts are bound to the reviewed statement hash. A stale Flash verdict after a restate had
  counted, live; `tests/test_redteam_binding.py`.
- **Found, not fixed (needs John):**
  - `dispatch.sandbox()` mounts a writable host root. This is proved in SANDBOXF1(a); the fixed policy is in
    SANDBOXF1(b) and needs a CLI compatibility test before deployment.
  - The scout additionally reports, unverified: no PID namespace with ptrace_scope 0 (a possible `/proc/<pid>/root`
    read of hidden directories), shared network, and readable credential files.

## Honest significance
(Final calibration after the novelty gate: see below.)

## Next formalisation step
(See below.)

# Session 2026-10-07 (second session, ~03:00 UTC onwards)

Prompt: `~/research/proofledger/prompts/next-session-control-stack-2.md`. Nothing was sent to anyone, and nothing was
deployed. Mid-session, John shared an external critique and a list of prior art. Both are recorded with their
disposition in `reviews/external-critique-2026-10-07.md` and `reviews/related-work-2026-10-07.md`.

## Delivered
| item | status | notes |
|---|---|---|
| SANDBOX2F1 (corrected sandbox fix) | **verified** (frozen 094db3d3379a) | state binds before the hiding tmpfs; hiding holds for every choice of state directories. Not deployed |
| UMLOWERF1 (converse for nonadaptive designs) | **verified** (frozen 8415ec049329) | restated after both red teams flagged that the colluder was chosen after the design; the proof was adapted |
| VCVio operational refinement | **proved** (394 lines; not ledger-gated) | the trace-level ProbComp game equals `catG` exactly; the protocol factorises; the end-to-end bound and attainment are in-project |
| UMUSEF1 (usefulness companion) | **verified** (frozen 61a4c0bdf711; 573 lines) | v1 rejected (false κ conjunct; PH ⊆ Bad mismatch); v2/v2.1 add the view-blind pair, the obstruction q·u ≤ D·X, Cantelli for both tails, the honest ROC and the b = 0 sharpening |
| UMDEFERF1 (audit-then-defer) | **verified** (frozen ad82ec06fc48; 714 lines) | v1 got major from Sol; v2 → v2.1 adds the service-dependent catV with a reachable conditional floor, the finite retry certificate, the protocol certificate and the no-go for every two-point honeypot law |
| prior-art positioning | done | STACK.md section; the defensible claim is narrowed to machine-checked worst-case probabilistic bounds for UM with honeypots |

## What the critique changed
- The positioning claim was narrowed, and the novelty labels lowered: UMUSE is an instance of Games for AI Control's
  framing, and UMDEFER's ratio is credited to Shlegeris/LASR.
- Decision-relevant findings are now explicit:
  - per-class slack vs a global counter (≈ 0.05 vs 0.38 risk at matched honest false shutdown);
  - deferral needs a uniform stopping hazard, priced at 1/θ;
  - a completion target forces risk ≥ α₀·u.
- **Proposed next direction (awaiting John):** Lean-check a Games-for-AI-Control trusted-monitoring certificate
  (merges with N1b), or port SOUNDGATE's gate model so that A4/A5/A11 become consequences of complete mediation.

## SC-03 authorized local follow-up — 2026-10-08 after 09:30:31 UTC

Read global instructions and local handoff/evidence first; no nearer repo agent
instruction file and no configured Git remote. No auditgate, production deployment,
publication, public target contact or external repository transmission. Existing
Astra/Opus review records were used locally. No rate-limit error occurred; the
five-hour timer is not evidence of account reset.

Fixed two observer correctness gaps: IPv6 connects now parse into independent
pinned-peer/prior-permit records (previously rejected by IPv4-only patterns), and
non-initial IPv6 fragments retain address evidence rather than being lost while
parsing continuation payload as extension headers. Two regressions reproduce the
old behavior. Refreshed original runtime receipts and assurance hashes.

Actual checks: `/usr/bin/python3 egress/test_oracle.py` → 9 tests OK;
`sudo -n /usr/bin/python3 egress/suite.py --output egress/results/local-full.json`
→ 62/62 pass, 1,454 kernel-counted packets, zero drops, 69 mirror SYNs/69 traced
connects, zero orphan SYNs. Same command with `--self-check-shared-net`,
`--self-check-packet-oracle`, `--self-check-direct-mirror` and the respective
`local-{namespace,packet,mirror}-mutation.json` outputs → mutation-detected,
zero drops, exit 0 for each. `--gateway-only --output egress/results/local-parser.json`
→ partial-pass, 34 controls. Ordinary-user full command outside managed network
restrictions with `--output egress/results/local-unprivileged.json` → blocked,
EPERM, exit 2. `egress/check_lean.sh` → six axiom checks pass;
`/usr/bin/python3 egress/check_evidence.py` → all refreshed source/receipt hashes,
full controls, mutations and outer calibration pass, CONDITIONAL. `git diff --check`
→ clean. No Lean source change; prior full build was not repeated.

Managed-sandbox attempts also blocked: default sudo has no-new-privileges; full
mode cannot create NETLINK_ROUTE (receipt `/tmp/egress-followup-managed-blocked.json`);
parser fixture socket initially got EPERM. Approved local escalated runs succeeded;
no automatic approval rejection. These blocks were not treated as denials/pass evidence.

Feasibility probe `sudo -n unshare --net /bin/sh -c 'ip link set lo up; ip -brief link; ip route show; ip -6 route show'`
→ exit 0, only lo, no external routes. Implemented isolated
`egress/experimental/outer_accounting.py`. Ran:

```sh
sudo -n unshare --net /usr/bin/python3 egress/experimental/outer_accounting.py \
  --host-netns "$(stat -Lc %i /proc/self/ns/net)" \
  --output egress/results/local-outer-accounting.json
```

Result: pass, exit 0; eight independent bind/connect/sendto flows across four
locally assigned IPv4/IPv6 documentation addresses and two sender PIDs; eight
initial TCP SYN/UDP packets attributed, 16 decoded frames total, 32 kernel-counted
frames, zero drops. Removing a flow detects missing provenance. Repeated after
per-child isolation guards; same result. Direct `--sender 0` without outer topology
exits 1 before traffic. No external links, default routes, DNS or target listeners.
All-destination packet capture here is a bounded calibration, not universal process
attribution: replies have no PID attribution, sandbox/gateway integration and raw,
inherited-FD/connected-UDP/sendmsg/io_uring paths remain untested. The corresponding
assurance assumption stays UNRESOLVED.

Commands, real results and limitations are fully recorded in
`reviews/egress-follow-up-2026-10-08.md`; README/FIDELITY/ROADMAP/HANDOFF updated.
Pre-existing untracked destination prototype and TMCERT review error/metadata files
were left untouched. Next: integrate gateway and disposable sandbox into the isolated
outer topology, then test alternate sends/inherited authority and negative provenance
mutations before expanding the claim. This bounded follow-up is complete; stop here.

## SC-03 publication authorization — 2026-10-08

John clarified that Git pushes are permitted and the external-send restriction
concerns emails/messages to people. Publishing the prepared private branch
`egress-r10-controls` and running GitHub CI are authorized. The completed local
follow-up is included; unrelated destination prototypes and review metadata are
excluded. Auditgate is unchanged.

Publication checks: `python3 egress/check_evidence.py` (receipt hashes, 62 controls,
three mutations and eight-flow calibration), `python3 egress/test_oracle.py`
(nine tests), `egress/check_lean.sh` (six theorem axiom checks) and
`git diff --check` passed. Remote results will be recorded after the push.
Next engineering step: integrate the gateway/sandbox into the isolated outer
topology; general process attribution remains unresolved.

## SC-03 remote egress CI — 2026-10-08

Private branch `egress-r10-controls` pushed at `b30177e`.
[Egress CI](https://github.com/jwcodes12/control-stack/actions/runs/37784398180) passed both jobs: 62/62 full controls, three
mutations, nine oracle regressions and six Lean axiom checks. Downloaded outcome
artifacts confirm 1,454 kernel-counted packets and zero drops in full mode; all
three mutation receipts also have zero drops. Existing fast/auditgate checks
passed; the covert-channel Lean job is still running as of this entry.
General attribution remains unresolved; gateway/sandbox integration in the isolated
outer topology is the next engineering step. Auditgate source is unchanged.

## SC-03 publication complete — 2026-10-08

Private branch `egress-r10-controls` is pushed at `7efd2dcf6f3b7786bfdedbc0c9b35e7d1ca1e610`.
Both latest-commit workflows passed:
- [egress-boundary](https://github.com/jwcodes12/control-stack/actions/runs/37784927374): negative controls and Lean egress jobs passed. Downloaded artifacts confirm 62/62 full controls, all three detected mutations and zero packet drops; parser remains an explicit 34-control partial pass.
- [fast-checks](https://github.com/jwcodes12/control-stack/actions/runs/37784927391): fast, auditgate-db and lean-covert passed. The slow full VCVio job is dispatch-only and was skipped on push; no new full-project remote build is claimed.

Local publication checks: receipt/hash checker, nine oracle regressions, six Lean
axiom checks and whitespace checks passed. The export checkout is clean and tracks
the pushed branch. Auditgate source and remote main are unchanged. Tracker #1
records publication, verification and the remaining gateway/sandbox integration
work; general process attribution remains unresolved. Git pushes and CI are
authorized; emails/messages to people still require approval.

## Astra/Opus xhigh roadmap consultation — 2026-10-08

Both requested reviews completed: native gpt-6-astra xhigh and exact
claude-opus-5-5 xhigh (served model confirmed in metadata). Reports, static
source packet/hash provenance and disposition are under
`reviews/roadmap-consult-2026-10-08/`. No code, auditgate source or assurance
status changed; no new test/exploit result is claimed.

The previous proposed roadmap mixed bounded exact-secret recovery with
monitor-based safety. Current next step is fixing the actual honest task,
usefulness target, horizon, lineage and observation contract, while testing
lifetime accounting and residual channels in parallel. Egress integration stays
a bounded supporting/separate reachability track. Sampling average monitor rates
does not establish content-adaptive coverage. ROADMAP.md now states this order.

Verification: `git diff --check`; consult metadata shows both requested models
at xhigh completed. Remaining work: implement the revised scenario contract and
usefulness viability gate; recommendations have not been implemented yet.

## SC-01 repair milestone — 2026-10-08

Implemented the contract/usefulness milestone and durable SQLite lifetime charging.
See `gateway/scenario/README.md`, the two preregistrations, source-bound receipts
and `ControlStack/ScenarioARepair.lean`. Contract preregistration: `1001024`.
Baseline and mediated repair each passed 320/320 episodes and 64/64 lifetimes;
simultaneous completion lower bound 93.382% exceeds the 90% floor. Ten ledger
controls, five scenario/oracle/evidence-mutation tests, ten gateway tests, selected
harness probes, three new standard-axiom Lean checks and full
`lake build ControlStack` (3,691 jobs) passed. Both final receipt verifiers passed.

The targeted shared-cache experiment decoded one secret bit in 64/64 trials with
a constant NULL gateway view. This falsifies the sole-transcript premise in the
current harness. It does not demonstrate full-secret recovery; the finite-view
Lean bound remains model-only and the case stays CONDITIONAL. Initial results
and corresponding changed source snapshots are retained, not pooled.

Next blocker: stronger isolation or a justified bound covering all receiver
observations, followed by repeat probes and gateway/model correspondence. Valid
host snapshot rollback, statistical runtime independence and workload transport
remain assumptions. Auditgate untouched. Private tracker: GitHub issue #2.

SC-01 private branch `sc01-repair-viability` pushed at `9a7e3a6`; GitHub CI completed successfully for all three workflows. Tracker #2 records results and the confirmed isolation blocker.

## Current continuation status — 2026-10-08

Canonical status: [gateway/scenario/STATUS.md](gateway/scenario/STATUS.md).
Published SC-01 commit `9a7e3a6` now has three successful GitHub workflows:
scenario-a-repair, fast-checks and egress-boundary. The 320/320 repair usefulness
result and 64/64 shared-cache bit observation remain the completed evidence.

A separate-runtime-file experiment is preregistered at source commit `8b96430`.
Five implementation files are local drafts; three rejection-control tests pass.
The first smoke invocation failed at `AttributeError: __enter__`; no receipt or
new cache/usefulness measurement exists. Next: fix lifecycle, run real preflights
and comparison/usefulness experiments, then consult Opus xhigh and Astra high
on meaningful results. Those new reviews remain pending. No runtime secrecy
certification or production deployment; auditgate untouched.
