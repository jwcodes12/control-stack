
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

> **SESSION 6 CONTINUATION (2026-10-07).** The sharper adaptive bound now compiles in standalone modules and in a separate kernel-gated proofport against the actual setup and protocol definitions. The proof uses only standard axioms. The frozen statement remains unchanged; a separate strengthening still needs registration and red-team review.
> The anonymized private export was refreshed with these modules and pushed as snapshot commit `98fe35f`.
> **SESSION 6 STATUS (2026-10-07).** Stratified VCVio survival, seeded factorization and classwise end-to-end safety compile with standard axioms.
> The LASR interval fixture has a rational usefulness certificate with conditional floor `22873/250`; deployment-matched held-out data remain missing.
> TMLIPF1 Claim and Witness local gates pass with standard axioms. Two-family review returned `kill` on the contribution and `revise` on formulation; it remains draft and unfrozen.
> `DeferGame.lean` now proves equality with an exact operational `ENNReal` recursion and calibrated real-valued ledger `catV`; bridge axioms are standard.
> `AdaptiveBalance.lean`, `AdaptiveGeneric.lean` and `AdaptiveUMADAPT.lean` prove the adaptive sharp aggregate bound; the frozen claim remains unchanged pending separate strengthening registration.

# Session 5 continuation (2026-10-07). Added exact-rational simultaneous ROC bands and a LASR archive converter. Generated an eight-vertex, 100-step/two-coin interval table; `checkRiskQ`, `checkLawfulQ`, and the TMCERTF1 full-information risk bound compile by `decide +kernel`, with standard axioms only. This is a real-data pipeline demonstration, not deployment certification (the sample's held-out/IID/deployment match is unestablished). Added the VCVio soft-hazard honeypot survival bridge in `ControlStack/SoftSlack.lean`; it compiles with standard axioms. Added `COMPOSITION-N1-UMPROT.md`: still design-stage pending a common protocol/event and adversary intersection; only the `min` corollary is currently justified. TMLIPF1 remains a local draft pending the user's decision on external review. The anonymised private export was refreshed with these results.

> **SESSION 5 CONTINUATION STATUS (2026-10-07).** `SoftSlack.lean` proves exact survival, seed factorization, first moment and end-to-end domination bound `(1-r)+r·L·ns/(nh+1)`. `SoftHockey.lean` proves the finite hockey-stick pass bridge and end-to-end bound `(1-r)+r·(δ+e^η·ns/(nh+1))`; both compile with standard axioms. Stratified and defer game variants remain. Next: implement the stratified game bridge, then refresh the anonymised export.

> **SESSION 5 STATUS (2026-10-07 ~16:00 UTC).** Opened draft campaign TMLIPF1, depending on TMCERTF1: certificate inflation by row L1 error, plus finite-grid confidence-box transfer.
> Statement compiles; local claim and witness gates pass with standard axioms; exact N=1 and finite-grid witnesses are included.
> External formulation/red-team transmission was rejected by automatic review; user approval is pending. No freeze, final gate, or theorem promotion yet.

> **SESSION 4 STATUS (2026-10-07 ~15:45 UTC).** Added DESIGN-A2 and an exact-rational 100-problem/2-coin fixture; 101 certificate rows, 1,200 checker inequalities.
> Illustrative full-information risk bound ≈0.45051; honest used-solutions estimate ≈52.464/100. The ROC endpoints are synthetic, not empirical confidence bands.
> Next: obtain labelled validation data, derive simultaneous rational bands, then run the concrete `checkRiskQ`/`decide +kernel` fixture; no theorem was added.

> **SESSION 3 STATUS (2026-10-07 ~15:20 UTC).** TMCERTF1 and TMGACF1 frozen; both reviewer families pass; claim/witness gates pass with standard axioms.
> Research and ledger harness records committed; private export `d320fa9` pushed to `jwcodes12/control-stack` main; both new CIDs pass independent ledger-check.
> Session 3 tasks 1–4 complete. Task 5 skipped as instructed.

> **SESSION 3 STATUS (2026-10-07 ~14:45 UTC).** Precursors 1–3 DONE (UMCERTF1, UMADAPTF1 verified; Outcome game proved).
> Direction (A) remaining steps (all mechanical):
> 1. TMCERTF1: Reviewer A PASS; Reviewer C pending. Then `pl freeze TMCERTF1`, `pl gate TMCERTF1 <proof-output>/TMCERTF1/proof.lean
>    --actor reviewer family:prover agent-prover agent-5-5` (dry-run gate already PASSES), copy proof to proofs/, ledger/TMCERT.lean from
>    ledger-drafts/TMCERT-v2.lean, fill the hash in fidelity/TMCERTF1.md (drafted), STACK row, ROADMAP.
> 2. TMGACF1: red team (Reviewer A, Reviewer C) runs after TMCERT's. Proof ready: <proof-output>/TMGACF1/proof.lean (554 lines;
>    needs TMCERTF1 verified before gating). Same steps; fidelity/TMGACF1.md drafted.
> 3. Refresh the private GitHub export (/var/tmp/cs-export; anonymise; ledger-check the 2 new CIDs; push).
> 4. Then disable routine trig_01RsgfEAcQ1rDt5TZLo2tLMp. John said tokens are low: be economical.

# Session 2026-10-07: a Lean-verified, capability-free control stack, layer 1 (collusion) plus action-layer step 1

Prompt: `<research-root>/ledger harness/prompts/` (next-session control stack); skill `/safety-theory-sprint` with John's
overrides (classical lemmas allowed as infrastructure; no GPU work). Nothing was sent to anyone.

## Deliverables (in the prompt's order)
1. **REUSE.md** (decisions, costs) and **CORRESPONDENCE.md** (ControlArena / LASR mapping).
   - VCVio builds cleanly in `<research-root>/control-stack` (Lean v4.34.0; 11.5 GB; about 10 min). It gives T1 for
     arbitrary `ProbComp` distinguishers in two lines (`ControlStack/Spike.lean`).
   - The quantitative core is real-valued finite sums in the shared 4.35 project, ledger-gated.
   - Nothing was vendored: the Atlas repos have no TV or hockey-stick material; TestingLowerBounds is a
     correspondence target.
   - Cedar (pinned `3f51c8f7`) is planned for a later action-layer step; Veil was rejected (sorry-based SMT trust).
2. **DESIGN.md v1.** The model, the full assumption list (TRUSTED-COMPONENT / MODELLING / STANDING) and the theorem
   list. v0 was hostile-reviewed *before* any Lean (Reviewer A: "reject as spec"; Reviewer B: "major"), and every point is
   dispositioned in §8.
3. **Verified CIDs** (ledger harness, `pl headline` OK; two foreign red-team passes each, no overrides; standard axioms):
   see the table below.
4. **STACK.md.** Maps each guarantee to its assumptions and to real protocols, and lists what is still unproved.
5. **Honest significance and next step:** below. The final review is in `reviews/final-review-{Reviewer A,Reviewer B}.md`.

## Verified results
| CID | plain-English guarantee | proof |
|---|---|---|
| UMHSF1 | hockey-stick pass bound (attained), TV bound, kernel DPI, content factorisation, exact and approximate decoder floors, perturbation, maximal-leakage floor (attained), domination from class coverage | 348 lines |
| UMSURVF1 | honeypot-test survival depends only on the pass rate h; binomial CDF / (1−κh)^n; h·S ≤ (n_s+1)/(n_h+1), and ≤ n_s/(n_h+1) for soft slack | 200 lines |
| UMPROTF1 | **for every colluding pair** (shared seed, stateless monitor, adaptive generator): P(uncaught catastrophe) ≤ (1−r) + r·L·(n_s+1)/(n_h+1) when bad views are L-dominated by mediated honeypots (also hockey-stick and soft forms); the first bad submission decides; one-shot attainment | 276 lines |
| UMSTRATF1 | stratified honeypots with class-aware shutdown: ≤ (1−r) + r(s_c+1)/(m+1), with no class-count factor; attained by a decodable colluder | 218 lines |
| UMNOGOF1 | a content-preserving mediator with k decodable bad classes: **one deterministic colluder** beats every iid honeypot law, every shutdown schedule and every budget, with probability ≥ (1−1/k)^{n_h}; exact attainment curve | 244 lines |
| CANONF1 | a verified canonicaliser for a toy imperative language: semantics preserved; unique normal form modulo for→while, `;`-association and local renaming; class-agreeing laws give identical mediated laws | 757 lines |
| SANDBOXF1 | the ledger harness sandbox (bwrap mount table): (a) the current policy lets a sandboxed process write the host `~/.elan`, which the gate executes; (b) a read-only-root policy confines host writes to scratch plus declared state directories; (c) the current hiding works at mount level, outside the stated `/proc` boundary | 91 lines |

## Harness work (ledger harness)
- `a637fac`, `a08075e`: stack statements may reference transitive dependency definitions (check_statement, gate,
  auto_probe, red-team prompts); `tests/test_deps.py`.
- `6ea98c5`: red-team verdicts are bound to the reviewed statement hash. A stale Reviewer C verdict after a restate had
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

Prompt: `<research-root>/ledger harness/prompts/next-session-control-stack-2.md`. Nothing was sent to anyone, and nothing was
deployed. Mid-session, John shared an external critique and a list of prior art. Both are recorded with their
disposition in `reviews/external-critique-2026-10-07.md` and `reviews/related-work-2026-10-07.md`.

## Delivered
| item | status | notes |
|---|---|---|
| SANDBOX2F1 (corrected sandbox fix) | **verified** (frozen 094db3d3379a) | state binds before the hiding tmpfs; hiding holds for every choice of state directories. Not deployed |
| UMLOWERF1 (converse for nonadaptive designs) | **verified** (frozen 8415ec049329) | restated after both red teams flagged that the colluder was chosen after the design; the proof was adapted |
| VCVio operational refinement | **proved** (394 lines; not ledger-gated) | the trace-level ProbComp game equals `catG` exactly; the protocol factorises; the end-to-end bound and attainment are in-project |
| UMUSEF1 (usefulness companion) | **verified** (frozen 61a4c0bdf711; 573 lines) | v1 rejected (false κ conjunct; PH ⊆ Bad mismatch); v2/v2.1 add the view-blind pair, the obstruction q·u ≤ D·X, Cantelli for both tails, the honest ROC and the b = 0 sharpening |
| UMDEFERF1 (audit-then-defer) | **verified** (frozen ad82ec06fc48; 714 lines) | v1 got major from Reviewer A; v2 → v2.1 adds the service-dependent catV with a reachable conditional floor, the finite retry certificate, the protocol certificate and the no-go for every two-point honeypot law |
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

## SC-03 remote egress CI — 2026-10-08

Private branch `egress-r10-controls` pushed at `b30177e`.
[Egress CI](https://github.com/jwcodes12/control-stack/actions/runs/37784398180) passed both jobs: 62/62 full controls, three
mutations, nine oracle regressions and six Lean axiom checks. Downloaded outcome
artifacts confirm 1,454 kernel-counted packets and zero drops in full mode; all
three mutation receipts also have zero drops. Existing fast/auditgate checks
passed; the covert-channel Lean job is still running as of this entry.
General attribution remains unresolved; gateway/sandbox integration in the isolated
outer topology is the next engineering step. Auditgate source is unchanged.
