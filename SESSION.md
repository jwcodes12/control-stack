> **SESSION 3 STATUS (2026-10-07, updated ~14:30 UTC): Sonnet's three precursors are DONE.**
> 1. UMCERTF1 **verified** (frozen 73c2633b1568; 750 lines): one-shot reduction, envelope + grid certificates, AOQL floor,
>    exactness at L = 1, for decodable content-only mediators (Xp) and for the stratified design (S2).
> 2. UMADAPTF1 **verified** (frozen a416cc05f830; 484 lines): adaptive converse t·max(0, 1 − tn/k); the nonadaptive
>    UMLOWER formula fails for adaptive testers pointwise (c1) and after optimisation (c2).
> 3. Outcome-valued VCVio game **proved** (`ControlStack/OutcomeProof.lean`, 512 lines): five-outcome law, honest-completion
>    bridge to UMUSEF1, Pareto identity.
> Direction (A): TMCERT v0 got MAJOR from both reviewers; split into TMCERT v1 (core checker: soundness vs history-dependent
> Red and rectangular nature, fixed-model corollary, tightness, usefulness, rational checker, vertex lemma, abstraction
> theorem) and TMGAC v0 (GAC instance: bridges to Prop. 4.1 and usefulness, separation 13/50 vs 11/32); second design
> review running. John asked to publish to a PRIVATE GitHub repo `control-stack` (sandbox results generalised; model
> names anonymised); export being prepared in /var/tmp/cs-export. Routine `trig_01RsgfEAcQ1rDt5TZLo2tLMp` (every 2h).

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
