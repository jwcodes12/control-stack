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
