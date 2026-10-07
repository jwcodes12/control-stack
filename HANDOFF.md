> **ROADMAP.md** (added 2026-10-07 at John's request) is the one-page status plan: completed / in flight / next / open
> assumptions / needs John. Keep it current whenever a row changes status, and mirror it into the GitHub export.

# HANDOFF: control stack, state at end of session 2 (2026-10-07, ~07:30 UTC)

> **Update 2026-10-07 (session 5 continuation):** Current roadmap is in `ROADMAP.md`. Processed the LASR audit2 score archive into simultaneous rational ROC bands and a 100-step/two-coin table; `checkRiskQ`, `checkLawfulQ`, and a TMCERTF1-derived all-Red risk bound pass `decide +kernel` with standard axioms. This is not deployment evidence because the sample design/match is unestablished. `ControlStack/SoftSlack.lean` proves the constant-hazard soft-slack honeypot survival bridge; end-to-end soft slack remains open. Added `COMPOSITION-N1-UMPROT.md`; no joint theorem is claimed yet. TMLIPF1 is a local draft with passing local claim/witness gates; external red-team transmission is awaiting explicit user approval. The anonymised private export is refreshed with these updates.

> **Update 2026-10-07 (session 6 continuation):** `DeferGame.lean` proves the VCVio operational game equals an exact `ENNReal` recursion; calibration to the real-valued ledger `catV` is still open. `AdaptiveBalance.lean` and `AdaptiveSharp.lean` prove the balanced-count and weighted-path aggregation cores; the adaptive tester's all-FLAG path measure remains to be connected. The local TMLIPF1 red-team dispatch failed in the sandbox, and automatic review rejected an escalated send to OpenAI/Google; no verdict was recorded. Await explicit destination approval before retrying that external review. See `SESSION.md` and `ROADMAP.md` for current status.

> **Update 2026-10-07 (~19:22 UTC):** The adaptive sharp-converse path measure is now connected to the campaign's actual survival and uniform-seed catastrophe sum in `proofledger/campaigns/UMADAPT/forms/UMADAPTF1/proofs/sharp-conv-port.lean`. The direct frozen-statement gate assembly passes, and `conv_a_sharp` uses only standard axioms. No gate event or statement change was recorded. The sharper theorem remains auxiliary pending a decision to register a separate campaign statement; see ROADMAP.md and SESSION.md.

Read this first in a fresh session, then STACK.md (status and positioning; revised after two final reviews),
DESIGN.md v1 (model and assumptions A1–A11) and SESSION.md (what happened). Reviews of this session:
- `reviews/final-review2-{sol,sonnet}.md`;
- `reviews/external-critique-2026-10-07.md` (John shared it; with its disposition);
- `reviews/related-work-2026-10-07.md`.

## Status: nothing in flight
- **Verified this session** (each passed a hash-bound Sol-high + Flash red team, the proofledger gate with standard
  axioms only, and a fidelity audit; `pl reverify` gives 46/46 ok):
  - SANDBOX2F1 (corrected sandbox fix; model theorem; not deployed);
  - UMLOWERF1 (converse for NONADAPTIVE joint test designs);
  - UMUSEF1 (honest availability identities, and the mimicry constraint α₀·u ≤ X for nonempty Bad and N ≥ 1);
  - UMDEFERF1 (audit-then-defer with a reachable conditional stopping floor; finite retry certificate; two-point
    no-go).
- **VCVio, not ledger-gated:** `ControlStack/RefinementProof.lean` (394 lines). The trace-level game equals `catG`
  exactly; the protocol factorises; the end-to-end bound and attainment hold. This is operational adequacy for an
  abstract game, not a deployed scaffold.
- **Total:** 11 control-stack CIDs verified (UMHS, UMSURV, UMPROT, UMSTRAT, UMNOGO, CANON, SANDBOX, UMLOWER, SANDBOX2,
  UMUSE, UMDEFER), plus the VCVio Spike, HoneypotBridge and Refinement files.

## Blocked on John: choose the next direction
The two final reviews agree on the ranking.
- **(A) Rescoped (recommended).** A certificate checker for a finite stateful trusted-monitoring model, with explicit
  adversary observations and uncertainty in the conditional transitions.
  - Soundness: for a fixed Blue controller, a valid risk certificate bounds the catastrophe probability for EVERY
    admissible history-dependent Red and every admissible transition model; a separate certificate lower-bounds
    honest useful reward.
  - First instance: Games for AI Control (2409.07985) Prop 4.1. Note that GAC's Red is memoryless with a fixed β;
    show exactly when that is without loss of generality, and give a counterexample when Red sees more.
  - Reuse N1b's dual certificates.
- **Cheaper precursors** (Sonnet), cheapest first:
  1. A certificate form for UMPROT/UMSTRAT: if binCDF(n_h, n_s, t)(1 − r + r·min(1, L t)) ≤ U for all t, then
     risk ≤ U. The DESIGN §5 numerics then become Lean-checked rational certificates; this also makes the AOQL
     two-sidedness explicit.
  2. The adaptive-tester converse t(1 − t n/k) (identical-until-bad).
  3. An outcome-valued operational game (completion, catastrophe, caught, test rejection, halt), which closes the
     honest-completion bridge.
- **(B) Ranked last.** Port SOUNDGATE's gate. Complete mediation alone does NOT imply A4/A5/A11; it would need the gate
  plus a verified protocol driver plus an execution-order contract.

## Key findings to carry forward (corrected wording)
1. **Coarse views.** Capability-free collusion safety needs a coarse view.
   - The numerical scenario (DESIGN §5; r = 1; honeypot-test false shutdown ≤ 10%; n_h ≤ 100) needs risk ≲ 0.1, an
     honest miss rate α₀ ≲ 0.01 and k ≲ 4–8 Red-choosable classes.
   - Rich content-preserving mediators lose against every iid honeypot law (UMNOGOF1).
2. **Budget scaling (order of magnitude).**
   - Lower bound: every NONADAPTIVE design (UMLOWERF1); adaptive testers can beat that formula.
   - Upper bound: under UMSTRATF1's hypotheses (content-only mediator, coverage, class-aware slack).
   - At L = 1 the honeypot term (n_s+1)/(n_h+1) is tight within a factor ≤ e. This is the honest-free AOQL floor
     max_h h·binCDF(n_h, n_s, h) of acceptance sampling (Dodge–Romig).
3. **Absolute bounds.** The upper bounds are absolute risk bounds. Always-FLAG has worst-case risk 1 − r (nonempty
   Bad, N ≥ 1, b ≥ 1); the honeypot term bounds the excess over that worst case.
4. **Where capability re-enters:** through L (coverage), r (audit recall), α (incrimination floor), the scaffold
   (A1–A4, A11) and the model class. A stateless fresh-context monitor is load-bearing: a call-counting monitor
   reaches risk 1.
5. **Protocol semantics.**
   - Catching an attack must be absorbing shutdown (A11).
   - Deferral keeps the honeypot guarantee only with a uniform conditional stopping hazard θ, at a cost of up to 1/θ.
     Without one, a horizon-tuned burn-then-attack colluder reaches risk → 1 (free submission, no benign-flag guard).
   - In a safety-only model, halting dominates deferral.
6. **Prior art.** Claim only "machine-checked worst-case probabilistic bounds for UM with honeypots; no comparable
   artifact found in this search". Never claim a first Lean formalisation of control protocols. Neighbours: GAC,
   Ctrl-Z App. E, LASR App. B, Roger–Shlegeris toy models, Shlegeris win/continue/lose, Alignment Contracts,
   SOUNDGATE.
7. **The harness sandbox (dispatch.py) mounts a writable host root** (SANDBOXF1).
   - The corrected fix is SANDBOX2F1 (read-only root; state binds BEFORE the hiding tmpfs).
   - Hidden FILES are not modelled: `~/.codex/history.jsonl` needs its empty-file bind after the state binds.
   - Not deployed. It needs John's OK, a CLI compatibility test and `--unshare-pid`.

## Where things are
| what | where |
|---|---|
| programme repo (docs, numerics, proofs, reviews, tools) | `~/research/control-stack` (git) |
| second Lake project (Lean v4.34.0 + VCVio `9146f78c`); NEVER make a third | `~/research/control-stack` itself |
| shared Mathlib project (v4.35.0-rc3), where the ledger gate compiles | `~/research/alignment-contrib/lean/StabilityDebate` |
| ledger, campaigns, harness | `~/research/proofledger` (git); campaigns UMHS UMSURV UMPROT UMSTRAT UMNOGO CANON SANDBOX UMLOWER SANDBOX2 UMUSE UMDEFER |
| frozen statement sources | `control-stack/ledger/*.lean` (`ledger-drafts/` holds superseded versions) |
| gated proofs (copies) | `control-stack/proofs/<CID>.lean` |
| fidelity audits | `control-stack/fidelity/<CID>.md`, copied to `campaigns/<C>/forms/<CID>/fidelity-orchestrator.md` |
| VCVio level | `control-stack/ControlStack/{Spike,HoneypotBridge,HoneypotBridgeProof,Refinement,RefinementProof}.lean` |
| tools | `control-stack/tools/` |

The tools:
- `mkprover.py <CID>`: sets up an isolated prover directory in `/var/tmp/opus-provers/<CID>`;
- `trygate.py <CID> <proof> claim|witness`: a dry-run gate that records nothing;
- `trystmt.py <CID> <file> <deps,comma>`: a statement check.

## Process that worked this session
1. Brute-force first, in exact `Fraction` arithmetic, mirroring Lean semantics: ℕ subtraction truncates and
   `choose n j = 0` for j > n.
2. Run a hostile design review (Sol xhigh plus a Sonnet subagent) before any red team. Both caught real errors (a
   false κ conjunct; PH ⊆ Bad; an uncharged audit resource).
3. Red team with sol-high and flash. Verdicts are hash-bound, so every restate needs a fresh red team.
4. Isolated Opus prover subagents. Give them the plan from the reviews, and tell them to write proof.lean early and
   grow it, so progress survives interruptions (a usage limit killed one prover once).
5. Gate, fidelity audit, STACK row, commit. Then `pl reverify` and the final reviews.

## Gotchas
- **Gate:**
  - the raw-text scanner bans `prefix` and `import`, even in comments;
  - witness defs that use ℝ division need `noncomputable`;
  - `pl restate` needs `--actor`;
  - red-team `fixed_lean` files often inline the dependencies with `import Mathlib`, so take only their deltas.
- Statements may reference dependency definitions (`deps` in form.json). Provers cite `PLDep_<dep>.claim`; write
  `PL_<cid>.Claim` explicitly.
- **Box limits:**
  - 2 cores and 14 GB: at most 2 concurrent Lean compiles;
  - the Claude subagent usage limit hit at about 04:40 UTC and reset at 05:10 UTC; resume the agents with
    SendMessage, since their context survives.
- **VCVio:** the `Pr[…]` notation is deprecated at the pinned commit (warnings only).
- **Never deploy the sandbox change, and never send anything to anyone, without John.**
