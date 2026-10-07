# HANDOFF: control stack, state at end of session 2026-10-07

Read this first in a fresh session, then STACK.md (status), DESIGN.md v1 (model and assumptions) and SESSION.md (what
happened). The next-session prompt is `~/research/proofledger/prompts/next-session-control-stack-2.md`.

## IN FLIGHT (session 2, 2026-10-07 from ~03:00 UTC; updated ~04:05)
- DONE this session:
  - SANDBOX2F1 verified (frozen 094db3d3379a) and UMLOWERF1 verified (frozen 8415ec049329).
  - **VCVio refinement proved** (`ControlStack/RefinementProof.lean`, 394 lines, standard axioms): the deploy game
    equals `catG` exactly; the protocol factorises; the end-to-end bound; attainment; witness.
  - External critique and a related-work audit (`reviews/external-critique-2026-10-07.md`,
    `reviews/related-work-2026-10-07.md`); STACK.md has a prior-art and positioning section.
- **UMUSEF1 (campaign UMUSE).** v2 drafted after the Sol xhigh and Sonnet design reviews (v1 was rejected: the κ
  bound was false; the mimicry floor needed PH ⊆ Bad).
  - Sol-high red team: revise, minor (`IsRule φ₀` in (b'), docstring fixes). v2.1 with the fixes is in
    `ledger/UMUSE.lean` and compiles.
  - Next: read the Flash verdict; `pl restate UMUSEF1 ledger/UMUSE.lean --actor orchestrator`; re-red-team; prover
    (`tools/mkprover.py UMUSEF1`, then an isolated Opus subagent); gate; fidelity audit; STACK row.
- **UMDEFERF1 (campaign UMDEFER).** v2 after Sol's xhigh review (major: resource accounting, conditional α contract,
  finite retry certificate, false asymptotic prose, prior art from Shlegeris' win/continue/lose).
  - Red team (sol-high, flash) running: log `/var/tmp/redteam6.log`. A Sonnet v2 review is running →
    `reviews/umdefer-v2-review-sonnet.md`.
- **Awaiting John:** whether the next step is the critique's suggested project: Lean-check a Games-for-AI-Control
  trusted-monitoring certificate, which merges with N1b. Alternatives: a SOUNDGATE gate model (turns A4/A5/A11
  into consequences of complete mediation), or the action layer with Cedar.
- Tools:
  - dry-run gate without recording: `python3 /var/tmp/trygate.py <CID> <proof.lean> claim|witness`;
  - statement check: `/var/tmp/trystmt.py <CID> <file> <deps,comma>`.

## Where things are
| what | where |
|---|---|
| programme repo (docs, numerics, proofs, reviews) | `~/research/control-stack` (git) |
| second Lake project (Lean v4.34.0 + VCVio `9146f78c`); NEVER make a third | `~/research/control-stack` itself (`lakefile.lean`, `.lake/`, 8.5 GB + 3.0 GB toolchain) |
| shared Mathlib project (v4.35.0-rc3), where the ledger gate compiles | `~/research/alignment-contrib/lean/StabilityDebate` |
| ledger, campaigns, harness | `~/research/proofledger` (git); campaigns UMHS UMSURV UMPROT UMSTRAT UMNOGO CANON SANDBOX UMLOWER SANDBOX2 |
| frozen statement sources | `control-stack/ledger/*.lean` (`ledger-drafts/` holds superseded versions) |
| gated proofs (copies) | `control-stack/proofs/<CID>.lean` |
| fidelity audits | `control-stack/fidelity/<CID>.md`, copied to `campaigns/<C>/forms/<CID>/fidelity-orchestrator.md` |
| hostile reviews | `control-stack/reviews/` (design-review-{sol,sonnet}.md; final-review-{sol,sonnet}.md) |
| VCVio interface level | `control-stack/ControlStack/{Spike,HoneypotBridge,HoneypotBridgeProof}.lean` |
| prover setup script | `/var/tmp/mkprover.py <CID>` (it may not survive a reboot; it is also copied into `control-stack/tools/mkprover.py`) |

## Status
- **Verified (9 CIDs; check `pl status`):**
  - UMHSF1, UMSURVF1, UMPROTF1 (main theorem), UMSTRATF1, UMNOGOF1 and CANONF1 (verified canonicaliser);
  - SANDBOXF1 (the harness bwrap root is writable, in the model);
  - UMLOWERF1 (design-free converse) and SANDBOX2F1 (corrected fix).

  All of them re-verify (`pl reverify`).
- **VCVio (not ledger-gated):** the T1 spike and the honeypot-test bridge are proved, with standard axioms.
- **Final review verdict** (Sol xhigh, Sonnet): sound and modest; nothing "apparently open". STACK.md is rescoped as
  "strategy-free guarantees conditional on explicit trust hypotheses". The bounds are one-sided: they bound the
  adversarial gain over an always-flag protocol, and usefulness is not in Lean.

## Key findings to carry forward
1. **Capability-independent collusion safety needs a coarse view.** It is non-vacuous only when few Red-choosable bad
   classes survive mediation: k ≲ 4–8 at realistic n_h ≤ 100.
   - Content-preserving rich mediators lose against every iid honeypot law (UMNOGOF1).
   - The likelihood-ratio constant is at least the exponentiated maximal leakage (UMHSF1).
   - With UMLOWERF1 and UMSTRATF1, risk = Θ(k(n_s+1)/n) for every honeypot design.
   - So the **critical path runs through the action layer**: make badness structural, so that k is small by
     construction.
2. **Two parity hypotheses carry the weight, and they are where capability re-enters:**
   - L: honeypots, after mediation, cover every attack U could produce;
   - r: audits catch U's attacks.
3. **Protocol semantics matter.**
   - Deferring without incrimination voids honeypot guarantees (retries); this is shown in numerics only.
   - Catching an attack must be absorbing shutdown (A11).
4. **The harness sandbox (dispatch.py) mounts a writable host root.**
   - The fix needs read-only root plus scratch plus state directories, with the state binds placed BEFORE the hiding
     tmpfs mounts (SANDBOX2F1).
   - Not deployed. It needs John's OK and a CLI compatibility test, plus `--unshare-pid` for the `/proc` boundary.

## Next steps, in order (formal work only; no GPU work)
1. **Usefulness companion lemmas.** Honest false-shutdown = 1 − S_κ(α₀); false halt = P(Bin(N, f₀) > b). Then a
   safety/usefulness Pareto statement. Small.
2. **Operational refinement theorem (VCVio).**
   - Define the protocol as a trace-level `ProbComp` game with an audit kernel (conditional recall ≥ r), absorbing
     shutdown and halting.
   - Prove Pr[catastrophe] ≤ `protocolCat` with r.
   - Extend the honeypot bridge to the deployment phase.
3. **Defer-to-trusted / rate-test variant.**
   - Either prove first-bad-decides under an incrimination condition, or prove the exact retry value
     sup_h S(h)(1−(1−h)^K).
   - This decides applicability to the protocols labs run (Greenblatt, LASR, Ctrl-Z).
4. **Action layer proper.**
   - A reference monitor for agent tool calls, with Cedar pinned at `3f51c8f7` (v4.34.0, Batteries only) in
     control-stack.
   - A structural catastrophe set B̄ (a finite catalogue of dangerous effects), plus reachability theorems.
   - The bridge to layer 1: a structural mediator with provably small k.
5. **Integrate trusted monitoring** (N1/N1b in `~/research/control-tree/lean/ControlTree.lean`) into the stack's
   encoding, then a first composition theorem. It is a min, unless conditional independence is proved.
6. **Later:** verified implementations of the mediator and scaffold (Aeneas/hax on a Rust core).

## Gotchas
- **Gate (proofledger):**
  - The raw-text scanner bans the word `prefix`, even in comments.
  - Witness defs that use ℝ division need `noncomputable`.
  - `pl restate` needs `--actor`.
- **Red-team verdicts are hash-bound since commit 6ea98c5.** Verdicts from processes started earlier are unbound: after
  a restate, re-restate to clear them.
- **Statements may reference dependency definitions** (`deps` in the form JSON). Provers cite `PLDep_<dep>.claim` and
  the dep's helper lemmas. `open` of dependency namespaces makes `Claim` ambiguous inside proofs; provers write
  `PL_<cid>.Claim`.
- **Box limits.** 2 cores and 14 GB: at most 2 concurrent Lean compiles. Sonnet subagents hit a session usage limit
  once (it resets at 00:00 UTC). Do not write random-program generators in Lean `#eval` inside `import Mathlib` files
  (elaboration hit 13 GB); mirror the definitions in Python.
- **VCVio.** The `probOutput`/`probEvent` notation is deprecated at the pinned commit (only warnings).
  `probOutput_true_add_false` and `probOutput_bind_eq_sum_fintype` are not reachable from the minimal imports.
- **Never deploy the sandbox change, and never send anything to anyone, without John.**
