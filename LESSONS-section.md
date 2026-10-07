## Round 7 (2026-10-07): a Lean-verified, capability-free control stack, collusion layer (this repository)
- **Goal shift worked.** The bar was "correct, used in the stack, Lean-verified", not novelty. With classical lemmas
  allowed as infrastructure, the campaign produced 7–9 verified CIDs in one session (UMHS, UMSURV, UMPROT, UMSTRAT,
  UMNOGO, CANON, SANDBOX, plus UMLOWER and SANDBOX2 at close); see STACK.md for final status. Every one passed two
  foreign red teams with **no overrides** (the programme owner's override was never needed). There were also two VCVio bridge
  results, not ledger-gated.
- **The final hostile review still matters when every statement is verified.** Both reviewers found no false or
  vacuous Lean, but 11+ MAJOR overclaims in the plain-English STACK rows:
  - "capability-free" hides two parity hypotheses, L and r;
  - the bounds are one-sided (an always-flag protocol satisfies them);
  - the coarse-regime caveat was missing;
  - the LASR/Python claims were overextended;
  - a regression in my own proposed sandbox fix.

  Rule: verified ≠ correctly described. Review the prose against the frozen text.
- **Calibrated significance.** Novelty is known/classical/modest; nothing is "apparently open". The decision-relevant
  output is structural:
  - capability-independent collusion safety needs few Red-choosable classes in the monitor's view;
  - honeypot budget per class is necessary and sufficient, Θ(k(n_s+1)/n);
  - the critical path is the action layer.
- **Design review before Lean was decisive again.**
  - Reviewer A rejected DESIGN v0 as a spec ("reject"); Reviewer B gave "major". All core inequalities were true. The failures
    were definitional:
    - L by division;
    - halt semantics;
    - retraining ≠ shutdown;
    - task selection;
    - an unsupported summariser floor.
  - Reviewer B contributed three better theorems:
    - the maximal-leakage floor;
    - stratified class-aware tests (no k factor);
    - the exact Neyman–Pearson value.
  - v1 was formalised; no v1 statement was found false.
- **Realistic parameters change the story.** Honeypots cost human points (n_h ≤ 30–100). The v0 table used
  n_h ≥ 1000. At real budgets a capability-free collusion bound ≲ 0.1 needs ≲ 4–8 Red-choosable bad classes surviving
  mediation.
- **Reuse.**
  - VCVio built cleanly in its own project (5.4 min fetch, about 4 min compile, 11.5 GB) and gives a two-line T1.
  - But its probability API is mid-deprecation and is `ℝ≥0∞`/tsum based. Real-valued finite sums in the shared
    project were the right core.
  - Neither Atlas repo nor Mathlib has TV or hockey-stick; TestingLowerBounds does, but measure-theoretic.
- **Harness bugs found by doing real stack work:**
  1. Dependent statements could not reference dependency definitions. Fixed: transitive dependency statements are
     now included in statement checks, probes and red-team prompts.
  2. Red-team verdicts were not bound to the reviewed statement, so a stale Reviewer C verdict counted after a restate.
     It happened live; fixed with hash binding and a regression test.
  3. The gate's raw-text scanner bans the word "prefix" even in comments.
  4. A bubblewrap policy that starts from a writable host root (`--dev-bind / /`) lets an untrusted process modify
     toolchain directories that a later, unsandboxed checker executes. Now a theorem about the mount-table model
     (SANDBOXF1(a)), with a proved read-only-root policy (b) and a corrected bind ordering (SANDBOX2F1).
- **Provers.** Isolated prover agents (one directory each plus a check.sh that assembles exactly what the gate
  assembles) proved:
  - UMSURV (200 lines, 3 min);
  - UMHS (348 lines, 5 min);
  - CANON, a full verified canonicaliser (757 lines, 10 min);
  - UMPROT (276 lines, 4 min);
  - SANDBOX (91 lines, 4 min).

  Giving provers a precise mathematical plan in the prompt made every proof land on the first attempt.
- **Lean `#eval` gotcha.** Ad-hoc random program generators written with nested `let`/`match` inside `import Mathlib`
  files blew up elaboration to 13 GB RSS. Mirror the definitions in Python for brute force instead.
