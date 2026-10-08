# Adversarial consultation: "completing the circle" for control-stack

You are a hostile but fair senior reviewer: an AI-control researcher who also knows formal methods and has seen many
"certified safety" projects end up useless. Do NOT sugarcoat. The owner explicitly wants the honest ceiling and the
failure modes, not encouragement. If something is a dead end, say so and say why. Distinguish clearly between what you
verified by reading files and what you are inferring.

## The repo
Read-only checkout: /var/tmp/cs-circle (branch claude/circle = master eb0200e). Lean 4 + Mathlib, plus Python tooling.
Start with: HANDOFF-lean-track.md, ROADMAP.md, REVIEW-PACKET.md, STACK.md, CERTIFICATE-DECOMPOSITION.md,
assurance/sc01-safety-case.json, tools/check_sc01_case.py, numerics/ (benchmark -> certificate pipelines for
ControlArena/LinuxArena/LASR/LaStraj data), and the Lean files in ControlStack/ (read statements, not proofs). Do not
modify anything. Do not run long builds.

Summary of what exists (verify, do not trust):
- Ledger-verified (two-family red team + Lean gate) layer-1 results on untrusted monitoring with honeypots, adaptive
  converses, trusted-monitoring certificate checkers (UMPROTF1, UMADAPTF2, TMCERTF1, TMLIPF1, TMGACF1, ...).
- Newer "proved but not red-teamed" Lean: counting bound for covert channels through a finite-view gateway
  (covert_bound, attain_embedding), side-channel domination certificates (SideChannel: P <= |V| * sum c / |M|),
  SC-01 instance (target 2^-16 tolerates side mass <= 1.11; one clean side bit breaks it), usefulness gate validity,
  lifetime ledger (no-rollback necessary), multi-channel GatewayCore with a differential test vs Python, coverage
  (K, eps) composition for trusted monitors (tight), MultiStep (uniform conditional catch rate => (1-c)^k; marginal
  rate with correlated misses => no-go), AuditBudget (hidden random audit set => hypergeometric survival; observable
  schedule => survival 1).
- A one-command safety-case checker for SC-01 whose current verdict is HYPOTHESIS_REFUTED: a measured shared-cache
  side bit (64/64, lower bound 0.954) forces certificate mass >= 1.909 > 1.11.
- Benchmark-derived certificates (numerics/, CERTIFICATE-DECOMPOSITION.md) where certified risk at N=100 rounds is
  often near 1 because of statistical margins.

## The owner's proposed next effort ("complete the circle")
1. One certificate calculus: a Lean `ControlCert` (protocol, threat class, typed hypotheses, bound) with combinators
   (episodes/lifetimes multiply view spaces; side kernels multiply domination masses; monitor layers compose;
   multi-step uses hazard products; audit budget uses the hypergeometric). "Completeness" = every combinator sound AND
   tight, with an attaining adversary. Plus a "necessity catalogue" showing no assumption can be dropped
   (attain_embedding, repair_one_bit_attained, restore_breaks, varObs_breaks_target, correlated_nogo,
   observable_schedule_nogo, tight_K/tight_eps, ComposeBlindSpot).
2. A typed assumption ledger: each hypothesis is THEOREM, REFUTABLE-BY-MEASUREMENT (with a lemma turning a statistic
   into a certified refutation, like bit_refutes), or TRUSTED-UNTESTABLE.
3. A researcher-facing tool (Python package/CLI): protocol parameters in (channels, budgets, audit B/N, monitor ROC
   bands from the user's eval, attack length k, coverage K/eps) -> certified bound, Lean-checkable certificate, the full
   assumption list, which experiment would refute each assumption, and the parameter change needed to hit a target.
4. Benchmark bridges: ControlArena/LinuxArena/LASR outputs -> certificates automatically.
5. Honest ceiling: the physical boundary cannot be proved; capability-free bounds may be vacuous at realistic
   parameters; the value may be mostly precise accounting plus refutation, not positive guarantees.

## Answer all three parts. Be concrete and cite files/theorems.

### (a) Theory
- Is a "certificate calculus" a real theoretical contribution, or a repackaging of a union bound, a product of
  cardinalities and a Bernoulli hazard product? What would make it non-trivial (e.g. a genuine composition theorem whose
  hypotheses are weaker than the naive conjunction; a completeness/tightness theorem for the whole calculus, not each
  combinator; an impossibility result)?
- Which combinators are actually sound for ADAPTIVE adversaries across components (side channel x monitor x audit
  budget x multi-step), and where does naive composition break? Name the specific missing results (e.g. side channels
  with feedback, audit budget with false positives, joint collusion + side channel). Which ONE theorem would most
  change the picture, and is it provable at reasonable cost?
- Is the "necessity catalogue" honest? For each witness, does it show the assumption is necessary for the BOUND, or
  only that some specific strengthening fails? Are there assumptions with no witness?
- What is novel versus known (information theory: maximal leakage / Sibson, channel capacity with feedback; AI control
  literature: Greenblatt et al., Ctrl-Z, subversion strategies, Griffin et al. games, safety cases by Korbak/Clymer)?
  Be explicit about what is NOT new.

### (b) Researcher applicability (tool, assumption ledger, benchmark bridges)
- Who would actually use the tool, for which decision, and what would they do differently because of its output?
  If the honest answer is "nobody, because X", say so and say what would change it.
- The benchmark certificates are near-vacuous at N=100. Is that a fixable artefact (multiplicity corrections, design)
  or a fundamental property of capability-free worst-case bounds? What output would still be useful when the bound is
  vacuous (e.g. sample-size calculator, "what you would need to measure", refutation)?
- Is "theory says what to measure; measurement returns a refutation or a calibrated parameter" a genuinely useful loop
  for control evals? What is the best concrete demo of it?
- What minimal deliverable would a control researcher at a lab or in academia actually cite or run?

### (c) Honest ceiling, independent of whether specific bounds pan out
- What can this whole programme (theory + researcher tooling) actually achieve at best? Give the ceiling in one
  paragraph, then the three most likely ways it ends up useless or misleading, then the single most likely way it is
  "true but useless".
- Is there a risk that Lean-certified bounds create false confidence (formal veneer over untestable assumptions)? How
  should outputs be framed to prevent that?
- If you had to cut the plan to the 20% that delivers 80% of the value, what is in and what is out?

## Output format
Markdown, at most ~2500 words. Sections: Verdict (5 lines), (a) Theory, (b) Applicability, (c) Ceiling, Ranked plan
(at most 8 items, each with an acceptance criterion and an estimated effort), Things I checked in files (with paths),
Things I am inferring. No praise padding.
