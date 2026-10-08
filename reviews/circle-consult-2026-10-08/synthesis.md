# "Complete the circle" consultation: synthesis and disposition (2026-10-08)

Two independent adversarial consultations on the same prompt (`prompt.md`), both read-only on `eb0200e`:
- Astra: `gpt-6-astra`, reasoning xhigh, `codex exec -s read-only` → `astra-review.md`.
- Fable: `claude-fable-5-1` via a Claude Code subagent → `fable-review.md`.

## Where they agree (adopted)

1. **Do not build the general `ControlCert` calculus now.** Its combinators are classical: the cardinality guessing
   bound, maximal leakage (Issa–Wagner–Kamath) and its additivity, hazard products, and sampling without replacement.
   Lean typing makes them checked, not new. Global "calculus completeness" cannot even be stated yet, because each file
   quantifies over a different adversary class and failure event. Per-combinator tightness does not compose.
2. **There is no cross-component adaptive composition theorem today.** `dom_pi` assumes no feedback between episodes,
   which a page cache violates. `AuditBudget` fixes the attack set; its adaptive reduction is only a comment.
   `MultiStep` hazards cannot be fed by marginal ROC data (`correlated_nogo`).
3. **The necessity catalogue must be relabelled narrowly.** Each witness shows that one specific strengthening fails,
   not that the assumption is necessary for the bound. Several assumptions have no witness: secret independence,
   independent lifetimes, the fresh-coins premise of `ComposeGame`, the naive audit × monitor product, and lineage
   completeness.
4. **The value lies in conditional accounting, refutation and experiment design, not positive guarantees.** The best
   existing demo is `bit_refutes` → the cache probe → HYPOTHESIS_REFUTED.
5. **N = 100 vacuity has two causes.** In LASR/BigCodeBench it is statistical margin, fixable by design and data. In
   LinuxArena it is the protocol: a deferred attack is not incriminated, so the risk compounds, and no sample size fixes
   it. A tool should diagnose which regime applies.
6. **The formal-veneer risk is concrete.** `tools/check_sc01_case.py` prints "All checks passed" and exits 0 even when
   the verdict is HYPOTHESIS_REFUTED. Outputs must separate proof validity, evidence validity and case applicability, and
   must never print a bare bound.
7. **Most likely "true but useless" outcome:** a correct tiny exact-recovery bound while one permitted bit says "attack
   now" (`one_bit_coordinates`), or while the real host gives the receiver more than the transcript.
8. **Ceiling:** at best, a machine-checked accounting layer for narrowly specified protocols. It removes arithmetic and
   composition errors, prices adversary information, names a refuting experiment for each premise, and records no-go
   results. It never certifies the physical boundary, coverage of an unrestricted attack space, or harm beyond the
   proxy. Much of its practical value is in *preventing* unjustified positive conclusions.

## Where they differ

- **The one theorem to fund.**
  - Fable: adaptive (feedback) composition of side-kernel certificates, which replaces `dom_pi`'s independence
    assumption (days).
  - Astra: *leakage-sensitive adaptive auditing*: an attacker that sees a c-dominated side observation Z of the audit set
    survives with probability ≤ min(1, L · C(N−k,B)/C(N,B)), plus a causal-feedback version (2–4 weeks).
  - Disposition: these are the same theorem. Both are instances of one *leakage-transfer* principle: an adversary whose
    information about a hidden variable arrives through c-dominated, history-dependent kernels is worth at most
    mass(c) blind adversaries. Prove it once, sequentially, and derive both.
- **Assumption ledger shape.** Fable proposes a three-way tag. Astra says the tags mix logical provenance, falsifiability
  and evidential status, and wants separate axes. Disposition: use separate axes. The three-way view becomes a derived
  summary.
- **Tool.** Fable: vacuity diagnoser, sample-size calculator, and one Inspect-log bridge. Astra: one portable decision
  tool with no home-directory paths, plus a prospective external-user demonstration. Astra also warns that benchmark
  bridges aggregate per-trajectory maxima, which is not an online catch. Disposition: build one portable tool. Record
  the trajectory-max caveat as an assumption, not a fix.

## Plan adopted for this effort (branch `claude/circle`)

1. **Theory: `ControlStack/Leakage.lean`.** One-shot leakage transfer, then the sequential version with
   history-dependent certificates and hidden state. Instances:
   - covert/side bounds with feedback, replacing `dom_pi`'s independence;
   - SC-01 per-episode mass budget;
   - leakage-sensitive adaptive auditing, where absorbing catch feedback is free;
   - endpoints: hidden schedule = hypergeometric, full visibility = vacuous, consistent with `observable_schedule_nogo`.
2. **Missing witnesses: `ControlStack/Necessity.lean`.** Seed-correlated secret; correlated lifetimes break
   `false_pass_le`; shared-score audit × monitor product unsound.
3. **Honest reporting.** The checker separates proof, evidence and applicability, and is never "passed" when refuted. A
   multi-axis assumption record replaces the single status, and the necessity catalogue gets narrow labels.
4. **Researcher tool.** A portable CLI covering the regime diagnosis (margin vs protocol vs monitor), sample-size and
   budget calculators, the leakage-sensitive audit calculator and refutation thresholds. Every number is printed with its
   conditions.
5. **Write-up.** Headline the negative and refutation results; cite IWK 2020, Greenblatt et al., Griffin et al.,
   Ctrl-Z, Mallen et al. and Korbak et al. Claim no priority for the mathematics.

Out of scope for now: the general calculus, bridges for all three benchmark suites, a Python↔Lean refinement proof,
and racing VM isolation to reinstate 2^-16.
