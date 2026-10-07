# Fidelity audit (orchestrator): UMUSEF1, the usefulness companion

Statement: `ledger/UMUSE.lean` v2.1 (frozen 61a4c0bdf711). Proof: 573 lines (isolated prover agent), gated, standard axioms. Depends on UMPROTF1 and UMSTRATF1 (and UMHSF1, UMSURVF1).

History:
- **v1** was rejected by both design reviewers.
  - Reviewer A found a false conjunct: the mimicry inequality fails for κ ∉ [0,1]; counterexample κ = 3.
  - Both reviewers found that the mimicry floor needs PH ⊆ Bad, while the design puts PH on a superset B̄.
  - Its "Pareto" conjunct only restated earlier results.
- **v2** adopted both reviews: the view-blind pair; the usefulness-target obstruction; Cantelli in both tails; the
  honest ROC (Reviewer B); the b = 0 sharpening; the class-aware identity; valid schedules; "honest completion".
- **Red team.** On v2, Reviewer A said revise: (b') lacked `IsRule φ₀`, plus four docstring overstatements (the
  mixture-convexity claim was false: concave at N = 2, b = 0). Reviewer C passed. On v2.1, both passed (hash-bound).

| element | classification | note |
|---|---|---|
| `haltP` | MODELLING (same protocol as `cat`) | Both reviewers checked it against `cat` (cat + halt + caught + clean = 1 on 300 instances). A bad PASS and a bad audited FLAG are not halts, so r is correctly irrelevant. The (b+1)-st flag halts |
| benign iid law `μ`, supported off Bad | MODELLING (honest stream) | `μ` is a law on submissions, not tasks. A rate shared across rounds is not covered, and its effect can go either way (docstring) |
| honest rule `φ₀`, α₀ = missRate, f₀ = flagRate | SOURCE: a nominated reference rule | these are capability statistics of φ₀, not trusted quantities. The honest half is NOT capability-free (docstring) |
| `honestCompletion` = surv × (1 − haltP) | MODELLING | full-run availability, not the literature's task usefulness. It is a product by the structure of the recursions; the operational bridge is the VCVio refinement (for `cat`). Benign audits have no false positives |
| (a), (b), (b') | SOURCE: exact identities | P(Bin(N, f₀) > b); survH(α₀)·binCDF(N, b, f₀); the class-aware product of per-class CDFs, with class-specific α_e |
| (c') view-blind exact value | SOURCE | no PH-support hypothesis, b = 0 included; at b ≥ 1 it is UMPROTF1's T3* with a constant rule |
| (P) D·risk = q·completion, hence q·u ≤ D·X and α₀·u ≤ X | SOURCE: the Pareto content | instantiates any universal certificate X at the view-blind pair. Reviewer A checked that the completion hypothesis is load-bearing (dropping it gives 1/2 ≤ 1/3) |
| (d), (d') Cantelli, both tails, hypothesis-free (max 0) | classical infrastructure | the ε-form is division-free; the √ corollary in prose needs ε < 1 |
| (f) 1 − f₀ ≤ e^η α₀ + hs_η(M·μ, M·P_H) | SOURCE: UMHS T2 applied | it is the only coupling of the honest rates through trusted components; it is conditional on μ and φ₀. Data processing only raises the floor 1 − TV |
| (g) b = 0: risk ≤ L(n_s+1)/(n_h+1) | SOURCE | removes UMPROTF1's spurious 1 − r at b = 0 |

**Reading.**
- A protocol whose honest completion is ≥ u cannot certify risk below u × (q = the honest monitor's own honeypot
  miss rate, plus audit failures when b ≥ 1). The bracket is tight only at L = 1 or at large n_h.
- With (f), the floor is driven by trusted components: α₀ + f₀ ≥ 1 − TV(M·μ, M·P_H).
- Numerics (`numerics/umuse_frontier.out`, corrected after Reviewer A: designs separated, grid sups labelled) show the
  decision-relevant gap at matched honest false shutdown ≤ 10%. With k = 8 and α₀ = 0.05, risk is about 0.38 for a
  global counter and 0.05–0.06 for class-aware slack at n_h ≥ 10³, against the floor α₀·u ≈ 0.045.

**Witness.**
- An asymmetric (α₀ = 9/40, f₀ = 13/40) blurring-mediator instance with L = 1. Reviewer A proved the whole Witness in Lean
  during its red team.
- The ideal honest rule attains the ROC bound (f) exactly: 3/4 = 1/4 + 1/2.

**Novelty.**
- The safety/usefulness framing is Games for AI Control's (2409.07985) and Greenblatt et al.'s.
- "Safety is bounded by honest ability" is in LASR App. B.3.
- The inequalities are classical (Cantelli 1928; Neyman–Pearson / hockey-stick).
- Calibrated: infrastructure. The value is closing the always-flag loophole in Lean, on both sides of the same
  recursions.

**Scope notes (Reviewer A, final review 2).**
- (P) requires a bad x and N ≥ 1. At N = 0 or with Bad = ∅, every pair has zero risk while completion can be
  positive, so the obstruction does not apply.
- α₀ is the honest rule's honeypot TEST-PASS rate. It is a backdoor miss rate only if the honeypot law has that
  meaning.
- (P) is a necessary constraint on universal certificates at an availability target. It is not a Blue optimisation,
  Pareto or feasibility result.
- The frozen docstring's sentence "The operational bridge for both is the VCVio refinement" overstates. The VCVio
  game proves the catastrophe correspondence only; honest completion (`haltP`) has no game-level correspondence yet.
