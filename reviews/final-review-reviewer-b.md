# Final hostile review (Reviewer B): fidelity, overclaims, novelty gate, significance

Reviewer: Reviewer B, 2026-10-07. Scope: the seven frozen statements embedded in `final-review-prompt.md`
(UMHSF1, UMSURVF1, UMPROTF1, UMSTRATF1, UMNOGOF1, CANONF1, SANDBOXF1), STACK.md as quoted there, DESIGN.md (read),
`fidelity/*.md` (read, challenged), `numerics/*.py` (read; `realistic_budgets.py` logic re-derived and re-run
in scratch). I did NOT re-check proofs. I did not read `ledger/*.lean`, the proofs, or the harness's sandbox code
(outside the allowed read list), so SANDBOXF1's correspondence to the real code is taken from the orchestrator's table.
Scratch work: `<scratch>/` (`strat_vs_global.py`, `nogo_numbers.py`, `sbx.lean`, `arx.sh`, extracted
LASR/Greenblatt/Ctrl-Z text). Nothing else was written.

## 0. Bottom line

- **No FATAL defect.** I found no Lean statement that is vacuous, mis-quantified in a way that changes its meaning,
  or false-as-read. Every conjunct of UMHSF1/UMSURVF1/UMPROTF1/UMSTRATF1/UMNOGOF1 does what its docstring says, and
  the witnesses are non-degenerate (UMSURVF1's soft witness and UMSTRATF1's padded witness are weak; see below).
- **The problems are in the plain English, not the Lean.** Four MAJOR overclaims or omissions in STACK.md:
  1. "capability-free" is mislabelled: the two load-bearing hypotheses (L, r) are capability-parity hypotheses
     (X1);
  2. the guarantee is one-sided: halting counts as safe, no usefulness theorem exists, and an always-flag protocol
     satisfies every bound (X2);
  3. the verified positive results live in the regime where untrusted monitoring is least needed (coarse mediated
     view), and STACK.md does not say so; one sentence in "Assumptions still unproved" contradicts DESIGN §3 (X3);
  4. "no class-count factor" in UMSTRATF1 is an accounting artefact; at equal honeypot budget and equal slack the
     class factor is back and the exact game values coincide (S1, numbers below).
- **Two MAJOR issues in SANDBOXF1** (a model theorem described as a system defect; the proposed fix
  regresses hiding, shown by a model counterexample using the frozen definitions) plus a scope gap (reads and
  state-directory contents).
- **Novelty**: nothing is "apparently open" as mathematics. UMHSF1, UMSURVF1, UMNOGOF1, CANONF1, SANDBOXF1 are
  known or classical; UMPROTF1 and UMSTRATF1 are elementary assemblies that give the existing informal arguments
  (Greenblatt §3.4.2, LASR App. B/D, Ctrl-Z App. E) a machine-checked, worst-case-over-colluding-pairs form.
  Calibrated label for UMPROTF1: **modest**; for UMSTRATF1: **classical** (elementary corollary), with a modest
  design observation that is not in the Lean.
- **Overall verdict: ACCEPT as verified infrastructure with a conditional, honestly-labelled scope; REJECT the
  current STACK.md wording as a "capability-free guarantee stack".** After the fixes in section 6 it is a sound,
  small, useful formal note. As a research contribution it is modest.

## 1. Cross-cutting issues (apply to several CIDs)

### X1. "Capability-free" is the wrong word for what is proved. MAJOR
Where: the STACK.md title ("capability-free control guarantee stack"), the UMPROTF1 row (bold "**For every
colluding pair**"), DESIGN §0 ("Capability-free: no assumption on what U can do").

Why: what is proved is *strategy-free and computation-free* (information-theoretic): U's monitor and generator are
universally quantified, with unbounded computation, given two hypotheses that are themselves capability-parity
claims.
- **L (A9).** Domination `M x z ≤ L·q z` must hold for **every** bad x that U could ever produce, with q built by
  Blue. This says Blue's honeypot generator spans U's attack space up to a constant L. If U's attacks are subtler
  than anything Blue can synthesise, their mediated views are not dominated and the theorem is silent. This is
  exactly the "honeypot generator is unlikely to be indistinguishable" worry LASR states in its introduction
  (arXiv:2602.20628, introduction) and Greenblatt §3.4.1 treats empirically.
- **r (A6).** Worst-case audit recall over Bad is human/U parity, as the stack says.
- **A1–A4 (scaffold).** Statelessness and "z is the complete input" are enforced by engineering, not provable
  from the model.

DESIGN §0 half-admits this ("exactly as capability-free as the construction of B̄ and P_H") but STACK.md's header and
bold row text do not.

Fix: rename to "strategy-free (adversary-quantified) guarantee conditional on two parity hypotheses". Add a
"who must be trusted for what" column: r = audit parity; L = honeypot generator spans U's attack space;
A1–A4 = scaffold statelessness. Delete "capability-free" from the title.

### X2. The guarantee is one-sided; the bounds do not credit untrusted monitoring at all. MAJOR
Where: UMPROTF1/UMSTRATF1 rows; STACK.md header ("Each row is a machine-checked guarantee").

Why:
- In `cat`, FLAG with no audit available halts and returns 0. So a monitor that flags everything satisfies every
  bound (T3a with A = 0 gives cat ≤ 1−r; survival is 1 because h = 0).
- Every upper bound has the form (1−r) + r·(small), and (1−r) is the value of that useless protocol. UMPROTF1
  therefore bounds **what collusion can add to an always-flag baseline**, not the safety UM buys. Honest-monitor
  usefulness (false shutdown = 1 − S_κ(α₀), false halt = P(Bin(N,f₀) > b)) appears only in DESIGN prose and numerics,
  not in any Lean statement.
- A "control guarantee" in the Redwood sense is a safety/usefulness pair. Half of the pair is not formalised.

Fix: (i) say in each row "bounds the adversarial gain over the always-flag protocol; usefulness not formalised";
(ii) add the companion lemma (honest false-shutdown = `1 − survH α₀ κ nh 0`, false-halt binomial tail). It is two
lines from existing definitions and makes the Pareto statement a theorem.

### X3. The verified positive results sit in the coarse-mediation regime; STACK.md omits this and contradicts DESIGN. MAJOR
Where: STACK.md "Assumptions still unproved", item 1; the UMSTRATF1 row; the UMNOGOF1 row.

Why:
- UMSTRATF1 needs a content-only mediator (`M x = K (c x)` for **all** x) with k small enough that k·m honeypots are
  affordable (DESIGN §5: k ≲ 4–8). Then the monitor's view is a ≤8-valued feature, and a trusted rule on the same
  feature is available. DESIGN §5 ("coarse-regime objection stands, Reviewer A #22/N2: we establish no such value") says
  so. STACK.md never does. A reader of STACK.md sees "verified, every colluding pair" and not "in the only regime
  where the hypotheses are satisfiable, UM's value over a trusted class rule is unproved".
- Item 1 says the domination hypothesis "is false for every honeypot law" for "LLM summarisers, semantics-preserving
  code transforms", citing UMHSF1's floor and UMNOGOF1. Three errors:
  - (a) the floor is `≥ e^ℒ`, finite, not "false" (DESIGN §8 "Reviewer A #9" fixed this wording and STACK.md regressed);
  - (b) LLM summarisers are not exactly decodable, so neither UMNOGOF1 nor T4c applies; DESIGN §3 UMLEAK says "the
    summariser application is **withdrawn** (Reviewer A #7)";
  - (c) the floor refutes only *pure* L-domination; the hockey-stick form (T3 second conjunct) with δ > 0 is not
    touched by `Σ_z max_x`.

Fix: replace item 1 with "for mediators that exactly preserve a k-class feature (identity, canonicalisers,
semantics-preserving transforms) no iid honeypot law gives a useful bound once k ≳ n_h (UMNOGOF1); for noisy
mediators (LLM paraphrase) the pure-L route has constant ≥ e^ℒ and the (η,δ) route is open." Add a one-line
"coarse-regime objection" to the Layer 1 header.

### X4. Fidelity of the recursion to the operational protocol, and to the named protocols. MAJOR (known, but understated)
- The simulation (`numerics/simulate_protocol.py`) checks the recursion against the author's own operational
  description (honeypots, PASS = miss, flag/audit/halt). That is a useful typo check, not a bridge to the named
  protocols. I re-read it: it is a faithful independent sampler of the `cat`/`surv` semantics.
- The halting semantics (flag without budget halts, counted safe) is the strongest possible response and is **not**
  the semantics of any named protocol:
  - Greenblatt audits the top q% by score and executes the rest, with a binomial FPR shutdown;
  - LASR Eq. (1) is a defer-to-trusted "continue" model (Ctrl-Z App. E is similar in spirit);
  - the stack's own numerics (variant D) say the guarantee is voided there.
  The "protocols it speaks to" column should read "a halting idealisation; no named protocol". UMPROTF1's own
  row ("the halting variant of UM") is honest; UMHSF1 ("every untrusted-monitoring protocol") and UMSTRATF1 ("any
  honeypot protocol") are not.
- Greenblatt §3.4 is the right section (verified in the PDF: "3.4 Untrusted monitoring", §3.4.1 making synthetic
  inputs hard to tell apart, §3.4.2 collusion techniques and countermeasures).

Fix: relabel the column; state that the VCVio bridge, even if completed, certifies only the halting idealisation.

## 2. Per-CID review

### 2.1 UMHSF1 (testing infrastructure)

Statement check: every conjunct is a textbook inequality. Hypotheses are minimal or absent:
- T2: no law hypotheses (true for arbitrary reals since φ ∈ [0,1]);
- T4a: holds for sub-laws;
- T5d: pointwise max-algebra.
Quantifier orders are standard. `E` and `push` are the usual objects. I found no encoding trap.

Issues:
- **F1 (MINOR) floor scope.** STACK row writes `Σ_z max_x M(x,z)`; the Lean is `Σ_z B.sup' …` over a finite `B`
  (= B̄ ⊇ Bad). Over all of X the quantity is larger. Fix: write `max_{x∈B̄}`.
- **F2 (MINOR) attainment of the floor is not by a honeypot law.** The attainment conjunct produces an arbitrary law
  Q on Z (Q ∝ column max). A mediated honeypot law is `push M PH` ∈ conv{M x}, and Q ∝ colmax need not lie in
  that hull. Counterexample (hand-checked, X = B = {A, B}): rows A = (0.6, 0.4, 0), B = (0, 0.4, 0.6); colmax = (0.6, 0.4, 0.6), so
  e^ℒ = 1.6; every q = wA + (1−w)B has max-ratio max(1/w, 1/(1−w)) ≥ 2. So "the maximal-leakage floor is tight for
  honeypot designs" is not established; the row does not claim it, but DESIGN §5 and STACK item 1 read as if e^ℒ
  were attainable. Fix: either say "floor, not nec. tight for PH-designs" or add the (convex-hull) minimum as a
  separate quantity.
- **F3 (MINOR)** T2 attainment: docstring says "deterministic rule", Lean says "some [0,1] rule". Orchestrator noted it;
  agree. Fix: add `∀ z, φ z = 0 ∨ φ z = 1` (the indicator already satisfies it).
- **F4 (MINOR)** "speaks to every untrusted-monitoring protocol": it is a lemma about stateless rules on iid or
  law-level data; say so.

Orchestrator audit: agree with all "faithful" verdicts; they missed F2. Their "Q ranges over all laws, a superset of
mediated honeypot laws, so the floor applies to every honeypot design" is correct for the lower bound and silently
wrong as an implication for tightness.

Triviality: T2/T1 = Neyman–Pearson; T4a/T4b/T4c = one data-processing inequality; T5d = three-line algebra; T4c' =
`Σ_z colmax ≤ L·ΣQ`; "domination from coverage" = one inequality. All textbook.

Novelty: **known**. References (all verified):
- Wasserman–Zhou, "A statistical framework for differential privacy", arXiv:0811.2501;
- Kairouz–Oh–Viswanath, "The Composition Theorem for Differential Privacy", arXiv:1311.0776 (hockey-stick /
  hypothesis-testing form of (ε,δ));
- Balle–Barthe–Gaboardi, arXiv:1807.01647 (hockey-stick divergence, post-processing);
- Dong–Roth–Su, "Gaussian Differential Privacy", arXiv:1905.02383 (trade-off functions);
- Issa–Wagner–Kamath, "An Operational Approach to Information Leakage", arXiv:1807.07878 (maximal leakage);
- Saeidian et al., "Pointwise Maximal Leakage", arXiv:2205.04935 (the pointwise form is exactly the domination
  hypothesis `M x z ≤ L·q z` with q the output marginal; follow-up Grosse–Saeidian–Oechtering arXiv:2310.07381);
- Smith, FOSSACS 2009 (min-capacity `log Σ_y max_x W[x,y]`; no arXiv id, not web-verified by me).
The identity `min{L : ∃Q, M ≤ L·Q} = Σ_z max_x M(x,z)` is the min-capacity of Smith and I_∞-capacity of Sibson/Verdú.
Not a contribution; infrastructure.

### 2.2 UMSURVF1 (survival of the upfront test)

Statement check: faithful. `surv` is the stated recursion (PASS = miss, (j+1)-th miss kills w.p. κ j). Conj. 1 needs
only `Σ q = 1` (pure algebra), conj. 2/3 are polynomial identities for all real h,k, conj. 4/5 have the natural
`0 ≤ h ≤ 1` hypothesis; conj. 6 is a sanity bound. `softKill 0 = 1/0 = 0` in Lean, but the only user (UMPROTF1 soft)
has `1 ≤ ns`; no trap.

Issues:
- **V1 (MINOR) row vs statement.** The row's "h·survival ≤ (n_s+1)/(n_h+1)" is the hard-slack conjunct. The constant
  schedule gives `1/(κ(n+1))` (= n_s/(n_h+1) for κ = 1/n_s). State both.
- **V2 (MINOR) "LASR slack".** The row lists "LASR slack" as a protocol spoken to. LASR's slack is a retraining-dynamics
  parameter ("each training example independently has a 1/n_s chance of making the gradient updates",
  App. B.5); the Lean docstring correctly says "inspired by, not a model of retraining"; the STACK row should too.
- **V3 (MINOR) soft witness is arithmetic.** `1/((1/5)(100+1)) = 5/101` does not instantiate `surv`/`softKill`.
  Orchestrator accepted it for infrastructure; I agree it is harmless, but "non-vacuity" is not demonstrated for the soft
  form. Fix: add `survH (1/4) (fun _ => 1/5) 3 0 = (1 - 1/20)^3`.
- **V4 (MINOR) looseness.** `h(1−κh)^n ≤ 1/(κ(n+1))` is loose by a factor ≈ e (sup is ≈ 1/(eκn)); likewise s = 0
  hard slack. Say so; the exact sup is what the DESIGN tables use.

Orchestrator audit: agree.

Novelty: **classical**. Truncated-binomial first moment `p·C(n,j) = ((j+1)/(n+1))·C(n+1,j+1)·…` is textbook; the
exchangeability reading ((s+1)/(n+1) = chance a given item is among s+1 accepted of n+1 exchangeable items) is classical.
Informal precedents: Greenblatt §3.4.2 (Bayesian remark: "the likelihood ratio stays the same but the prior that the
input is synthetic goes up"); LASR App. B.5 (Poisson approximation, `e^{−λ/n_s}`); LASR App. D ("collusion bits");
Ctrl-Z (arXiv:2504.10374) App. E (the untrusted-monitoring game and its optimisation; LASR says "much of" its Eq. (1) is
shared with Bhatt et al. 2025 but cites an appendix number that differs from the current arXiv version, where App. C is
importance sampling and App. E is untrusted monitoring).

### 2.3 UMPROTF1 (protocol safety)

Statement check, point by point:
- `cat` implements exactly the docstring's recursion. PASS on bad = 1; FLAG with u < b on bad = 1−r; FLAG with
  u ≥ b halts (0); history records (x, z, verdict).
- `protocolCat = Σ_ω ρ ω · surv(push M PH)(φ ω) κ nh 0 · cat(…)`. The product form encodes: given ω, honeypot test and
  deployment are independent, and the generator does not observe the honeypot transcript. The Lean covers only that
  strategy class; the orchestrator notes it.
- T3a: the `if u < b` bound is right for every history; the induction needs only `E (M x) φ ≤ A` on Bad, so it holds for
  adaptive generators and (unusually) gives the generator more information than reality (it sees monitor verdicts on
  benign items). Upper bounds are therefore conservative on that axis.
- T3* attainment: exact equality for fixed bad x, N ≥ 1, b ≥ 1. It does not need `IsRule φ` (harmless).
- T3 domination / hockey-stick / soft: hypotheses are the stated ones. `0 ≤ r ≤ 1`, `0 ≤ L` (or δ), `1 ≤ ns` (soft).
  Not capped at 1: the bound is vacuous but true when RHS ≥ 1.

Issues:
- **P1 (MAJOR) one-sidedness and baseline.** See X2: bound = (1−r) + r·small, and (1−r) is the always-flag
  protocol's value. Fix as in X2.
- **P2 (MINOR) row text.** "The same holds in hockey-stick and soft-slack forms": the soft form exists only in domination
  form (no soft + hockey-stick), and its bound is `L·n_s/(n_h+1)` not `(n_s+1)/(n_h+1)`.
- **P3 (MINOR) tightness is overstated.** "With T3*, the domination form is tight up to the counting gap" (fidelity file).
  The gap is up to ≈ e at s = 0 and the full slack between `a ≤ L·h` and the true `a`. State "within a factor ≈ e, and
  exact when the domination is tight and the counting bound is".
- **P4 (MINOR) generator without honeypot transcript.** Not covered by Lean; Reviewer B's numeric check does not substitute.
  Say "non-observing generator" in the row (it already says "adaptive generator").
- **P5 (MINOR) b = 0.** For b = 0 T3a gives A (not 1−r+rA); the assembled T3 uses the weaker (1−r)+rA. Harmless.
- **P6 (MINOR) "first bad submission decides".** This is the proof idea of T3a, not a separate Lean claim; fine, but the
  stack should not cite it as a verified separate result.
- **P7 (MINOR) halting is the semantics.** See X4.

Orchestrator audit: agree on binders and "faithful"; the "novel as a machine-checked statement" claim is correct but
under-qualified (see novelty).

Novelty: **modest** (formal exactness, not new mathematics). The informal content is Greenblatt §3.4.2 and LASR Eq. (1).
What the Lean adds: quantification over *all* stateless colluding pairs with shared seed and a fully adaptive,
budgeted generator (LASR and Ctrl-Z optimise a parametric strategy family numerically with double-oracle, following
Griffin et al., arXiv:2409.07985); exact attainment; and clean dependence on (r, L, κ, n_h). The proof is a two-line
induction plus the binomial first moment. It is the worst-case counterpart of the "stateless strategising" assumption
studied empirically in Mallen et al., arXiv:2412.12480 ("relax the worst-case assumption of perfect strategic ability").

### 2.4 UMSTRATF1 (stratified honeypots, class-aware shutdown)

Statement check: faithful. Strat survival is the product of per-class `surv (K e) φ (hardKill sc) m 0` (independent
per-class tests given ω); the catastrophe recursion uses `fun x => K (c x)` (content-only). Hypothesis
`∀ bad x, c x ∈ Es` is coverage. (b) attainment needs an exact decoder, N ≥ 1, b ≥ 1. The Claim's docstring correctly
says the second conjunct does not assert tightness.

Issues:
- **S1 (MAJOR) "no class-count factor" is an accounting artefact.** The bound is `(1−r) + r(s_c+1)/(m+1)` with m
  honeypots per class and total n = k·m. In terms of the total budget it is `k(s_c+1)/(n+k)`, which is the iid-global
  bound with L = k at equal n (`k(n_s+1)/(n+1)`). Scratch computation (`strat_vs_global.py`; r = 1, hard slack, colluder
  best response, exact sups):

  | n | k | slack s (equal) | X global | X stratified | honest false-shutdown (α₀ = 5%) global / strat |
  |---|---|---|---|---|---|
  | 96 | 8 | 0 | 0.030 | 0.029 | 0.993 / 0.993 |
  | 96 | 8 | 1 | 0.070 | 0.068 | 0.956 / 0.635 |
  | 96 | 8 | 3 | 0.162 | 0.163 | 0.713 / 0.018 |
  | 96 | 8 | 8 | 0.432 | 0.476 | 0.051 / 0.000 |
  | 100 | 4 | 2 | 0.055 | 0.055 | 0.882 / 0.419 |
  | 120 | 8 | 3 | 0.130 | 0.130 | 0.856 / 0.043 |

  At equal budget and equal slack the exact game values coincide to within a few percent; the Lean bounds differ by
  `(m+1)/(m+1/k)` (≈ 7% at m = 12, k = 8). The DESIGN §5 gain (0.415 vs 0.163 at n_h = 100, α₀ = 5%, k = 8) comes
  entirely from a different effect: per-class slack lets the *honest* monitor tolerate ≈ k·s_c misses in total while the
  *colluder* can use only s_c in its target class, so a smaller s_c meets the same false-shutdown budget. That is a real
  but different (calibration) claim, supported only by numerics, and it depends on α₀ (honest behaviour), which the Lean
  never models. At α₀ = 0 the table shows no gain (0.029 vs 0.029).
  Fix: replace "with no class-count factor" by "at equal total honeypot budget the class factor is unchanged (m = n/k);
  the benefit is per-class slack calibration for an honest monitor, shown numerically (DESIGN §5), not in Lean". Do not
  call it a "design recommendation for any honeypot protocol".
- **S2 (MAJOR, scope)** Content-only for **all** x is the L = 1-per-class case: honeypots of class e have exactly
  `K e`, the same view as attacks. It is the coarse-regime hypothesis (X3).
- **S3 (MINOR) Witness padding.** The Witness has ten trivial conjuncts (`true = true`, `(0:ℝ) ≤ 1`, `Finset.univ.card = 2`,
  `id true ∈ univ`, …) "representing hypotheses". Harmless, but it is padding; the content is the last four lines (value
  `binCDF 12 1 (1/6) · (1/6)`, positivity, and `< 2/13`). Fix: delete the padding or replace it by a single
  statement that the instance satisfies every hypothesis of Claim (a).
- **S4 (MINOR) "any honeypot protocol".** The theorem is for the halting variant with class-aware hard slack and a
  content-only mediator.

Orchestrator audit: agree it is faithful. Disagree with "gain over global: 0.163 vs 0.415" being presented as a
consequence of the verified theorem (S1), and disagree that "no class-count factor" is a finding.

Novelty: **classical** (elementary corollary of UMPROTF1: for fixed ω the product survival ≤ the survival of the
target class, then T3a and T3c). Stratified testing with per-stratum counters and a union bound is textbook
statistical design; the AI-control relevance (class-aware slack) is a **modest** design observation, not a theorem here.
I found no reference stating it, but Greenblatt §3.4.1 (matching synthetic and real distributions on theme and
naming) is the informal precedent.

### 2.5 UMNOGOF1 (coverage impossibility)

Statement check: faithful for what it says. The pair (φ, π) is chosen after (M, c, PH, S) and before
(nh, κ, r, b, N); it is deterministic; π = `submit xs`. For every valid κ, r, b, N ≥ 1 the protocol value is ≥
(1−1/k)^{n_h}. Mathematically: pick the class of S with PH-mass ≤ 1/k (pigeonhole); pass iff the decoded class equals it;
honeypot misses ≤ one class's mass; survive w.p. ≥ (1−p)^{n_h} for any κ; attack passes with probability 1. Part (b)
gives the exact value `t·binCDF(nh,ns,t·p)` for r = 1. I checked this derivation by hand.

Issues:
- **N1 (MAJOR) exact decodability only, but the row extrapolates to "summarising/paraphrasing".** `ContentPreserving`
  is zero-error decodability on supports for **every** x. LLM summarisers/paraphrasers do not satisfy it; the approximate
  decoder appears only in UMHSF1 as a hockey-stick floor, with no operational counterpart. The honest scope is "any
  channel the mediator transmits without error" (identity, canonicalisers, semantics-preserving transforms, preserved
  themes in Greenblatt Table 4–5). Fix: change the row to that scope and add the approximate-decoder version (see
  section 7).
- **N2 (MINOR) pair depends on PH (Kerckhoffs).** The pair knows PH. A shared seed uniform on the k classes gives the
  same bound against an unknown PH, by Jensen (convexity of p ↦ (1−p)^{n_h}). The seed-randomised version is the stronger
  statement and costs one more `ρ`.
- **N3 (MINOR) iid-only and weak when k ≲ n_h.** (1−1/k)^{n_h} is informative only for k ≳ n_h; the exact iid value is much
  larger (`nogo_numbers.py`):

  | n_h | k | no-go (1−1/k)^{n_h} | exact iid value (n_s = 0) | design-free Markov converse (section 7) |
  |---|---|---|---|---|
  | 30 | 8 | 0.018 | 0.097 | 0.067 |
  | 30 | 32 | 0.386 | 0.386 | 0.267 |
  | 100 | 8 | ≈ 0.000 | 0.029 | 0.020 |
  | 100 | 32 | 0.042 | 0.117 | 0.080 |

  The stratified design (UMSTRATF1) is outside the iid family, so no lower bound at all currently covers it.
- **N4 (MINOR) free-submission model.** Red picks the task; with an exogenous task stream the pair needs the task of xs
  to arrive (DESIGN §2.1; orchestrator noted).
- **N5 (MINOR) CANON corollary.** "Canon alone cannot give a guarantee once Red has many ≈-distinct bad programs" is
  true but says no more than "any near-injective mediator has k = (number of bad classes)": it is not specific to canon.

Orchestrator audit: agree with the table. The "quantifier order: stronger than the informal claim" remark is right and
I add N2. They did not flag N1.

Novelty: **classical**. Pigeonhole plus no-hit probability; the statistical fact "a rare subpopulation cannot be tested
with few samples". Empirical analogue: Greenblatt Tables 4–5 (collude-on-theme safety 0.828 → 1 after matching; I
confirmed in the PDF). Conceptual relatives: zero-error capacity (Shannon 1956; no arXiv), steganographic collusion
(Motwani et al., arXiv:2402.07510; Roger–Greenblatt, arXiv:2310.18512 on paraphrasing defences), LASR App. D "collusion
bits".

### 2.6 CANONF1 (verified canonicaliser)

Statement check:
- (i), (ii), (iii) are as docstring-described. `Runs` is existential over terminating runs, so non-termination is
  preserved implicitly (the orchestrator's remark). `Admissible` = fixes params, keeps locals local, injective on
  occurring variables. `SynEquiv = EqvGen Step`, so `for → while` is identified in both directions and for arbitrary
  splits of a while body into (body, step).
- (iii) is a statement about **marginal** laws (orchestrator noted) and is a near-tautology given (ii) (pushforward
  through a class function).
- Witness is non-degenerate.

Issues:
- **C1 (MAJOR) "LASR's For/While marker survived their minifier; this class is provably erased".** Provably erased
  **in the toy language only**.
  - The toy `cfor` is a distinct constructor with C-style statement init/step, no break/continue, no scope. LASR's marker
    is an LLM-written Python `while` where a `for` is natural; Python's iterator `for` is not an `init; while` rewrite.
  - In LASR's own results For/While is not the strongest channel. APPS UM-only: SFT self-recognition 26.4% / 26.1% / 68.8%
    (none / minifier / summariser) vs For/While 50.9% / 76.3% / 82.0%. BCB UM-only: For/While 6.7% / 13.3% / 91.7%, so
    the **summariser**, not the minifier, is LASR's best defence against For/While.
  - The strongest channel (self-recognition by style and tokens: "package imports or method calls", LASR §5) is untouched
    by a canonicaliser that erases only three declared freedoms.
  Fix: "erases the toy analogue of the for/while marker; no claim about LASR's Python pipeline; the strongest LASR
  channel is not in the erased class".
- **C2 (MINOR)** (iii) marginal-only. With a shared seed ω, "every monitor's pass rate is identical on both" needs the
  class-agreement conditional on ω (or an ω-free monitor). The docstring over-reads; the orchestrator recorded it; fix
  the docstring.
- **C3 (MINOR) strength of the "verified mediator" label.** `canon` is a verified *syntactic* normal form for a six-construct
  toy language; it certifies no bound on δ or L (DESIGN: δ(canon) = class-level hs, "astronomically many classes").
  The row says "(a verified trusted component)", which is accurate; the "protocols it speaks to" cell is not.

Orchestrator audit: agree with their fidelity table; they under-weight C1.

Novelty: **known / classical**. Desugaring plus α-normalisation by first occurrence (de Bruijn-style) is textbook;
mechanised for-to-while lowering and semantics-preservation proofs are routine in verified compilers (CompCert's Clight
and Cminor pipeline, Leroy, CACM 2009; no arXiv id, not web-verified by me). The relational big-step semantics with `cfor`
as the C11 equation makes preservation nearly definitional (orchestrator and Reviewer B agree). Its value is as a
trusted-component exemplar only.

### 2.7 SANDBOXF1 (action layer, first step)

Statement check:
- (a) `∀ W ⊇ /var/tmp, WritesHost (currentPolicy W) (home ∪ /var/tmp) (<toolchain>/bin/lake)`: the effective mount of that path is
  the root `.bind [] [] .rw` because no later mount covers it. This is a one-line consequence of `--dev-bind / /`; the
  Lean adds no insight beyond restating the policy. `canWrite` is *instantiated* by the statement ("inside home or
  /var/tmp"), so the theorem is conditional on that host-permission model.
- (b) `WritesHost (fixedPolicy W stateDirs) canWrite p hp → W ⊑ hp ∨ ∃ d ∈ stateDirs, d ⊑ hp` is a parametric lemma true for
  **any** "ro root + list of rw binds" policy. It is true for W = [] too. The security content is entirely in which W and
  stateDirs the harness passes.
- (c) is a denylist theorem: it proves the listed hidden directories are hidden in the current policy under the
  boundary assumption.

Issues:
- **B1 (MAJOR) model theorem described as a system defect.** STACK says "(a) The current policy does **not** confine
  host writes to scratch: the toolchain directory (executed by the gate) is writable." Two premises are outside the Lean:
  that bwrap with this argv really leaves it writable (host bits, mount semantics), and that the unsandboxed checker
  executes from that directory. "Verified" in the status column means "the model theorem is kernel-checked", which
  readers will take as "the defect is confirmed". Fix: label the result as a model theorem and keep system claims
  separate; a system claim needs its own test (for example a harmless canary write from inside the sandbox).
- **B2 (MAJOR) the proposed fix regresses hiding; checked in the model.** `fixedPolicy` places `hiddenDirs.map .tmpfs`
  **before** `stateDirs.map (bind d d rw)`. If a declared state directory is an ancestor of a hidden directory, the later
  bind covers the earlier tmpfs. `hiddenDirs` contains session-log and scratch subdirectories of CLI state directories
  (`<cli-a>/sessions`, `<cli-a>/log`, `<cli-b>/tmp`, …); the CLI state the fidelity file mentions (credential refresh)
  plausibly forces `<cli-a>` or `<cli-b>` as declared state directories.
  `sbx.lean` (the frozen `effective`/`fixedPolicy`/`hiddenDirs` definitions copied verbatim; `lean` v4.35.0-rc3):
  ```
  -- stateDirs = [<home>/<cli-a>, <home>/<cli-b>]; probe paths inside hidden dirs
  effective (fixedPolicy W stateDirs) [<home>,<cli-a>,sessions,rollout-1.jsonl]
    = some (Mount.bind [<home>,<cli-a>] [<home>,<cli-a>] rw)     -- hidden dir revealed, and writable
  effective (fixedPolicy W stateDirs) [<home>,<cli-b>,tmp,x]
    = some (Mount.bind [<home>,<cli-b>] [<home>,<cli-b>] rw)     -- revealed
  effective (fixedPolicy W [])        [<home>,<cli-a>,sessions,rollout-1.jsonl]
    = some (Mount.tmpfs [<home>,<cli-a>,sessions])               -- hidden when no ancestor is declared
  ```
  (b) remains true (writes land inside a state dir) while hiding silently fails. There is no (c′) for `fixedPolicy`.
  Fix: put the state binds before the hide tmpfs (or hide after), and add a theorem
  "∀ stateDirs, ReadsHost (fixedPolicy W stateDirs) p hp ∧ H ∈ hiddenDirs ∧ H ⊑ hp → hp inside a state dir ∨ inside Mathlib"
  with the order made explicit.
- **B3 (MAJOR, scope) state directories are execution surfaces and reads are unconfined.**
  - Coding-agent CLI state directories hold executable configuration (hooks, MCP server commands, skills, settings) that
    outside processes will run. (b) only moves the problem to the choice of stateDirs; files (not dirs) and copy-in/copy-out
    of credentials are the safe pattern.
  - The fixed policy keeps `--ro-bind / /` and (per the boundary assumption) an open network: every non-hidden secret
    (SSH keys, env files with API keys, other projects) is readable and exfiltratable. (c) is a denylist; there is no
    allowlist/confidentiality theorem.
- **B4 (MINOR) boundary assumptions.** `Path` is a syntactic list of components: no `..`, symlinks, bind aliases, `/proc`,
  unix sockets, device nodes, setuid/capabilities. The named boundary only covers `/proc/<pid>/root` and network.
- **B5 (MINOR) layer fit.** SANDBOXF1 models a research-harness sandbox for untrusted provers, not an agent action monitor
  for U's tool calls. It supplies no B̄ and discharges no assumption of Layer 1 (A9). The row sits under "Layer 2:
  actions" which implies progress on the constructibility gap; there is none yet.

Orchestrator audit: correspondence table is plausible but untestable by me. They are right that (a) is a "model fact";
I disagree that "faithful" suffices as the verdict given B1–B3.

Novelty: **known** (bwrap mount semantics; engineering). Value: it found a code-reading defect and pinned a fix; no
research novelty is claimed or deserved.

### 2.8 "Existing verified results that slot into the stack" (N1/N1b, K5, CLKF1/2, LUREF1/2)
Their statements were not given to me; no verdict. One caution: STACK says they "are the stateful-adversary caveats to
A1 and A4 here". If that is a claim of formal composition it should not be made without a theorem (composition with trusted
monitoring is a min, not a product, absent conditional independence; the stack itself says so).

## 3. Overclaim register (STACK.md, exact rows)

| row / text | claim | problem | sev. |
|---|---|---|---|
| title | "capability-free control guarantee stack" | L and r are capability-parity hypotheses (X1) | MAJOR |
| UMPROTF1 | bold "**For every colluding pair**" | strategy class is stateless monitor, non-observing generator, halting semantics (X1, X4) | MAJOR |
| UMPROTF1/UMSTRATF1 | "guarantee" | one-sided; always-flag satisfies it (X2) | MAJOR |
| UMSTRATF1 | "with no class-count factor" | accounting artefact; equal budget ⇒ factor k (S1) | MAJOR |
| UMSTRATF1 | "design recommendation for any honeypot protocol" | halting, content-only, hard class slack only | MINOR |
| UMNOGOF1 | "why summarising/paraphrasing alone cannot give capability-free collusion safety" | exact-decodable only (N1) | MAJOR |
| CANONF1 | "LASR's For/While marker … provably erased" | toy language; weaker channel (C1) | MAJOR |
| "Unproved" item 1 | "false for every honeypot law" for LLM summarisers | floor is finite; summarisers not exact; contradicts DESIGN §3/§8 (X3) | MAJOR |
| UMHSF1 | "every untrusted-monitoring protocol" | a stateless-rule lemma (F4) | MINOR |
| SANDBOXF1 | "verified" (a)(c) | model theorem, not a system test (B1) | MAJOR |
| SANDBOXF1 | (b) "fixed policy confines…" | fix un-hides when stateDirs are ancestors (B2); dirs are exec surfaces (B3) | MAJOR |
| UMSURVF1 | "LASR slack" | retraining dynamics, not shutdown (V2) | MINOR |
| UMPROTF1 | "same holds in … soft-slack forms" | soft only domination form; constant differs (P2) | MINOR |

## 4. Novelty gate (calibrated)

Labels use: known / classical / modest / apparently open.

| CID | label | why | closest prior art |
|---|---|---|---|
| UMHSF1 | **known** | NP lemma, DPI for hockey-stick, min-capacity; the pointwise-leakage form is the domination hypothesis | arXiv:0811.2501, 1311.0776, 1807.01647, 1905.02383, 1807.07878, 2205.04935, 2310.07381; Smith 2009 |
| UMSURVF1 | **classical** | truncated binomial identity; exchangeability | Greenblatt §3.4.2 prose; LASR B.5; Ctrl-Z App. E (2504.10374) |
| UMPROTF1 | **modest** | machine-checked worst-case over all stateless pairs with exact attainment; mathematically a 2-line induction plus the binomial moment | LASR Eq. (1) (2602.20628); 2504.10374; Griffin et al. 2409.07985; Mallen et al. 2412.12480 |
| UMSTRATF1 | **classical** (elementary corollary) / modest as a design observation not in Lean | per-stratum counters and union bound | Greenblatt §3.4.1 |
| UMNOGOF1 | **classical** | pigeonhole + no-hit probability; not even stated design-free | Greenblatt Tables 4–5; 2402.07510; 2310.18512 |
| CANONF1 | **known** | verified desugaring + α-normalisation | verified-compiler literature (CompCert) |
| SANDBOXF1 | **known** | bwrap mount semantics | none needed |

Search coverage: I searched for formal/Lean treatments of AI-control protocols, for information-theoretic
(maximal leakage/DP) treatments of collusion and mediators, and for analytic untrusted-monitoring bounds, and found
**no prior Lean-verified or worst-case-over-all-pairs treatment** (nearest: Lean-based agent guardrails for finance,
arXiv:2604.01483, which is unrelated; Alignment Contracts, arXiv:2605.00081). My cutoff is June 2026 and search is
US-only; absence is evidence, not proof. The honest claim is "I did not find this stated", which for these results is
unsurprising because they are elementary.

## 5. Significance for AI control (honest)

What the package genuinely contributes:
1. A precise, checkable statement of the folklore argument for upfront honeypot testing (Greenblatt §3.4.2, LASR
   App. B/D): the colluder's gain over an always-flag baseline is ≤ r·L·(n_s+1)/(n_h+1), with all dependence on three
   named quantities (r, L, κ) and the scaffold assumptions.
2. A clean information-theoretic reading of mediation: the domination constant is pointwise maximal leakage; its floor is
   the min-capacity; why a mediator that passes a k-class feature needs ≈ k·m honeypots.
3. Infrastructure (an exact `cat`/`surv`/`protocolCat` in Lean that later work can extend).

What it does not deliver:
- **The hard parts are the unproved assumptions**: L for any real mediator, r, A1–A4, constructibility of B̄, and
  stateless enforcement. The Lean covers the easy arithmetic around them. Effective strength = the informal argument plus
  correct arithmetic.
- **The hypotheses are satisfiable only for coarse mediated views** (X3), where UM's value over a trusted rule is
  unestablished.
- **Not a statement about a named protocol** (X4); and **no usefulness half** (X2).
- It does not improve on the empirical picture: LASR's strongest channel (SFT self-recognition through the summariser:
  68.8% UM-only) is untouched by any theorem here, and the verified mediator (CANON) addresses a weaker one.

Net: a careful, honest formalisation of the existing argument, good as the formal skeleton of a safety case section
("what must be true for the honeypot test to bound collusion"). Not, on its own, a research result.
Probability it changes a control-design decision today: low; the most decision-relevant, least-new content is "honeypot
budget scales with the number of distinct decodable collusion classes" (qualitatively in Greenblatt), and "retry/defer
voids the guarantee" (numerics only).

## 6. Fix list (ordered)

1. Retitle and add the "who must be trusted for what" column (X1).
2. Add "adversarial-gain bound over the always-flag baseline; usefulness not formalised" to the UMPROTF1/UMSTRATF1 rows;
   add the honest-side companion lemma (X2).
3. Replace "Unproved" item 1 and add the coarse-regime sentence (X3).
4. Rewrite the UMSTRATF1 row (S1); delete "any honeypot protocol".
5. Scope UMNOGOF1 to exact decodability; add the approximate/seed-randomised/design-free versions (section 7).
6. CANONF1: restrict the LASR sentence to the toy analogue (C1).
7. SANDBOXF1: split model status from system status (a system claim needs its own test); fix `fixedPolicy` ordering and add a hiding theorem
   for the fixed policy; address state-dir exec surfaces and reads (B1–B3).
8. Minor: F1–F4, V1–V4, P2–P6, S3–S4, N2–N5, C2–C3, B4–B5.

## 7. Single most valuable next formalisation step

**A design-free, noise-robust converse that makes Layer 1 two-sided: "any honeypot design needs n_h = Ω(k(n_s+1)/X)".**

Lean-ready statement (sketch). For finite X, Z, C; M an `IsKernel`; `ContentPreserving M c` (or γ-approximate: decoder error ≤ γ);
S ⊆ Bad with `c` injective on S, |S| = k; **any** honeypot design (an arbitrary joint law of n submissions, not iid, possibly
adaptive in the class labels, independent of ω); any hard-slack or class-aware hard-slack shutdown rule. Then for r = 1
and every t ∈ [0,1] there is a colluding pair (seed uniform on the k classes, `φ_ω(z) = t·[g z = e_ω]`, generator
`submit x_{e_ω}`) with
  `protocol risk ≥ t·(1 − t·n/(k(n_s+1)))`  (≥ k(n_s+1)/(4n) at t = k(n_s+1)/(2n) ≤ 1; ≥ 1/2 when n ≤ k(n_s+1)/2).

Proof: averaged over the uniform class, E[hits per class] ≤ n/k, so E[misses] ≤ t·n/k; Markov gives
P(misses > n_s) ≤ t·n/(k(n_s+1)); the attack passes with probability t. No iid, no knowledge of the honeypot law (the seed
randomises), no Kerckhoffs assumption. With a γ-error decoder subtract an additive O(γ·n) term.

Why this one:
- it turns UMNOGOF1 (iid-only, informative only for k ≳ n_h) and UMSTRATF1 (upper bound only) into a **matching pair**
  `Θ(k(n_s+1)/n)`, shows the class factor is **unavoidable for every design**, and thereby makes S1 a theorem instead of a
  correction;
- it is elementary and Lean-sized (a few hundred lines on existing `surv`/`protocolCat`), so it is certain to land;
- it removes the largest scope restriction of the no-go (exact decodability and iid) and so supports, or honestly retracts,
  the "summarising/paraphrasing" sentence;
- it gives AI-control designers the one quantitative design rule the stack can honestly assert: honeypot budget per
  distinguishable collusion class.

Runner-up (higher impact if it works, riskier): extend `cat` with a defer-to-trusted routing kernel plus Greenblatt's
rate test (execute/audit/replace/halt) and prove either a first-bad-decides bound under an incrimination condition or the
exact retry-closure value `sup_h S(h)(1−(1−h)^K)` that the numerics claim. That is the formalisation step that
decides whether anything here applies to the protocols labs actually use.

## 8. Per-CID verdict table

| CID | fidelity verdict | worst issue | novelty label | references (all arXiv ids web-verified) |
|---|---|---|---|---|
| UMHSF1 | faithful (minor scope/wording: F1–F4) | F2 floor not nec. attained by honeypot law | known | 0811.2501, 1311.0776, 1807.01647, 1905.02383, 1807.07878, 2205.04935, 2310.07381; Smith FOSSACS 2009 (no id) |
| UMSURVF1 | faithful (V1–V4) | V3 soft witness is arithmetic | classical | Greenblatt 2312.06942 §3.4.2; LASR 2602.20628 B.5/D; Ctrl-Z 2504.10374 App. E |
| UMPROTF1 | faithful in Lean; MAJOR overclaim in row (X1, X2, X4) | one-sided, halting, "capability-free" | modest | 2602.20628 Eq.(1); 2504.10374; 2409.07985; 2412.12480; 2312.06942 |
| UMSTRATF1 | faithful in Lean; MAJOR framing (S1, S2) | "no class-count factor" is accounting | classical (modest as design observation) | 2312.06942 §3.4.1 |
| UMNOGOF1 | faithful; MAJOR scope (N1) | exact decodability only | classical | 2312.06942 Tables 4–5; 2402.07510; 2310.18512; 2602.20628 App. D |
| CANONF1 | faithful; MAJOR overclaim in row (C1) | toy language, weaker channel | known | CompCert (Leroy 2009, no id); 2602.20628 Table 2 |
| SANDBOXF1 | faithful as a model; MAJOR scope/status (B1–B3) | model theorem only; fix un-hides | known | none |

Overall verdict: **sound but modest; relabel and rescope before circulating.** No FATAL. 11 distinct MAJOR items: X1–X4, S1, S2,
N1, C1, B1–B3 (P1 duplicates X2). Do not claim "capability-free" or "guarantee" without the qualifiers.

## 9. arXiv ids cited and checked (export.arxiv.org API, 2026-10-07)

| id | title (as returned) |
|---|---|
| 2602.20628 | When can we trust untrusted monitoring? A safety case sketch across collusion strategies (Gardner-Challis et al., 2026-02-24) |
| 2312.06942 | AI Control: Improving Safety Despite Intentional Subversion (Greenblatt, Shlegeris, Sachan, Roger) |
| 2504.10374 | Ctrl-Z: Controlling AI Agents via Resampling (Bhatt, Rushing, Kaufman, Tracy) |
| 2409.07985 | Games for AI Control: Models of Safety Evaluations of AI Deployment Protocols (Griffin, Thomson, Shlegeris, Abate) |
| 2412.12480 | Subversion Strategy Eval: Can language models statelessly strategize to subvert control protocols? (Mallen et al.) |
| 2402.07510 | Secret Collusion among AI Agents: Multi-Agent Deception via Steganography (Motwani et al.) |
| 2310.18512 | Preventing Language Models From Hiding Their Reasoning (Roger, Greenblatt) |
| 1807.07878 | An Operational Approach to Information Leakage (Issa, Wagner, Kamath) |
| 2205.04935 | Pointwise Maximal Leakage (Saeidian, Cervia, Oechtering, Skoglund) |
| 2310.07381 | Extremal Mechanisms for Pointwise Maximal Leakage (Grosse, Saeidian, Oechtering) |
| 1311.0776 | The Composition Theorem for Differential Privacy (Kairouz, Oh, Viswanath) |
| 1807.01647 | Privacy Amplification by Subsampling: Tight Analyses via Couplings and Divergences (Balle, Barthe, Gaboardi) |
| 0811.2501 | A statistical framework for differential privacy (Wasserman, Zhou) |
| 1905.02383 | Gaussian Differential Privacy (Dong, Roth, Su) |
| 2604.01483 | Type-Checked Compliance: Deterministic Guardrails for Agentic Financial Systems Using Lean 4 Theorem Proving (Rashie, Rashi) |
| 2605.00081 | Alignment Contracts for Agentic Security Systems (David, Guarnieri, Gervais) |

Not web-verified by id (no arXiv id): Smith FOSSACS 2009; Leroy CACM 2009; Shannon 1956.
