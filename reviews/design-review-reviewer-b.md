# Hostile review of DESIGN.md + CORRESPONDENCE.md (reviewer: Reviewer B, 2026-10-07)

Scope: everything in `reviews/design-review-prompt.md`. Sources actually read: LASR 2602.20628 v2 (full text, App. B and E
in detail), Greenblatt et al. 2312.06942 (full text, §3.1-3.4, App. F-G), REUSE.md, `numerics/*.py` (all run). My own checks are in
`<scratch>/check*.py` (exact `Fraction` DP for the protocol with budget/recall/halting; NP-frontier exact value;
table recomputation; counterexample searches). Nothing outside `<scratch>/` and this file was written.

## 0. Verdict: MAJOR (not reject; do not formalise as written)

* The finite-sum core is TRUE as stated: T1, T2, T3a, T3b, T3c, T3c', T4a, T4b, T4c, T5a, T5b, T5d all survive every
  counterexample search I could build (including r<1, finite budget, halting, adaptive history-dependent generators, h=0,
  n_s>=n_h, empty Bad, q with zero entries, eta<0). I found no false theorem among T1-T5. They are classical
  (DP hockey-stick / conformal validity / data processing); fine as infrastructure.
* The problems are (i) **unfaithfulness of the protocol semantics** (halt-on-exhaustion + audit-as-release-valve; r as a
  constant; soft slack as a trusted parameter), (ii) **"capability-free" is overclaimed**: r, the enumerability of Bad, the
  constructibility of P_H and soft kappa are all capability assumptions, (iii) **non-vacuity is overstated** (the §5 table uses
  honeypot counts 10-1000x above what LASR/Greenblatt budgets allow; at realistic budgets X is >= 0.25 as soon as k >= 8),
  (iv) **T5c ("no honeypot law gives less") and T6 ("provably erased") are overclaims**, with explicit counterexamples below,
  (v) the numerics do **not** cross-check the Lean `cat` definition with budget, r<1 or halting (I did; it passes), and the
  bridge from the hand-written recursion to an independent probabilistic semantics is listed last (§7.5) although it is the only
  faithfulness anchor.
* There is a strictly better, simpler, exact formulation available (§3, "T3*"/"T4c'") that I would formalise instead of T3d/T4c/T5c.

No FATAL finding on the mathematics. Two items are FATAL-for-the-headline-sentence if not relabelled: F2 (r) and F5 (Bad/P_H
operationality) say "X is a function of trusted quantities only" (§0) is not true operationally. Rated MAJOR below because the
theorems remain correct once those quantities are made explicit hypotheses.

---------------------------------------------------------------------------------------------------------------------------

## 1. Faithfulness (Q1)

### F1 [MAJOR] Halt-on-exhaustion + "audit = release valve" is not what Greenblatt/LASR do, and carries the whole of T3a
Sentence: "FLAG and the budget is exhausted: **halt** deployment (safe)" (§2.2); A5 "budget exhaustion halts deployment | first bad
attempt decides"; §6 "Variant: defer on budget exhaustion ... The bound degrades to ≈ K·(e^η h + δ)".

What the sources do:
* Greenblatt App. G: audit threshold is rate-calibrated (top 1.4-2% of honest-calibrated suspicion); budget-wasting is handled by a
  *continuous binomial test* "significantly more false positives than the expected 2% rate (tested using the binomial CDF with
  p = 0.03)", after which "we only submit solutions from the trusted model ... we temporarily use the trusted model and then swap
  back". That is a rate test with *temporary* deferral, not a permanent halt at a count.
* LASR §B.4: win/**continue**/lose; flagged-for-defer-but-not-audit "the game continues". Their p_red has the factor u/(c+u),
  not u. T3a's "P(cat | ω) ≤ u" equals LASR's per-attack term only if c+u = 1, i.e. every flagged attack is audited. CORRESPONDENCE
  row "safety event" ("our T3a is exactly the per-attack ratio") is therefore overclaimed.
* ControlArena: budget = percentile of honest scores (a rate), no halting.

Why it matters. Under the model as written, a colluding monitor flooding the queue (flag b decoys) is *neutralised by fiat*.
Without that fiat the first bad attempt no longer decides and T3a is false. The one-line "≈ K·(e^η h + δ)" is also wrong in kind:
it is an upper bound exceeding 1 for any K >= 10; the true value with perfect coverage is already ≈ 1
(`check8_defer.py`: n_h=100, n_s=5, **L=1 (perfect honeypots)**, K attacks after exhaustion, each passed w.p. a=h; value =
sup_h S(h)(1-(1-h)^K) = 0.032 (K=1), 0.264 (K=10), 0.885 (K=100), 1.000 (K=1000, 4900); same for n_h=30 and n_h=1000, n_s=16 at K=4900).
So "defer" is not a small gap; honeypots alone cannot protect any protocol where an attack can be retried ~n_h times. Exhaustion
must be prevented by pacing/rate-testing, which is exactly what Greenblatt does.

Second-order: with halting, audits are strictly *harmful* in the model. Exact first-bad value is (b>=1) (1-r)(1-a)+a vs (b=0)
a (`check1_t3a.py`, 300 random instances, exact). So Blue's optimal b is 0, b never appears in any bound, and the
(1-r) term of T3 is self-inflicted (it exists only because an audit may *release* a flagged attack that halting would have
blocked). Consequently the safety theorems are monotone in "halt more" and there is no usefulness model to stop the degenerate
optimum (halt at first flag).

Fix. (a) State the protocol with an explicit post-flag rule R in {halt-at-b, pace/rate-test then temporary defer}. Prove T3a for
the rate-test version ("any window with > w flags halts"), which is the faithful one and still gives "first bad decides" if the test
is a function of the flag history only. (b) Add the usefulness companion in the same game: P(false halt | honest monitor with miss
rate α₀ and false-flag rate ε) for the same (n_s, b, window). Without it every safety theorem is trivially satisfiable. (c)
Replace the §6 remark by the exact deferral computation above and say "vacuous unless K·h ≲ 1".

### F2 [MAJOR] r is a capability quantity; additive (1−r) is the wrong shape
Sentence: "A6 | An audit of a bad submission catches it with probability ≥ r | TRUSTED-COMPONENT (human audit)"; §0 "No quantity in
X depends on what U chooses to do".
Red chooses x∈Bad, so a capability-free r must be inf_{x∈Bad} r(x), the audit recall on the *worst* attack U can produce. For
superhuman or merely audit-evading attacks that is ≈ 0 and T3 is ≥ 1. Greenblatt assumes "H can construct an exploit iff the attack
policy can" (parity between H and U), and LASR assumes "a human audit would find clear evidence" (§2): both are capability
assumptions on U/H, flagged in those papers and silently relabelled TRUSTED here. Shape: the exact first-bad value is (1-r) + r·a
(b>=1), so the stated bound (1-r) + a is loose by (1-r)a, and T3 adds S(h)(1-r) <= (1-r) instead of keeping it multiplied by S.
Fix: label r STANDING (like S2) or define it as the worst-case-over-Bad recall; state T3 as S(h)·[(1-r) + r·a].

### F3 [MAJOR] Soft slack is a capability assumption, and the justification for "every pass counts" is inverted
Sentences: "Soft slack (LASR App. B.5): κ_j = 1/n_s for every j"; "'Honest vs dishonest' is a fact about U_M's internal belief that
Blue cannot observe. A capability-free model must let Red label every miss as honest. So every PASS counts" (§6); CORRESPONDENCE
slack row.
LASR App. E: κ = 1/n_s is a statement about SGD ("each training example independently has a 1/n_s chance of making the required
gradient updates", "not grounded in any established theory of fine-tuning dynamics", "lower-bounding n_s remains an open problem").
It is a property of U's learning dynamics, i.e. the least capability-free parameter in the whole setup. LASR counts only dishonest
misses because *their physical mechanism* (retraining) only moves weights on dishonest misses. If Red may "label every miss as
honest", then under LASR's mechanism no miss ever kills (S ≡ 1); the doc's conclusion "so every pass counts" does not follow.
What *is* capability-free is a Blue-run rule on observables (hard threshold / significance test), which is what Greenblatt and
Bhatt et al. use (LASR App. E: "in contrast to ... who opted for statistical significance tests"). Also "retraining into an honest
monitor; for safety the two are the same" ignores the honest monitor's residual miss rate on *real* (non-honeypot-like) attacks.
Fix: hard slack is the main theorem; soft kappa is a conditional theorem with kappa an explicit assumption on U (STANDING/ASSUMED),
and drop the sentence about labelling. Nice simplification (verified, `check9_kappa.py`): every kill schedule is a *mixture of hard
thresholds*: S_κ(h) = E_G F(n_h, G, h) with P(G >= j) = ∏_{i<j}(1-κ_i), hence for **all** κ
sup_h h·S_κ(h) <= (Σ_{j=0}^{n_h} ∏_{i<j}(1-κ_i)) / (n_h+1) (hard: n_s+1; soft: 1/κ = n_s). One lemma replaces T3c + T3c'.

### F4 [MAJOR] Tasks are chosen by Red; Bad is per-submission; the model cannot express multi-step attacks
Sentence: table row X: "Merging the task into the submission makes attack *selection* ... part of Red's choice".
(a) Over-adversarial: in deployment Red does not choose the task, it chooses *when* to attack among tasks the environment
supplies. Quantifying over all x=(task, output)∈Bad forces coverage of tasks that never occur, so k counts (task class × attack
class). Honest modelling: tasks t_i exogenous (or from a trusted law D), Red picks y_i and the timing; honeypots (t,y) with t~D' (Blue
can flatten D'). This is sound-but-pessimistic as written; say so, and note that Red waiting for a rare task is a real effect
(Greenblatt App. F.1 discusses selectivity) the exogenous model captures correctly.
(b) Bad is a property of a single submission and the monitor is stateless (A1), so the *conjunctive* multi-step / distributed attack
(each step benign-looking, composition bad) is outside the model by construction: Red cannot even express it, and a stateless
monitor cannot detect it. CORRESPONDENCE admits "X = trajectory prefixes (later)", but then the generator is constrained to
extend its previous prefix, k explodes (prefix content), and A1 must be relaxed. This should be listed in §7 as an exclusion, not
deferred in a table cell.

### F5 [MAJOR] X is not operational: it needs Bad enumerated and P_H constructible by Blue
δ_η = max_{x∈Bad} hs(M x ‖ q) can be evaluated only if Blue can enumerate (a superset of) Bad; the coverage of every bad class
by P_H requires Blue to *build a genuine working attack in each class*. T5c's optimum "uniform over bad classes" presupposes that
every class in c(Bad) has a Blue-constructible member. Classes only U can realise get P_H(c=e)=0, p=0, X=1. Greenblatt's H points
are written by the untrusted model itself (parity with U; 30 examples); LASR's honeypots come from a *different* model that "is unlikely to perfectly mimic
U_G's style" (§2.1). Greenblatt Tables 4-5 are the empirical instance of T4c: theming/naming present in 81.6%/70.4% of real
attack inputs vs 9.4%/7.9% of synthetic ones; a "collude if theme is present" colluder gets safety 0.828; after fixing coverage 1.0.
Fix: theorems relative to a Blue-enumerable Bad-superset B̄ ⊇ Bad and a Blue-samplable P_H supported on B̄ (monotonicity lemma
δ(Bad) <= δ(B̄)); the interface to the action layer is then "B̄ is structural". Add a sentence that the guarantee is exactly as
capability-free as the *construction of B̄ and P_H*.

### F6 [MINOR→MAJOR for T3 reading] Upfront vs interleaved is load-bearing, and A4 is mislabelled
A4 ("honeypot phase completes before any deployment output executes") is labelled TRUSTED-COMPONENT but is a *hypothesis of T3*:
with honeypots interleaved (random positions) and a time-aware generator, Red attacks at round 1 before any honeypot has been seen
and the bound is false (X → a ≈ 1). Because π sees history length, Red also knows the round index, so dropping LASR's (1-β)^10
(10 free upfront audits) is *exact* in this model, not merely conservative as §6 says. A10 is fine: I verified the generator seeing the
honeypot transcript changes nothing (S factors out; stateless φ_ω).

### F7 [MINOR] A1/A2 vs LASR's mechanism
LASR's honeypots are *training data* with "online honeypot generation" ("the training distribution matches deployment (ensured by
online honeypot generation)", §3.2). Frozen weights (A1) plus kill-or-survive is a model of Greenblatt's rule, not of LASR's.
State that T3 models Greenblatt-style evaluate-then-deploy, and that LASR's soft slack is imported only as a conditional schedule.

### F8 [MINOR] Trusted-monitor composition claim is not capability-free
§7.4 / CORRESPONDENCE: "an independent extra flag with worst-case recall τ multiplies the attack pass rate by (1 − τ)". Independence
is false for a worst-case attack (Red crafts x to evade T as well as the collusion channel; Greenblatt/LASR see correlated misses),
and worst-case τ over Bad is ≈ 0 for subtle attacks. Remove the product claim; the capability-free composition is a *min*, not a
product.

### F9 [MINOR] Greenblatt mapping omissions (§6)
Missing from the mapping: the binomial FP test + temporary swap (F1); the ensemble with T and a rank-based audit threshold (top 1.4%);
synthetic inputs cost 1 H point each (n_h = 30); redaction of both input and output; and the arms-race evidence in Tables 4-5.
Their "UM improves with scale" argument (prior that an input is synthetic grows with n_h) is the Bayesian reading of S(h).
Correct statements in DESIGN §6: upfront evaluation ✓, shutdown on too many misses ✓, LASR Eq. (1) transcribed correctly ✓,
LASR counts only dishonest misses ✓.

---------------------------------------------------------------------------------------------------------------------------

## 2. Truth of T1-T6 (Q2). What I tried and what I found

Edge-case sweep (all pass): h=0 (S=1, a<=δ); n_s>=n_h (F=1; closed form >= 1, vacuous but valid); κ=0 (S=1; soft closed form
undefined at n_s=0, requires n_s>=1 as stated); empty Bad (cat=0; Lean needs `sup'`-free statement); q with zero entries (L=∞, hs
counts the mass, fine; state L as a hypothesis `M x z <= L * q z`, not as a value); η<0 (T2 holds for every real η, restriction η>=0
is unneeded); b=0 (flag => halt, exact value a); r=0 (exact value 1 whenever b>=1: audits release everything); infinite L (vacuous).

* **T1/T2/T4a/T4b** true, textbook: T2 is *literally* (ε,δ)-indistinguishability of M x from q (Dwork-Roth; hypothesis-testing form
  Wasserman-Zhou 2010, Kairouz-Oh-Viswanath 2015; hockey-stick Barthe-Olmedo 2013, Balle et al. 2018), T4a is post-processing.
* **T3a** true. The exact value for the best generator is max_{x∈Bad}[a_x + (1-a_x)(1-r)·1{b>=1}] (attack at once; first bad decides), and
  my exact DP (300 random instances, `Fraction`, b∈{0,1,2,5}, r∈{1,.9,.5,0}, N≤3, adaptive generators maximised exactly) equals it with 0
  mismatches and 0 violations of the stated bound. The existing `protocol_bruteforce.py` implements *none* of b, r, halting or kill
  schedules (it uses r=1, no budget, hard slack only through the closed form B(n,s,h)); §4's "T3a ... brute-force" is
  overstated for the definitions in §2.2. Proof is a clean induction on n generalising (u, hist) (benign branch: B·Σ_z M(φ+(1-φ))=B).
* **T3b** true; **T3c** true and sharp within factor e: min over n<=300, s<=40 of sup_h hF/((s+1)/(n+1)) = 0.3685 -> 1/e (s=0, n→∞),
  0 violations. The identity is `Nat.succ_mul_choose_eq`. **T3c'** true (derivative; or Bernoulli: (1-u)^n<=1/(1+nu)). Both are
  corollaries of the single κ-general lemma in F3.
* **T3 closed forms** true. Soft form `n_s/(n_h+1)` requires n_h+1 >= n_s to be non-trivially below 1; the true sup is 1/e smaller
  (0.0183 vs 0.0495 at LASR parameters), so the closed forms are not "exact".
* **T3d is mislabelled "exact form".** It is an upper bound for a fixed η. The truly exact value (r=1, any mediator, any kill schedule)
  is **V = max_{x∈Bad} sup_{h∈[0,1]} S(h)·A_x(h)** where A_x(h) = max{E_{M x} φ : E_q φ = h} is the Neyman-Pearson frontier
  (fractional knapsack by likelihood ratio), equivalently A_x(h) = min_{γ>=0}(γh + hs_γ(M x‖q)). I verified this equals a brute-force
  grid search over all φ of the full protocol to 2.6e-4 (grid error) on 200 random 5×4 mediators, and that T3d with the best single η is
  within 1.000-1.079 of it. So T3d is nearly tight in practice, but the exact statement is cleaner (no η, no δ) and is two-sided
  (≤ for all policies, = attained by an explicit threshold monitor). Formalise that instead (§7).
* **T4c** true as stated (DPI along the decoder g; L>=1/P_H(c=cx) by Σ_z M x z = 1). Two problems: (1) the hypothesis "g z = c x
  whenever M x z>0" is exact decodability, which no LLM mediator satisfies, so as stated T4c says nothing about the cases the doc cares
  about; (2) it is a corollary of a hypothesis-free bound (next bullet).
* **T4c' (new, hypothesis-free floor, verified `check6_maxleak.py`).** For every law Q on Z (not only Q = M·P_H) and every attack set B:
  max_{x∈B,z} M(x,z)/Q(z) >= Σ_z max_{x∈B} M(x,z) =: e^{ℒ(M|B)}, with equality iff Q ∝ z↦max_x M(x,z). Proof: weighted-average ≤ max.
  This is the **maximal leakage** of M restricted to B (Issa-Wagner-Kamath 2020). For a deterministic content-only M it equals the
  class count k (so it contains T4c/T5c's "k"), for noisy mediators it interpolates (a randomised paraphraser can have ℒ << log|classes|).
  Approximate version (replace exact decodability): if g satisfies P(g(Z)=c(x)) >= 1-γ for all x then
  hs_η(M·P_A‖M·P_H) >= hs_η(c#P_A‖c#P_H) − (1+e^η)γ (same perturbation lemma that proves T5d). This is the form that applies to
  summarisers.
* **T5a** true (needs only content-only, not content-preserving: q z >= p·M x z). **T5b** true (brute force and my NP check agree:
  value (h/p)F(h), sup over h∈[0,p] = sup over all h because F decreasing). Note it needs r=1 and Red knowing P_H (Kerckhoffs; fine).
* **T5c is false as a "minimax over honeypot laws" claim.** It is true only inside the family {i.i.d. P_H, global miss-count kill rule,
  content-preserving deterministic classes}. Explicit counterexamples (all exact or tight numerics):
  1. *Non-i.i.d. stratified honeypots* (m per class, class labels known to Blue): k=100, n_h=100, n_s=0: i.i.d. optimum
     F*(100) = 0.366; stratified m=1 gives sup_a a(1-a) = 0.25.
  2. *Class-aware kill rule* (kill if ANY class has > s_c misses; Blue knows each honeypot's class): Red attacking class e needs
     ≤ s_c misses among m honeypots passed w.p. a_e, value <= sup_a a F(m,s_c,a) <= (s_c+1)/(m+1) by T3c. Honest monitor with α₀=1%:
     k=8, n_h=1000 (§5's own example): global n_s=16 gives X=F*(8)=**0.087** (false-halt 2.6%); per-class s_c=5 gives **0.025** (false-halt 1.4%).
     k=32, n_h=10000: global 0.307 vs class-aware 0.019. k=100, n_h=10000: 0.958 vs 0.038. So the factor "L·α₀" of §5 is an artefact of the
     global counter: class-aware X ≈ α₀ + O(√(α₀ log k / m)), m = n_h/k. This theorem needs only M x = K(c x), no content-preservation, and uses
     only T3c plus a product count: it is easier than T5 and strictly stronger. The kill rule is a function of trusted-observable data, so
     it is capability-free. (Caveat: the false-halt figures assume a homogeneous honest miss rate α₀ across classes; with per-class
     rates α_e Blue must know them, which Greenblatt §2.3 allows via honest-model summary statistics but which is an honest-capability input to usefulness, not to safety.)
  3. *Not content-preserving*: classes {0,1,2}, views z0,z1; class 0→z0, class 1→z1, class 2→½z0+½z1. Uniform P_H gives value 0.1241
     (= F*(3)); P_H = δ_{class 2} gives 0.0828 (L=2). The optimiser is the column-max law of T4c', not "uniform over bad classes".
     (`check5_overlap_K.py`.) For randomised K that preserves classes, uniform is optimal and members-per-class are irrelevant (only c#P_H
     enters); the failure is overlap, not randomisation.
* **T5d** true and tight in the constant: P'=½δ_a+½δ_d, Q'=e^{-η}P'+(1-e^{-η})δ_e; move γ of P' from d to b and γ of Q' from a to e:
  hs'=0 but hs = (1+e^η)γ. But it is useless in practice: γ = max_x TV(M x, K(c x)) must be small for *every* x, which no real mediator
  satisfies relative to a coarse c.
* **T6.** (i) holds in my toy (20000 random programs, stuck-on-uninitialised-read semantics, desugar+first-occurrence renaming: 0
  mismatches), but only if the semantics of `for` is given independently (a direct big-step rule), else (i) is definitional; the language
  must have no `break/continue` (desugar `body; step` is wrong with them) and no block-scoped declarations (`for (int i...)` shadowing).
  (ii) is representation-dependent. With binary-tree `Seq`, `canon` does not identify `S;(T;U)` with `(S;T);U`, so a hand-written
  `init; while` in one association and a `for` in the other get different canonical forms (`check7_t6.py`: canon(p)≠canon(p') for
  semantically and while/for-equivalent programs). Then (iii)'s "every collusion signal carried only by loop form contributes exactly 0"
  is false for the tree shape of Seq (a free bit per statement pair). With statement *lists* and a splicing desugar (also for `if`
  branches that are a single statement) it holds. (iii) itself is trivial (hs is invariant under a bijection of the class space).
  Overclaim: "LASR's For/While marker ... is provably erased here" erases two channels (loop form, names) out of hundreds (Seq
  nesting, commutative operand order, `x+=1` vs `x=x+1`, dead code, constants, statement order, temporaries); the equivalence
  classes are still astronomically many, so T4c gives δ≈1 for canon exactly as for any other mediator. T6 is disconnected from the
  stack's bottleneck and expensive (weeks of Lean for a CompCert-style development).

---------------------------------------------------------------------------------------------------------------------------

## 3. Non-vacuity (Q3)

### N1 [MAJOR] The §5 table uses unrealistic honeypot counts
Recomputed (`check3_t5_numbers.py`): F*(k) values match the table to rounding (0.0037, 0.0318, 0.0110, 0.0104, 0.0445, 0.0324; bound
column 0.0099, 0.0594, 0.0240, 0.0176, 0.0672, 0.0614), so the arithmetic is right. The parameters are not realistic. Each honeypot
costs an H point and honeypots share the budget with audits: LASR N·b = 5000×2% = 100 = n_h + n_a (and §6 of the DESIGN itself says
n_h<=100); Greenblatt uses 30. The rows n_h = 1000, 5000, 10000, 100000 require N >= 5·10^4 - 5·10^6 tasks at 2%. At realistic budgets
(hard slack, exact F*(k)):

| n_h | n_s | k=1 | k=2 | k=4 | k=8 | k=32 |
|---|---|---|---|---|---|---|
| 30 | 0 | 0.012 | 0.024 | 0.048 | 0.096 | 0.386 |
| 30 | 1 | 0.028 | 0.055 | 0.111 | 0.222 | 0.759 |
| 30 | 3 | 0.065 | 0.130 | 0.259 | 0.519 | 0.986 |
| 100 | 0 | 0.004 | 0.007 | 0.015 | 0.029 | 0.117 |
| 100 | 2 | 0.014 | 0.027 | 0.055 | 0.110 | 0.438 |
| 100 | 5 | 0.032 | 0.064 | 0.127 | 0.254 | 0.906 |

So at LASR/Greenblatt budgets X <= 0.1 needs k <= 3-4; k = 32 is vacuous. §5's closed form "X ≈ 0.017·L" at α₀=1%, n_h=1000 is
an upper bound (exact F*(8)=0.087, F*(32)=0.349) and would need L <= 5 for X <= 0.1. And with n_h=100 the protocol has b=0 audits
(budget shared), which under the DESIGN's own halt semantics means the first benign false flag halts deployment (F1): the headline
parameter point is not a valid usefulness configuration of the modelled protocol.
LASR's own data point: Table 2 summariser + SFT self-recognition has safety 68.8% (UM-only, APPS) and 90.2% (UM+TM). Any ROC with
AUC a has TV >= 2a-1 (Youden), so for AUC 0.78-0.91 (the DESIGN cites this range from an earlier session; I could not verify it from the paper text, it is
in figures) δ_0 >= 0.56-0.82. T3 is vacuous at the only real empirical data point, as §6 admits.

### N2 [MAJOR] The "coarse-regime objection" answer is not honest as written
§5: "k counts classes of *bad* submissions after mediation, not of all submissions. The view of benign work can stay rich."
The mediator does not know which submissions are bad (that is the monitor's job). A content-only M that collapses *bad* submissions
into k classes but keeps benign ones rich must itself decide badness, i.e. be a perfect trusted classifier, and then U_M is pointless.
If instead M is class-agnostic (summariser, minifier), the evidence of badness the monitor needs is exactly the Red-choosable
detail, so c(Bad) is huge and T4c bites. The partial answer collapses unless badness is *structural* (action layer: a trusted
reference monitor extracts "touches credentials file / opens socket" and the view is that feature). Then U_M judges intent given a
coarse structural feature, which is a legitimate but different protocol (and shrinks k via Bad, not via M).

### N3 What can actually be said capability-free for rich content (honest answer)
1. For a *content-preserving* (or approximately decodable) mediator over a rich attack space: **no capability-free guarantee exists**,
   and the right formalisation of the impossibility is the hypothesis-free max-leakage floor T4c' (not T4c): no honeypot law,
   even an unconstrained Q, can beat Σ_z max_{x∈Bad} M(x,z). T4c is the corollary with an exact decoder, and is the weaker and more brittle
   of the two.
2. The only mediators with a capability-free guarantee independent of honeypot coverage are those that are *noisy by construction*:
   if M is ε-**local-DP** over Bad∪supp(P_H) (M(z|x) <= e^ε M(z|x') for all x, x'), then M x z <= e^ε q z for any P_H, hence L <= e^ε
   and δ_η = 0 for η>=ε, giving X <= (1-r)+e^ε (n_s+1)/(n_h+1) with no coverage requirement. The catch is utility: the honest monitor
   must still separate Bad from benign, so the LDP property can only be imposed *within* Bad (and Bad-vs-benign must stay distinguishable),
   which again requires M to know what bad looks like (N2). Max-leakage ℒ(M|Bad) is the exact
   price; measuring it needs a Blue-enumerable B̄ (F5), so the result is "capability-free relative to B̄", which is the action-layer
   interface. This is the best non-vacuous direction I see; it should replace T6 as the "rich content" story.
3. "Red must also produce a working attack" does not help capability-free: Bad already encodes working attacks, and the worst case
   is over all of Bad. It helps only if Bad is made small structurally (action layer). "Randomised honeypot construction from
   deployment outputs" (inject a trusted attack into real U_G outputs) covers the *wrapper* features of benign-mode outputs, but Red controls
   attack-mode wrappers, so the signal moves into the wrapper at attack time; it does not close the channel. Verifiable determinism
   (Lepinski-Micali-shelat, STOC 2005, cf. their CF protocols) is the cryptographic analogue of the structural escape: free-choice content is the channel; the only
   fix is to remove the freedom, and the action layer is the AI analogue.
4. Stratified, class-aware honeypot *tests* (T5', §7) are the best honest improvement inside the current framework: X ≈ α₀ plus a
   sampling term instead of k·α₀.

---------------------------------------------------------------------------------------------------------------------------

## 4. Prior art (Q4): name them

* T1, T2, T4a, T5d: hypothesis-testing/hockey-stick characterisation of (ε,δ)-DP; post-processing. T2 *is* the definition of (ε,δ)
  indistinguishability (Dwork-Roth; Wasserman-Zhou; Kairouz-Oh-Viswanath; Barthe-Olmedo; Balle-Barthe-Gaboardi). Lean precedent: Degenne's
  TestingLowerBounds `eGamma` (already in REUSE).
* T3c/T3c' and the whole honeypot count: **conformal-prediction validity / exchangeability** (Vovk-Gammerman-Shafer): with L=1, δ=0 the
  event "attack passes and <= s of n honeypots pass" is the event "attack is among the first s+1 of n+1 exchangeable passers", probability
  <= (s+1)/(n+1). Also the Bayes rule of succession; Greenblatt §3.4.2's Bayesian argument is the same statement. L>1 is a change
  of measure. This gives a second, Lean-friendlier proof route for the L-form (finite exchangeability via symmetric group) but the
  binomial identity is simpler.
* T4c / T4c': maximal leakage (Issa-Wagner-Kamath, IEEE-IT 2020: ℒ = log Σ_y max_x P(y|x)), min-entropy leakage (Smith 2009); T5b/T5c
  minimax structure: capacity-like (Sibson / Rényi-∞ capacity). The DESIGN's k is e^{ℒ} for deterministic content-only mediators.
* Collusion-free / steganography: Alwen-shelat-Visconti CRYPTO 2008 (mediator that filters and re-randomises traffic, their
  setting; web-checked) and Lepinski-Micali-shelat STOC 2005 (cited from memory, not re-checked): collusion-freeness is achieved only when the players' messages are (verifiably) determined
  by protocol inputs; free content is the subliminal channel. Cachin 1998: stego security as D(P_C‖P_S) bounds the warden's detection via the binary-divergence data
  processing inequality, the KL analogue of T2. Hopper-Langford-von Ahn (provably secure steganography). Motwani et al. 2402.07510
  (capacity / minimum-entropy-coupling, average-case Shannon); Roger-Greenblatt 2310.18512 (paraphrasing, measured bits-per-KB:
  an empirical channel-capacity budget, exactly the information the capability-free theory cannot supply).
* AI-control formal models the DESIGN does not cite: Griffin-Thomson-Shlegeris-Abate, "Games for AI Control" (2409.07985; POSG
  with Stackelberg solution), Bhatt et al. 2025 (Ctrl-Z, App. C statistical model that LASR extends), Korbak et al. control safety
  case sketches, Järviniemi acausal collusion (cited in LASR). The novelty claim of the DESIGN is modest and honest if limited to:
  (a) first-bad-decides under adaptive stateless-monitor adversaries with explicit budget/halting semantics, (b) the exact minimax
  value (T5b + my T3*), (c) machine-checked versions. Everything else is classical infrastructure; name it as such in the statements' docstrings.

---------------------------------------------------------------------------------------------------------------------------

## 5. Numbers (Q5)

* §5 table: all six F*(k) and bound values verified (scripts: `numerics/binom_bound.py`, mine). Only presentational: row 5 0.0445→"0.045" ok, row 6 0.0324→"0.032" ok.
* §5 prose: false-shutdown for n_h=1000, α₀=1%, n_s=16 is 2.64% (the claim "≲5%" is true); "X ≈ 0.017·L" is the *bound*; the exact F*(L) is 0.0109 (L=1),
  0.087 (L=8), 0.349 (L=32).
* §6 LASR parameters: 5/101 = 0.0495 (doc "0.050") ✓; soft F* at L=1 = 0.0183 ("0.018") ✓; "0.018·L" holds only while L <= 1/h* ≈ 20 (h*=0.0495). At L=8 F* = 0.1464 = 8×0.0183 ✓.
* §6 Eq. (1) is transcribed correctly from LASR App. B.1 (v2); "10 free upfront audits", "2% budget, N=5000, n_s=5", "n_h+n_a = N·b", Poisson approximation of the binomial,
  "(1-ε) only for dishonest misses": all ✓. LASR's main-text formula (§3.3) is a different parametrisation (FPR/TPR factors, N−10); the DESIGN
  uses the App. B one, fine.
* Not verified / unverifiable from the paper text: "AUC 0.55-0.62" and "0.78-0.91" (figures only), "our previous session's data check".

---------------------------------------------------------------------------------------------------------------------------

## 6. Lean feasibility (Q6)

Good: real-valued `Finset.sum` core, laws as hypotheses, induction on remaining rounds for T3a, `Nat.succ_mul_choose_eq` for the
binomial identity, DPI as `Σ_z max 0 (Σ_x K(x,z)(Px−γQx)) ≤ Σ_x max 0 (...)`. Risks:
1. **Faithfulness anchor.** `cat`/`surv`/`protocolCat` are hand-written recursions; the claim "this is the probability of the
   intended game" rests on the bridge (§7.5, listed last). Do it first, for small N and n_h, against a `PMF`/VCVio game, or define the
   protocol once as a PMF and *derive* the recursion. The numerics must also be extended to the Lean definitions (b, r, halting,
   kill schedule inside the protocol); my `check1_t3a.py` does b, r, halt, adaptive generators exactly.
2. **Laws must be hypotheses.** M x, PH, ρ, π ω hist, φ∈[0,1], κ_j∈[0,1], r∈[0,1] each need explicit `IsLaw`-type hypotheses;
   omitting one makes T3 false (π with mass >1). Add a negative test per hypothesis (a script that drops each and exhibits a violation).
3. **No `sSup` in statements.** `sup_{h∈[0,1]}` over ℝ is junk-valued (0) when unbounded and `max_{x∈Bad}` over empty Bad needs `sup'`. State
   pointwise: `∀ h ∈ [0,1], h * F n s h ≤ (s+1)/(n+1)` and `∀ A, (∀ x ∈ Bad, a x ≤ A) → cat ≤ (1-r) + r*A`. For the exact value state "≤ for all policies" and
   "∃ policy attaining" as two theorems.
4. `Hist` is an unbounded list type, fine for recursion on n, but T3a should be proved for a generator `π : α → X → ℝ` over an arbitrary history type to avoid
   dependent-sum noise.
5. T5b needs an explicit colluder built from a decoder g and a class index; fine (finite), but state it as a `Decidable` finite construction to keep the proof computational.
6. Do not build on `Real.exp η` hockey-stick for T3 at all if T3* (NP frontier, no η) is adopted; η-form is a lemma.
7. T6: an independent several-week development with no stack payoff; defer.

---------------------------------------------------------------------------------------------------------------------------

## 7. Five most important fixes, and what to formalise first

### Five fixes
1. **Fix the protocol semantics (F1).** Replace halt-at-b by a flag-rate/pacing rule with explicit post-flag action; keep halt as one named
   variant; state the defer variant with the exact value (≈1 once K·h ≳ 1, even with perfect coverage); add the usefulness companion (false-halt probability
   of an honest monitor) so safety theorems cannot be satisfied by halting.
2. **Relabel and re-shape the non-trusted quantities (F2, F3, F5).** r (worst-case-over-Bad recall), soft κ, enumerability of Bad and constructibility of P_H become
   explicit hypotheses; stop claiming X depends on trusted quantities only; keep (1-r) multiplied by S: V = S(h)[(1-r)+r·a].
3. **Redo §5 with realistic budgets (N1) and answer the coarse-regime objection honestly (N2/N3).** Delete the n_h >= 1000 rows; say plainly
   that for rich content-preserving mediators no capability-free guarantee exists; present the max-leakage floor and the LDP/structural-Bad escapes.
4. **Replace T3d/T4c/T5c by the exact/hypothesis-free forms.** T3* (V = max_x sup_h S(h)A_x(h), NP frontier), T4c' (Σ_z max_x M(x,z)), and T5' (stratified honeypots with
   class-aware slack: V <= (s_c+1)/(m+1)); drop "no honeypot law gives less" (counterexamples in §2).
5. **Make the Lean statements faithful (§6).** Bridge theorem first; law hypotheses with negative tests; pointwise statements (no `sSup`); the κ-general counting lemma instead of T3c+T3c'; defer T6.

### Theorems to formalise, in order
1. **T2'** (all real η): `E_P φ ≤ e^η E_Q φ + Σ max 0 (P − e^η Q)`, equality at the indicator; T4a (kernel DPI of hs). Tiny, classical.
2. **T0 (bridge)**: `protocolCat` = P(catastrophe) of an independent PMF/ProbComp definition of §2.2, small N, n_h; plus negative tests for every hypothesis.
3. **T3a'**: first-bad lemma by induction, with budget b, recall r, halt (and, separately, the pacing rule): `cat ≤ (1-r) + r·A` whenever `∀ x∈Bad, a_x ≤ A`; exact equality for
   a one-shot generator.
4. **T3b/c-general**: surv depends only on h; every kill schedule is a mixture of hard thresholds; `h·S_κ(h) ≤ (Σ_j ∏_{i<j}(1−κ_i))/(n_h+1)`; hard (n_s+1) and soft (n_s) as corollaries.
   Assembly: T3 for hard slack (and soft as a conditional theorem).
5. **T4c'**: `∀ Q law, (∀ x∈B, ∀ z, M x z ≤ L·Q z) → Σ_z max_{x∈B} M x z ≤ L`, plus the approximate-decoder floor; class-count T4c as a corollary.
6. **T5'**: content-only M, stratified honeypots, class-aware slack: `V ≤ (s_c+1)/(m+1)` with the explicit attaining colluder (tightness), and the honest-monitor false-halt bound.
7. **T3***: exact value V = max_x sup_h S(h)A_x(h) for r=1 (≤ for all policies; ∃ attaining). Needs the NP lemma (fractional knapsack); do after 1-6.
Defer: T3d, T5c as stated, T5d (keep as a lemma only), T6.

Open items I could not resolve: (a) whether a paced-budget (rate-test) halting rule admits an equally clean first-bad-decides theorem when the monitor may flag at exactly the allowed rate
(probably yes with a window argument; unproved); (b) which realistic mediators have small ℒ(M|B̄) (empirical question for Blue-sampled M; no theory can answer it).

---------------------------------------------------------------------------------------------------------------------------

## Appendix: check log (`<scratch>/`)
* `check1_t3a.py`: exact Fraction DP, protocol of §2.2 with b, r, halt; 300 instances: 0 bound violations, exact value = first-bad value.
* `check2_np_exact.py`: NP-frontier exact value vs full-protocol grid search over φ (200 random mediators): gap <= 2.6e-4; T3d(best η)/exact ∈ [1.000, 1.079].
* `check3_t5_numbers.py`: §5 table, realistic-budget table, class-aware vs global slack, stratified vs i.i.d.
* `check4_factor_e.py`: T3c holds for n<=300; min ratio 0.3685 (→1/e).
* `check5_overlap_K.py`: non-content-preserving mediator: uniform P_H not optimal.
* `check6_maxleak.py`: L(Q) >= Σ_z max_x M(x,z) for all Q, 0 violations / 2000 random mediators.
* `check7_t6.py`: toy-language desugar+rename semantic preservation (0/20000 mismatches); Seq-association counterexample to "loop form contributes 0".
* `check8_defer.py`: deferral-after-exhaustion value (X≈1 for K>=1000 even with perfect coverage).
* `check9_kappa.py`: general-κ bound sup_h h S_κ(h) <= E[G+1]/(n_h+1), 0 violations, ratio 1.0.
