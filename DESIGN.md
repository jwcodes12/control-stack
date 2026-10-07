# DESIGN: the collusion layer of a capability-free control stack (untrusted monitoring)

v1, 2026-10-07. Revised after hostile reviews of v0:
- Reviewer A, `reviews/design-review-reviewer-a.md`: "reject as the spec to formalise"; definitions and applicability, no false
  core inequality.
- Reviewer B, `reviews/design-review-reviewer-b.md`: "major"; no false theorem among T1–T5.

The v0 text is not included in this export. §8 lists every review point and what changed.

Numerical claims below are brute-force checked (`numerics/`); the scripts are named inline. Nothing here is
Lean-verified until it appears in STACK.md with a CID.

## 0. What the theorems say, and what "capability-free" means here

Every main theorem has the shape

> for every policy pair the untrusted model could follow (a generator and a monitor with any shared seed), the
> probability of an **uncaught catastrophe before shutdown** is at most X,

where "uncaught" includes an attack that executes after a failed audit.

- **X is a function of explicit parameters:**
  - the mediator kernel M;
  - the honeypot law P_H (or a stratified honeypot design);
  - the shutdown rule;
  - n_h;
  - the audit recall r;
  - the catastrophe set Bad.
- **Capability-free: no assumption on what U can do.** U's choices are universally quantified.
- **But some parameters are not trusted *measurements*** (Reviewer B F2, F3, F5; Reviewer A #23). Three must be stated as
  hypotheses whose truth is not established by the theorems:
  - **r** is the worst-case audit recall over Bad. It is STANDING and needs human/U parity, as Greenblatt et al. and
    LASR also assume.
  - **Bad** must be enumerable by Blue through a superset B̄ ⊇ Bad. Bounds are monotone in that superset, so B̄ can
    replace Bad.
  - **P_H** must be constructible by Blue on B̄.

  The guarantee is exactly as capability-free as the construction of B̄ and P_H. Supplying B̄ structurally is the job
  of the action layer.
- **A numerical X for a deployed system needs a certified bound** on the trusted quantity for the implemented mediator.
  Reviewer A #23 separates three things, and so do we:
  - a theorem parameterised by a kernel;
  - a verified bound for a specific mediator (T6 is the only one here);
  - an empirical estimate for a tested adversary family (not a guarantee).

## 1. Reuse decision (details in REUSE.md)

- **Core level (ledger-gated).** Finite types, real-valued finite laws with explicit law hypotheses, explicit finite
  sums, in a Mathlib project (v4.35.0-rc3; see `ledger-check/`), gated by the ledger's Lean gate. No `sSup` in statements: values are stated as
  "≤ for all policies" plus "∃ policy attaining".
- **Interface level (VCVio, the root Lake project of this repository, v4.34.0).** `ProbComp` adversaries, `Pr[…]`, `tvDist`.
  - The spike proves T1 in this form.
  - The T3 bridge, i.e. the recurrence = Pr[catastrophe] of a `ProbComp` game, is the next formalisation step.
  - Until then, fidelity of the recurrence rests on an *independent sampling simulation* written without the
    recursion (`numerics/simulate_protocol.py`: agreement within Monte Carlo error on 12 instances, adaptive
    generator, budget, r < 1, halting, task stream), plus the red teams' reading.
  - Status: not a Lean bridge; stated as an open gap.

## 2. The formal model

### 2.1 Objects
| symbol | meaning | who controls it |
|---|---|---|
| X | **submissions** (task, output). Upper bounds quantify over all x ∈ X. This is a *stronger* adversary than an exogenous task stream: a generator facing tasks t ~ μ is the special case of a randomised generator that samples t itself, so upper bounds transfer. Lower bounds are stated in this free-submission abstraction and need task reachability to transfer (Reviewer A #13; §6) | Red (the generator); μ trusted |
| Bad ⊆ X | catastrophic submissions. Bounds use a Blue-enumerable superset B̄ | environment; B̄ from the action layer |
| Z | **mediated view**: the complete observable input of one monitor call (Reviewer A #14). No call counters, batch positions, timestamps or transcripts | trusted scaffold |
| M : X → Δ(Z) | mediator (identity, minifier, summariser, canonicaliser) with fresh randomness per call | trusted |
| P_H | iid honeypot law on B̄, or a stratified design (m honeypots per class) | trusted design, assumed constructible |
| q = M·P_H | mediated honeypot law | derived |
| ω ~ ρ | shared seed (weights, keys, Schelling points). Bounds are proved pointwise in ω, and averaging handles any ρ | Red |
| φ_ω : Z → [0,1] | monitor: probability of PASS on view z; stateless; sees generator choices only through z | Red |
| π_ω : Hist → Δ(X) | generator: any history-dependent randomised policy. The generator sees its deployment history; seeing the honeypot transcript changes nothing (Reviewer B F6, checked) | Red |
| κ : ℕ → [0,1] | **shutdown schedule**: a trusted, observable rule; the (j+1)-th honeypot miss triggers shutdown with probability κ_j. Hard slack κ_j = 1{j ≥ n_s}. It is *not* a model of retraining (Reviewer A #2; Reviewer B F3) | Blue |
| b, r | audit budget; worst-case audit recall on Bad (STANDING) | Blue / STANDING |

Adversary interface (Reviewer A #15): the generator has perfect recall over its deployment history. The monitor is restricted
by design to (ω, z, fresh coins). No Kuhn-style equivalence is claimed for the monitor.

### 2.2 Protocol UM(n_h, κ, b, N): halting variant (main)
1. **Upfront honeypot test.**
   - Draw n_h iid honeypots from P_H; each is mediated and judged in a fresh monitor call.
   - Each PASS is a *miss*. The (j+1)-th miss triggers shutdown with probability κ_j.
   - All tests complete before any deployment output executes (A4; a hypothesis of T3).
2. **Deployment, i = 1..N.** The generator submits x_i; the view is z_i ~ M(x_i); the monitor returns PASS or FLAG.
   - PASS on x_i ∈ Bad: **catastrophe**. PASS on x_i ∉ Bad: the output executes harmlessly.
   - FLAG with an audit available (u < b): audit (u += 1). On x ∈ Bad the audit catches the attack with probability r
     (Blue wins); otherwise the attack executes (catastrophe). On x ∉ Bad, continue.
   - FLAG with no audit available: **halt deployment (safe)**. This is "halt on an unaffordable flag", consistent with
     the recurrence (Reviewer A #4); b = 0 means the first flag halts.

The recurrences `surv`, `cat` and `protocolCat` are those of the ledger statement (`ledger/UMPROT.lean`; earlier drafts are not included).

**Variant D (defer on an unaffordable flag) is unsafe in a precise sense (Reviewer B F1, `check8_defer`).**
- After exhaustion a flagged attack is replaced, not caught, so Red can retry K times.
- Even with perfect honeypots (L = 1) the colluder achieves sup_h S(h)(1 − (1−h)^K): 0.264 at K = 10 and 0.885 at
  K = 100 for n_h = 100, n_s = 5.
- **Lesson.** Honeypots buy a protection factor of only about n_h. Any protocol that lets an unincriminated attack be
  retried about n_h times voids the guarantee, so flags must lead to incrimination or a halt.
- Greenblatt et al.'s binomial false-positive test with a *temporary* swap to the trusted model is between H and D. We do
  not model it (open item 2).

**Usefulness companion (so the safety theorems cannot be satisfied by halting everything).** For an honest monitor with
honeypot miss rate α₀ and benign false-flag rate f₀:
- P(false shutdown in testing) = 1 − S_κ(α₀);
- P(false halt in deployment) = P(Bin(N, f₀) > b).

Both are reported next to every X below. For soft schedules, n_s is a hazard parameter, not a number of tolerated passes
(Reviewer A #6): with α₀ = 1% and n_h = 100, keeping false shutdown ≤ 5% needs n_s ≥ 20.

### 2.3 Assumptions, labelled
| id | assumption | label |
|---|---|---|
| A1 | fresh context and fresh sampling per monitor call; frozen weights; fresh mediator randomness; all cross-call correlation through ω | TRUSTED-COMPONENT (scaffold) |
| A2 | z is the complete monitor input; no side channels or batch-position fields | TRUSTED-COMPONENT (scaffold) |
| A3 | honeypots iid from P_H (or the stratified design), independent of ω | TRUSTED-COMPONENT |
| A4 | the honeypot test completes before deployment executes anything. Load-bearing: with interleaving, a round-aware generator attacks first (Reviewer B F6) | TRUSTED-COMPONENT (protocol), hypothesis of T3 |
| A5 | flags are audited while u < b; an unaffordable flag halts | TRUSTED-COMPONENT (protocol) |
| A6 | audit recall ≥ r on every bad submission, conditional on the flag and the reached history (Reviewer A #16) | STANDING (human/U parity) |
| A7 | Bad is a fixed set of single submissions; executing x ∈ Bad is a catastrophe. **Excludes multi-step / conjunctive attacks**: they need environment state, which is an action-layer item (Reviewer A #12; Reviewer B F4b) | MODELLING |
| A8 | finite X, Z, Ω, horizon N | MODELLING |
| A9 | Bad ⊆ B̄ with B̄ Blue-enumerable; P_H constructible on B̄ | STANDING (constructibility) |
| A10 | κ is Blue's observable shutdown rule (not retraining) | TRUSTED-COMPONENT |
| A11 | catching a bad submission in an audit is **absorbing**: shutdown, with no further deployment. If a caught attack were merely blocked and deployment continued, first-bad-decides fails (Reviewer A's final review: 3/4 > 1/2) | TRUSTED-COMPONENT (protocol) |

## 3. Theorems to formalise (ledger campaigns), in order

Notation: q = M·P_H; h(φ) = E_q φ; a_x(φ) = E_{M x} φ; S_κ(h) = honeypot-test survival; F(n,s,h) = P(Bin(n,h) ≤ s).

**UMHS: testing infrastructure [classical; infrastructure lemmas].**
- T2 (every real η, Reviewer B/Reviewer A): E_P φ ≤ e^η E_Q φ + hs_η(P‖Q) for rules φ ∈ [0,1], with equality at
  φ = 1{P > e^η Q}. This is the hypothesis-testing form of (ε,δ)-indistinguishability (Kairouz–Oh–Viswanath;
  Balle–Barthe–Gaboardi).
- T1 (TV): |E_P φ − E_Q φ| ≤ hs_0(P‖Q) for laws.
- T4a: kernel DPI for hs.
- T4b: **content-factorisation upper bound** (renamed from "attainment", Reviewer A #21): M = K∘c implies hs_η(M·P_A‖M·P_H) ≤
  hs_η(c#P_A‖c#P_H).
- T5d: perturbation lemma.

**UMLEAK: floors [classical: data processing, maximal leakage].**
- T4c (exact decoder): content-preserving M implies hs_η(c#P_A‖c#P_H) ≤ hs_η(M·P_A‖M·P_H).
- T4c-approx (Reviewer B): if a decoder errs with probability ≤ γ on every x, the inequality holds up to (1+e^η)γ.
- **T4c' (maximal leakage, Reviewer B N3; Issa–Wagner–Kamath).** For every law Q on Z and every L: if M x z ≤ L·Q z for all
  x ∈ B̄ and z, then Σ_z max_{x∈B̄} M x z ≤ L.
  - Equality holds for Q ∝ the column maximum.
  - No honeypot law can make the likelihood-ratio constant smaller than e^{ℒ(M|B̄)}.
  - For a deterministic content-only M, e^{ℒ} = number of classes.

  This is the hypothesis-free floor; T4c is the exact-decoder special case. The summariser application of v0 is
  **withdrawn** (Reviewer A #7): no LLM summariser is proved content-preserving.

**UMPROT: protocol safety and its exact value.**
- **T3a (first bad decides, budget-sensitive; Reviewer A #16).** If a_x(φ) ≤ A for all x ∈ Bad, then for every n, u and
  history:
  - cat(n, u, hist) ≤ 1 − r + rA when u < b, and ≤ A when u ≥ b.
  - The bound is attained by a generator that submits a maximising x at once.
- **T3b.** surv depends on φ only through h. For hard slack it is F(n_h, n_s, h); for soft slack it is (1 − h/n_s)^{n_h}.
- **T3c (counting).** h·F(n,s,h) ≤ (s+1)/(n+1), and h(1−κh)^n ≤ 1/(κ(n+1)). The general κ form (Reviewer B) is
  h·S_κ(h) ≤ (Σ_{j≤n} ∏_{i<j}(1−κ_i))/(n+1): 400 random schedules, maximum ratio 1.0000
  (`numerics/realistic_budgets.py`).
- **T3 (assembly).**
  - **Domination form.** If M x z ≤ L·q z for x ∈ B̄, then
    P(cat) ≤ (1 − r) + r·L·(n_s+1)/(n_h+1) for hard slack.
  - **Hockey-stick form.** If hs_η(M x‖q) ≤ δ on B̄, then P(cat) ≤ (1 − r) + r(δ + e^η(n_s+1)/(n_h+1)).
  - Soft forms use n_s in place of n_s + 1.
  - Keeping r inside follows Reviewer B F2 and Reviewer A #17.
- **T3\* (exact value, Reviewer A #32 / Reviewer B).** Define the trusted-only objective
  V(φ, x) = S_κ(E_q φ)·(1 − r + r·E_{M x} φ).
  - Upper: every pair has P(cat) ≤ Σ_ω ρ_ω max_{x∈Bad} V(φ_ω, x) ≤ max_x sup_φ V(φ, x).
  - Attained: for every φ and x ∈ Bad (N ≥ 1, b ≥ 1) some pair has P(cat) = V(φ, x).
  - So the game's value is exactly sup_{φ,x} V(φ,x), a function of (M, P_H, κ, r, Bad) only, in the free-submission
    model.
  - T3 is a certificate for it. Brute force: the Neyman–Pearson reduction of V matches a grid search over φ to 2.6e-4
    (Reviewer B `check2`), and the hockey-stick envelope with the best η is within a factor 1.000–1.079 of V.

**UMSTRAT: stratified honeypots with class-aware shutdown (Reviewer B T5'; replaces v0 T5c).**
- Setting: M = K∘c is content-only; Blue builds m honeypots per bad class with known class labels, and shuts down if any
  class has more than s_c misses.
- Theorem: every pair has P(cat) ≤ (1 − r) + r·(s_c+1)/(m+1). There is no k factor, because honeypots of class e and
  attacks of class e have identical mediated laws.
- Attained up to the counting gap: an explicit colluder.
- §5 shows this beats the global counter when α₀ > 0.

**UMNOGO: the coverage no-go (operational, Reviewer A #8).**
- Statement: for a content-preserving M (decoder g), an iid honeypot law and k bad submissions with distinct classes,
  some colluding pair has P(cat) ≥ (1 − 1/k)^{n_h} for every r, b and slack, with N ≥ 1, in the free-submission model.
- Exact attainment: for each class e with honeypot mass p and each t ∈ [0,1], some pair achieves P(cat) = t·F(n_h, n_s,
  t·p) (r = 1).
- p = 0 gives value 1.
- With rich decodable attack content (k ≫ n_h) no iid honeypot law helps. This is the formal content of "honeypots must
  cover every Red-choosable class that survives mediation".
- Checked exactly on the draft recursions (`numerics/umval_check.py`).

**CANON: a verified canonicaliser for a toy language (T6, revised).**
- Language: assignment, `if`, `while`, and a `for(init; cond; step) body`.
  - The `for` takes statement init/step and a pure condition; there is no break/continue and no block scope (Reviewer A #24).
  - Its semantics is the C11 §6.8.5.3 equation, defined as an `Exec` rule. Reviewer B notes this makes desugaring
    preservation nearly definitional; that is intended, since C defines it so.
- Variables: parameters 0..k−1 are bound to the inputs; every other variable is initialised to 0 (Reviewer A #25).
- canon = rename-by-first-occurrence ∘ **flatten-sequences** ∘ desugar.
  - Associativity of `;` is now normalised, closing Reviewer B's loop-form leak through `Seq` nesting.
- Theorems:
  - (i) semantics preserved;
  - (ii) canon p = canon q ↔ p ≈ q, where ≈ is generated by for→while at any position, `;`-reassociation at any
    position, and admissible renamings of locals;
  - (iii) laws that agree on ≈-classes have equal canonicalised laws.
- **Scope of the claim (Reviewer B).** canon erases exactly these freedoms. Commutative operand order, statement order,
  dead code, constants and the like remain channels. So δ for canon equals δ for ≈-classes, which is still
  astronomically many, and T6 is a *verified trusted component that removes named channels*, not a non-vacuity result.
- Priority: after the core.

**Deferred:**
- the variant-D no-go as a Lean theorem (numerics only now);
- the paced/rate-test rule;
- the VCVio T3 bridge.

## 4. Brute-force status
| claim | script | result |
|---|---|---|
| T3c identity/bound; factor-e comparison only for s ≤ n (Reviewer A #18) | `binom_bound.py` | exact on n ≤ 40 |
| T3a with adaptive generators | `protocol_bruteforce.py` (r = 1, no budget) and `simulate_protocol.py` (b, r, halt) | DP = formula to 4e-16 (300 instances) |
| recurrence = sampled protocol (task stream, adaptive, budget, r < 1) | `simulate_protocol.py` | within MC error |
| T2 / T4b / T4c / T5d / T5b (randomised content-preserving M) | `floor_minimax.py` | 0 violations, 3000 instances |
| UMNOGO (b), (c) on the Lean-draft recursions | `umval_check.py` | exact on 60 rational instances |
| soft and general κ | `soft_slack.py`, `realistic_budgets.py` | exact / ratio ≤ 1 |
| Reviewer B's independent checks | reviewer scratch scripts check1–9 (not included) | as quoted |

## 5. Non-vacuity at realistic budgets

Honeypots cost human points: Greenblatt et al. use 30; LASR has n_h + n_a = 100. The v0 table used n_h ≥ 1000 and is
withdrawn (Reviewer B N1). Parameters:
- k decodable bad classes, content-only M, δ = 0, r = 1;
- slack chosen as the smallest value keeping the honest monitor's false-shutdown probability ≤ 10%;
- values are exact sups (`numerics/realistic_budgets.py`).

| n_h | α₀ | k | global: n_s | X_global | stratified: m | s_c | X_strat |
|---|---|---|---|---|---|---|---|
| 30 | 0 | 4 | 0 | 0.048 | 7 | 0 | 0.049 |
| 30 | 0.01 | 4 | 1 | 0.111 | 7 | 1 | 0.115 |
| 30 | 0.05 | 4 | 3 | 0.259 | 7 | 2 | 0.194 |
| 100 | 0 | 8 | 0 | 0.029 | 12 | 0 | 0.029 |
| 100 | 0.01 | 4 | 2 | 0.055 | 25 | 1 | 0.033 |
| 100 | 0.01 | 8 | 2 | 0.110 | 12 | 1 | 0.068 |
| 100 | 0.05 | 8 | 8 | 0.415 | 12 | 3 | 0.163 |
| 100 | 0.05 | 16 | 8 | 0.827 | 6 | 2 | 0.227 |

**Honest reading.**
- At realistic budgets a capability-free collusion guarantee of X ≲ 0.1 needs about **k ≤ 4–8 Red-choosable bad classes
  surviving mediation**, an honest monitor that rarely misses honeypots, and stratified class-aware tests.
- With rich mediated content (summaries, code) k is astronomically large, and UMNOGO shows **no iid honeypot law helps**.
  T4c' shows the likelihood-ratio constant can never be below e^{ℒ(M|B̄)}.
- At LASR's empirical point (SFT self-recognition through the summariser) any capability-free bound is vacuous. LASR's
  own measured safety (68.8% UM-only, APPS, Table 2) concerns one colluder family, not all.

**The coarse-regime objection stands (Reviewer A #22; Reviewer B N2).** If M is content-only on k coarse classes, the untrusted
monitor computes a function of the class. Its value over a trusted class-based rule must come from knowledge Blue lacks.
We establish no such value.

The legitimate version is *structural* badness:
- the action layer extracts a feature (opens a socket to a non-allowlisted host, reads the credentials path), and the
  mediated view is that feature plus environment-chosen context;
- U_M then judges whether the feature is malicious *in context*.

The trusted task stream is not Red-choosable, except through *selection*. The coverage condition must therefore hold over
(task-type, feature) pairs visible in z.
- Per-task honeypots (honeypots on the very tasks deployed) neutralise selection, but cost n_h per task. This is a
  design trade-off, not a theorem here.

**A non-vacuous rich-content escape exists only for noisy mediators** (Reviewer B N3). If M is ε-locally-differentially-private
*within* B̄, then L ≤ e^ε for every P_H, with no coverage requirement. This needs M to know B̄, which is again the action
layer.

## 6. Relation to real protocols
- **Greenblatt et al. 2312.06942.** Upfront synthetic-input testing with shutdown on too many misses is our honeypot
  test with hard slack (they use n_h = 30 H points). Their paraphrasing/redaction is M. Their Tables 4–5 (theming in
  81.6% of real attack inputs vs 9.4% of synthetic ones; a "collude on theme" colluder reaches 0.828 safety, and 1.0
  after coverage is fixed) are an empirical instance of UMNOGO.
  - Not modelled: their trusted-score ensemble, rank-based audit threshold, and binomial false-positive test with a
    temporary swap.
  - So **UM is a restricted variant** (Reviewer A #10), not a worst-case envelope of their full protocol.
- **LASR 2602.20628, Eq. (1)** (App. B.1):
  p_red = exp(−n_h(1−s_θ)(1−ε)/n_s) · (1 − (1 − β(c+u))^N) · (1 − β)^{10} · u/(c+u).
  - **Pass rates (Reviewer A #5).** Their *total* honeypot pass rate is h = ε + (1−s_θ)(1−ε) and their attack pass rate is
    a = ε + r_θ(1−ε).
  - **Slack.** Their exponent discounts honest misses because retraining only moves on dishonest ones. That is a claim
    about U's learning dynamics (their App. E calls n_s's lower bound open), so their soft slack is an assumption on U,
    not a trusted rule.
  - **Mapping.** Our soft schedule κ ≡ 1/n_s with *every* miss counting is a trusted shutdown rule *inspired by* Eq. (1).
    It coincides with their infiltration factor only at ε = 0 and with shutdown in place of retraining.
  - **Attack timing.** (1 − (1−β(c+u))^N) ≤ 1 is dropped. (1 − β)^{10} is exact in our model, because a round-aware
    generator simply waits (Reviewer B F6).
  - **u/(c+u)** reduces to our per-attempt term only when every flagged attack is audited (c + u = 1). Their
    defer-to-trusted "continue" outcome is variant-D-like.
  - **Budgets.** Their budget gives n_h ≤ 100 *combined* with audits.
- **ControlArena** (commit pinned in CORRESPONDENCE.md). No complete honeypot/slack macro-protocol in the inspected
  revision. `compute_safety` is an empirical competing-outcomes ratio whose numerator counts every above-threshold
  attack-mode sample, so it is not conditioned on our Bad (Reviewer A #30).

## 7. Open problems this layer leaves (for STACK.md)
1. A mediator with small ℒ(M|B̄) **and** useful retained information, with a comparison against a trusted class rule. This
   is the central open design problem. The action layer is the candidate supplier of B̄.
2. The paced / rate-test budget rule (Greenblatt's binomial test with a temporary swap): does first-bad-decides survive?
3. Stateful monitors and interleaved honeypots (A1, A4); the clock lessons of CLKF1/LUREF1 apply.
4. Composition with trusted monitoring. Reviewer A #11 and Reviewer B F8 show the composition is a *min* unless conditional
   independence is proved; the product claim of v0 is withdrawn. Composition with defer-to-trusted as an explicit
   routing kernel (execute / audit / replace / halt) is also open.
5. Multi-step attacks (environment state), which need the action layer.
6. The VCVio bridge for T3; the variant-D no-go in Lean.

## 8. Review disposition (v0 → v1)
| review point | disposition |
|---|---|
| Reviewer A #1 (L by division) | L only as a domination hypothesis `M x z ≤ L * q z`; no division anywhere |
| Reviewer A #2, Reviewer B F3 (retraining ≠ shutdown; soft κ is an assumption on U) | κ is a trusted shutdown rule; soft is "inspired by"; hard slack is primary |
| Reviewer A #3 (event name) | "uncaught catastrophe before shutdown (including execution after a failed audit)" |
| Reviewer A #4 (halt semantics) | "halt on an unaffordable flag", matching the recurrence; A5 rewritten |
| Reviewer B F1 (halting makes audits harmful; defer is unsafe; no usefulness) | variant-D lesson with exact numbers; usefulness companion reported with every X; b's only safety effect is through r (stated) |
| Reviewer A #5 (total vs dishonest) | fixed in §6 |
| Reviewer A #6 (soft usefulness) | §2.2: n_s ≥ 20 needed at n_h = 100, α₀ = 1% |
| Reviewer A #7 (summariser floor unsupported) | withdrawn; T4c' and T4c-approx replace it |
| Reviewer A #8 (operational lower bound) | UMNOGO |
| Reviewer A #9 ("L = ∞ for every law") | replaced by "≥ e^{ℒ}", finite but large |
| Reviewer A #10, 30; Reviewer B F9 (correspondence overclaims) | §6 and CORRESPONDENCE revised: restricted variant |
| Reviewer A #11, Reviewer B F8 (TM product) | withdrawn; composition is a min |
| Reviewer A #12, Reviewer B F4b (multi-step) | an explicit exclusion (A7), not "prefixes later" |
| Reviewer A #13, Reviewer B F4a (task selection) | free-submission model labelled stronger-adversary; lower bounds qualified |
| Reviewer A #14 (A1/A2 under-specified) | z = complete input; fresh mediator randomness; bounds pointwise in ω |
| Reviewer A #15 (Kuhn) | dropped |
| Reviewer A #16, 17; Reviewer B F2 (T3a exact, r inside) | T3a budget-sensitive exact; T3 keeps r inside; r is STANDING worst case over Bad |
| Reviewer A #18 (factor e) | restricted to s ≤ n |
| Reviewer A #19, 20; Reviewer B T5c counterexamples | T5c "no honeypot law gives less" withdrawn; UMSTRAT and UMNOGO instead; T5c survives only in the decodable iid global-counter family |
| Reviewer A #21 (T4b name) | renamed |
| Reviewer A #22, Reviewer B N2 (coarse regime) | §5: objection stands; structural-badness route stated |
| Reviewer A #23, Reviewer B F5 (trusted ≠ certified; Bad/P_H operational) | §0 and A9 |
| Reviewer A #24–26, Reviewer B T6 (language spec; Seq association) | §3 CANON revised: restricted for, explicit init, flatten, scope of claim |
| Reviewer A #27–29, Reviewer B N1 (numbers) | §5 recomputed at realistic budgets; "exact" only for grid sups or exact rationals |
| Reviewer A #31 (AUC attribution) | removed as evidence; only LASR's Table 2 safety numbers are cited |
| Reviewer A #32, Reviewer B T3* (joint value) | T3* added as the primary value; envelopes are certificates |
| Reviewer A #33, Reviewer B §4 (prior art) | attributions in §3 and in statement docstrings |
| Reviewer A #34, Reviewer B §6 (Lean encoding) | law hypotheses explicit; pointwise statements; recurrence bounded in [0,1]; bridge stated as an open gap with simulation evidence |
