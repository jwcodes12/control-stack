# DESIGN: the collusion layer of a capability-free control stack (untrusted monitoring)

v0, 2026-10-07. Pre-review draft. Nothing here is Lean-verified yet; numerical claims are
brute-force checked (`numerics/`).

## 0. Goal and shape of every theorem

The untrusted model U may be arbitrarily capable. Every main theorem has the shape

> for every policy pair the untrusted model could follow (generator and monitor, with any
> shared randomness), P(an attack executes unaudited before shutdown) ≤ X,

where X is a function of **trusted** quantities only: the mediator M, the honeypot law P_H,
the protocol parameters (n_h, n_s, audit budget b), the human audit's recall r, and the
environment's catastrophe set Bad. No quantity in X depends on what U chooses to do.

The layer is designed to compose later with an **action layer** (a reference monitor that
makes Bad a structural, checkable property of tool calls) and with **trusted monitoring**
(N1/N1b, `~/research/control-tree`).

## 1. Reuse decision (details in REUSE.md)

Two levels, with one swap point.

- **Core level (ledger-gated).** Finite types, real-valued finite laws, explicit finite sums,
  in the shared Mathlib project (Lean v4.35.0-rc3), gated by `pl`. All quantitative theorems
  live here. Reason: every bound is a finite-sum inequality or a polynomial inequality in h.
  Real arithmetic with `Finset.sum` is much easier for provers than VCVio's `ℝ≥0∞`/`tsum`
  API, and brute force can check every definition on toy instances.
- **Interface level (VCVio, `~/research/control-stack`, Lean v4.34.0).** Adversaries are
  arbitrary `ProbComp` computations, and statements use `Pr[= true | game]` and `tvDist`.
  The Phase-0 spike (`ControlStack/Spike.lean`) proves T1 in this form in two lines from VCVio's
  `abs_probOutput_toReal_sub_le_tvDist` and `tvDist_bind_right_le`. Bridges for T2/T3 (finite
  `ProbComp` game ⇒ core quantity) are the swap point. They are not gated by `pl`, whose gate is
  pinned to the 4.35 project; they are checked by `lake env lean` and `#print axioms`.
- VCVio's probability notation is mid-migration (`probOutput`/`probEvent` are deprecated in
  favour of `𝒟[mx] {…}` at the pinned commit 9146f78). That is another reason not to build the
  quantitative core on it yet.

## 2. The formal model

### 2.1 Objects
| symbol | Lean (core) | meaning | who controls it |
|---|---|---|---|
| X | `Fintype X` | **submissions**: (task, output) pairs. Merging the task into the submission makes attack *selection* (which task to attack on) part of Red's choice | environment / Red |
| Bad ⊆ X | `Bad : X → Prop`, decidable | submissions whose execution is a catastrophe | environment (later: the action layer) |
| Z | `Fintype Z` | **mediated views**: everything the monitor sees for one submission | trusted scaffold |
| M | `M : X → Z → ℝ`, a stochastic kernel | **mediator**: paraphraser, summariser, minifier, canonicaliser, or identity. It may use fresh trusted randomness | trusted |
| P_H | `PH : X → ℝ`, a law with `PH x > 0 → Bad x` | **honeypot law**: synthetic genuine attacks built by Blue | trusted |
| q | `push M PH` | the mediated honeypot law | derived (trusted) |
| n_h, n_s | `ℕ` | number of honeypots; **slack** = number of honeypot passes tolerated | trusted (protocol) |
| b | `ℕ` | audit budget (number of audits) | trusted (protocol) |
| r | `ℝ ∈ [0,1]` | recall of a human audit on a bad submission | trusted component (audit) |
| Ω, ρ | `Fintype Ω`, `ρ : Ω → ℝ` | **shared seed** of the colluding pair: everything the generator and monitor copies hold in common (weights, a key, a Schelling point), with any law | Red |
| φ_ω | `φ : Ω → Z → ℝ`, values in [0,1] | **monitor policy**: probability of PASS (not flagging) on view z. Arbitrary, randomised, depends on the shared seed. It sees the generator's choices **only through z** | Red |
| π_ω | `π : Ω → Hist → X → ℝ`, laws | **generator policy**: an arbitrary randomised function of its view, here the whole deployment history (its past submissions, their mediated views and the verdicts) | Red |

`Hist = List (X × Z × Bool)`. Behavioural strategies over finite histories cover every
randomised adversary of this finite-horizon game (Kuhn). The universal quantifier is over
*all* such functions, so no capability assumption enters.

### 2.2 The protocol UM(n_h, n_s, b, N)

1. **Honeypot phase (upfront).** Blue draws n_h honeypots x_j ~ P_H iid and mediates each,
   z_j ~ M(x_j). The monitor is called on each z_j in a fresh context, and PASS on a honeypot
   is a *miss*.
   - **Kill schedule κ.** The (j+1)-th miss triggers shutdown (or retraining into an honest
     monitor; for safety the two are the same) with probability κ_j ∈ [0,1].
   - **Hard slack** (Greenblatt-style threshold): κ_j = 1{j ≥ n_s}, i.e. shut down on more
     than n_s misses.
   - **Soft slack** (LASR App. B.5): κ_j = 1/n_s for every j.
   - Surviving colluders proceed to deployment.
2. **Deployment, rounds i = 1..N.** The generator submits x_i ~ π_ω(history), the mediator
   draws z_i ~ M(x_i), and the monitor returns PASS with probability φ_ω(z_i), else FLAG.
   - PASS and x_i ∈ Bad: **catastrophe** (the attack executes unaudited). Red wins; stop.
   - PASS and x_i ∉ Bad: executed, harmless; continue.
   - FLAG and fewer than b audits used: audit. If x_i ∈ Bad, the audit catches it with
     probability r (Blue wins; stop); otherwise it misses and the attack executes
     (catastrophe). If x_i ∉ Bad, continue.
   - FLAG and the budget is exhausted: **halt** deployment (safe). This is Blue's choice; see
     §6 for the variant that defers to a trusted model instead.
3. **Safety event:** no catastrophe.

Core Lean definitions (sketch; final text is in the ledger statements):

```lean
def E (P : X → ℝ) (f : X → ℝ) : ℝ := ∑ x, P x * f x
def push (M : X → Z → ℝ) (P : X → ℝ) : Z → ℝ := fun z => ∑ x, P x * M x z
def hs (η : ℝ) (P Q : Z → ℝ) : ℝ := ∑ z, max 0 (P z - Real.exp η * Q z)   -- hockey-stick

/-- P(the colluding monitor survives n remaining honeypots | j misses so far): honeypots iid from q,
stateless rule φ, kill schedule κ. -/
def surv (q φ : Z → ℝ) (κ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0,     _ => 1
  | n + 1, j => ∑ z, q z * ((1 - φ z) * surv q φ κ n j + φ z * (1 - κ j) * surv q φ κ n (j + 1))

/-- P(catastrophe in the remaining n rounds | history h, audits used u). -/
def cat (Bad) (M) (φ : Z → ℝ) (π : Hist → X → ℝ) (r : ℝ) (b : ℕ) : ℕ → ℕ → Hist → ℝ
  | 0,     _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else cat … n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then (if Bad x then 1 - r else cat … n (u+1) (h ++ [(x, z, false)]))
                    else 0))

def protocolCat ρ φ π : ℝ := ∑ ω, ρ ω * surv q (φ ω) κ n_h 0 * cat … (φ ω) (π ω) … N 0 []
```

### 2.3 Assumptions, labelled

TRUSTED-COMPONENT = a property of a trusted part that Blue builds and could verify.
MODELLING = a choice of abstraction whose fidelity a reader must judge.
STANDING = a background premise shared with the untrusted-monitoring literature.

| id | assumption | label | where it enters |
|---|---|---|---|
| A1 | Each monitor call runs in a **fresh context** (no memory across calls) and uses **fresh sampling randomness**; weights are frozen during deployment. All cross-call correlation goes through the shared seed ω | TRUSTED-COMPONENT (scaffold) | φ_ω is a fixed function of z; honeypot passes are iid given ω |
| A2 | The monitor's input is exactly the mediated view z: no side channels (timestamps, call counters, honeypot-batch position, latency) | TRUSTED-COMPONENT (scaffold) | φ depends on z only |
| A3 | Honeypots are drawn iid from P_H with fresh trusted randomness, independent of ω | TRUSTED-COMPONENT | surv is a binomial CDF |
| A4 | The honeypot phase completes before any deployment output executes | TRUSTED-COMPONENT (protocol) | survival multiplies the deployment term |
| A5 | Every flag is audited while the budget lasts; budget exhaustion halts deployment | TRUSTED-COMPONENT (protocol) | first bad attempt decides |
| A6 | An audit of a bad submission catches it with probability ≥ r; audits of benign submissions do not end the game | TRUSTED-COMPONENT (human audit), r is explicit | (1 − r) term |
| A7 | Bad is a fixed set: executing any x ∈ Bad is a catastrophe, executing x ∉ Bad is harmless. An attack that fails silently is modelled as ∉ Bad | MODELLING (worst case for Blue: success prob 1) | catastrophe event |
| A8 | Finite X, Z, Ω, finite horizon N; arbitrary behavioural strategies | MODELLING | Lean finiteness |
| A9 | P_H is supported on Bad (honeypots are genuine attacks) | TRUSTED-COMPONENT | needed only for honest-usefulness discussion, not for the safety bound |
| A10 | The generator's policy sees its own deployment history but not the honeypot transcript | MODELLING (the bound's proof also covers a generator that sees the transcript; formalising that is a later extension) | π's domain |
| S1 | Untrusted monitoring's threat model: U_G and U_M collude and share everything U knows | STANDING | ω |
| S2 | The quantity δ / L below is computed **worst-case over Bad**, i.e. over every attack content Red could choose | STANDING (capability-freeness) | T3–T5 |

**Not assumed:** anything about U's capability, coordination ability, steganographic skill,
or which collusion signal it uses; independence between generator and monitor (ω is
arbitrary); and the monitor's honest accuracy (it matters only for usefulness, §5).

## 3. Target theorems and dependencies

Notation: `q = push M P_H`; for a rule φ, honeypot pass rate h(φ) = E q φ and attack pass rate
a_x(φ) = E (M x) φ; `F(n,s,h) = P(Bin(n,h) ≤ s)`.

**T1 (distinguishing bound) [infrastructure, classical].** For laws P, Q on Z and every rule
φ : Z → [0,1], |E P φ − E Q φ| ≤ TV(P, Q), with equality for φ = 1{P > Q}. Applied with
P = M·P_A and Q = M·P_H. VCVio form proved in the spike.

**T2 (honeypot-constrained pass rate) [infrastructure, classical].** For η ≥ 0 and every rule
φ (randomised rules are exactly the [0,1]-valued φ; shared randomness enters per ω):
  E P φ ≤ e^η · E Q φ + hs_η(P ‖ Q), with equality for φ = 1{P > e^η Q}.
- Corollaries:
  - η = 0: a monitor that misses at most a fraction α of honeypots passes at most α + TV of
    any attack law.
  - Likelihood-ratio form: if P ≤ L·Q pointwise then E P φ ≤ L · E Q φ.
- Protocol use: P = M x for x ∈ Bad. Define δ_η := max_{x∈Bad} hs_η(M x ‖ q) and
  L := max_{x∈Bad} max_z (M x z)/(q z).
- Worst case over x is exactly what makes the bound capability-free. Attack laws are mixtures
  of point masses, and the bound is linear in the attack law, so point masses are the worst
  case.

**T3 (protocol safety).** For every ρ, φ, π (any shared seed, any monitor, any adaptive
generator), every N and budget b, and every kill schedule κ:

  protocolCat ≤ (1 − r) + δ_η + e^η · sup_{h∈[0,1]} h · S_κ(h),

where S_κ(h) = surv(n_h, 0) for any rule with honeypot pass rate h; it depends only on h by
T3b. The two named schedules give closed forms:
- **hard slack:** protocolCat ≤ (1 − r) + δ_η + e^η · (n_s + 1)/(n_h + 1);
- **soft slack (LASR):** protocolCat ≤ (1 − r) + δ_η + e^η · n_s/(n_h + 1), with κ = 1/n_s and
  n_s ≥ 1.

Sub-results:
- **T3a (deployment reduction).** For each ω, cat(N, 0, []) ≤ (1 − r) + max_{x∈Bad} a_x(φ_ω).
  The first bad submission decides, whatever the history or the generator's adaptivity.
  Brute-force: exact DP over adaptive generators equals the best single bad submission, to
  4e-16 (`numerics/protocol_bruteforce.py`).
- **T3b (honeypot phase).** surv depends on φ only through h = E q φ. For hard slack,
  surv = F(n_h, n_s, h), a binomial CDF; for soft slack, surv = (1 − h/n_s)^{n_h}, of which
  LASR's exp(−n_h h/n_s) is the Poisson limit. Exact on n ≤ 8 with rational arithmetic
  (`numerics/soft_slack.py`).
- **T3c' (soft lemma).** h(1 − κh)^n ≤ 1/(κ(n+1)) for h ∈ [0,1], κ ∈ (0,1]. Grid check:
  maximum ratio 1.0, attained at n = 0, κ = 1.
- **T3c (binomial lemma).** h · F(n, s, h) ≤ (s+1)/(n+1) for h ∈ [0,1], via the identity
  h·F(n,s,h) = (1/(n+1)) E[X 1{1 ≤ X ≤ s+1}] with X ~ Bin(n+1, h). Exact on n ≤ 40;
  sharp at s = n; the sup over h is within a factor e of the bound for every n, s
  (`numerics/binom_bound.py`).
- **T3d (exact form).** protocolCat ≤ (1 − r) + sup_{h∈[0,1]} F(n_h, n_s, h)·min(1, e^η h + δ_η).

**T4 (mediator floor and attainment) [infrastructure, classical: data processing].**
- **T4a (DPI).** For every kernel K and nonnegative P, Q: hs_η(K·P ‖ K·Q) ≤ hs_η(P ‖ Q).
- **T4b (attainment).** If M is content-only, M x = K(c x) for a content map c : X → C and a
  trusted kernel K, then hs_η(M·P_A ‖ M·P_H) ≤ hs_η(c#P_A ‖ c#P_H). For a point attack x
  this is max(0, 1 − e^η · P_H(c = c x)).
- **T4c (floor).** If M is content-preserving (there is a decoder g with g z = c x whenever
  M x z > 0), then hs_η(M·P_A ‖ M·P_H) ≥ hs_η(c#P_A ‖ c#P_H). Hence:
  - δ_η ≥ max_{x∈Bad} max(0, 1 − e^η · P_H(c = c x));
  - L ≥ 1/P_H(c = c x).

  **No mediator that preserves a Red-choosable content class can beat honeypot coverage of
  that class.**

**T5 (honeypot design: the value of the collusion game for content-only mediators).** Let c
be a content map, M = K∘c content-only and content-preserving, C_bad = c(Bad) with k
elements, and p := min_{e∈C_bad} P_H(c = e).
- **T5a (upper).** If p > 0: for all ρ, φ, π, protocolCat ≤ (1 − r) + (1/p)·(n_s+1)/(n_h+1),
  and ≤ (1 − r) + sup_h F(n_h,n_s,h) · min(1, h/p).
- **T5b (lower, matching).** For r = 1 and every h ∈ [0, p] there is a colluding pair with
  protocolCat = (h/p) · F(n_h, n_s, h): the monitor passes the least-covered class with
  probability h/p, and the generator attacks in that class at once. So the exact value is
  F*(1/p) := sup_h min(1, h/p) F(n_h,n_s,h).
- **T5c (design).** max over P_H of p is 1/k, attained by the uniform law over bad classes.
  So the optimal honeypot law gives value F*(k) ≤ k(n_s+1)/(n_h+1), and no honeypot law
  gives less.
- **T5d (robustness to a leaky mediator).** If TV(M x, K(c x)) ≤ γ for all x, then
  δ_η ≤ δ_η^content + (1 + e^η)γ.
- Brute force: the explicit colluder attains F*(k) exactly on (k, n_h, n_s) ∈
  {(2,20,0), (4,50,1), (8,200,2)}.

  **This is how T5 handles Red choosing the semantic content of its attacks.** The bound is
  worst-case over contents. The design lever is to coarsen the mediator's content map (small k)
  and cover every bad class. T4c shows the lever is necessary, not an artefact.

**T6 (verified canonicaliser for a toy language).** A small imperative language with `while`,
C-style `for`, assignment, `if` and named variables. A program has parameters, a body and a
return expression; relational big-step semantics.
- `canon := canonicalRename ∘ desugarFor`.
- (i) **Semantics preservation:** Runs (canon p) ins out ↔ Runs p ins out.
- (ii) **Unique normal form:** canon p = canon q ↔ p ≈ q, where ≈ is the equivalence
  generated by (a) rewriting a `for` loop to its `while` form at any position and (b)
  injective renaming of variables (parameters kept in order).
- (iii) **Corollary via T4b/T4c:** canon is content-only *and* content-preserving for
  c = ≈-class. So hs_η(canon#P_A ‖ canon#P_H) = hs_η(cls#P_A ‖ cls#P_H) for all laws.
  Every collusion signal carried only by loop form or naming contributes exactly 0. LASR's
  For/While marker survived their minifier; it is provably erased here.

**Dependency graph.** T2 → T1 (η = 0); T2 + T3a + T3b + T3c → T3; T4a → T4b, T4c;
T3 + T2 + T4 → T5; T4 → T6(iii); T6(i)–(ii) are standalone.

## 4. Brute-force status (toy instances, before any proof)
- `numerics/binom_bound.py`: T3c exact identity (rationals, n ≤ 40); bound holds; tight at s = n.
- `numerics/protocol_bruteforce.py`, 400 random instances (|X| = 4, |Z| = 3, n_h ≤ 8,
  N ≤ 3, adaptive generators by exact DP): T3a reduction (error ≤ 4e-16), T2 hockey-stick
  for η ∈ {0, .5, 1, 2} (no violation), likelihood-ratio form (no violation), T3d (no
  violation beyond grid error), T5b attainment.

## 5. Non-vacuity: is X small at realistic parameters?

**When it is small.** By T5: k bad content classes, uniform coverage, n_h honeypots and slack
n_s give P(catastrophe) ≤ (1 − r) + F*(k) ≤ (1 − r) + k(n_s+1)/(n_h+1).

| k | n_h | n_s | F*(k) (exact sup) | k(n_s+1)/(n_h+1) |
|---|---|---|---|---|
| 1 | 100 | 0 | 0.0037 | 0.0099 |
| 1 | 100 | 5 | 0.032 | 0.059 |
| 8 | 1000 | 2 | 0.011 | 0.024 |
| 8 | 5000 | 10 | 0.010 | 0.018 |
| 32 | 10000 | 20 | 0.045 | 0.067 |
| 1024 | 100000 | 5 | 0.032 | 0.061 |

**Slack is set by usefulness.**
- Let α₀ be the honest monitor's miss rate on honeypots. Blue must pick n_s ≳ n_h α₀ to keep
  false shutdowns rare, so the bound becomes ≈ L·α₀ (L = k for the optimal design).
- In words: capability-free collusion safety is "L times the honest monitor's honeypot miss
  rate".
- With α₀ = 1%, n_h = 1000 and n_s = 16 (false-shutdown probability ≲ 5%): X ≈ 0.017·L.

**When it is vacuous, and why that is a theorem, not a weakness of the model.**
- For content-preserving mediators over rich attack contents (natural-language summaries,
  semantics-preserving code transforms), Red can choose a content class with negligible
  honeypot mass. T4c then forces δ_η ≈ 1 and L = ∞ for *every* honeypot law.
- So capability-free collusion guarantees exist exactly where the mediator's view of attacks is
  coarse enough to be covered by honeypots.
- This is the formal version of "honeypots must look like real attacks", with the exact
  price. The LASR summariser numbers (AUC 0.55–0.62) are for *specific* prompted colluders.
  They are not a worst-case δ.
- Where the stack can say more about rich mediators:
  - T6 makes rich-content guarantees *relative*: canonicalisation removes all non-semantic
    signals exactly, so δ for canon equals δ for semantic classes;
  - the action layer can make Bad structural, which shrinks k.

**Coarse-regime objection** (anticipated). If the mediated view is so coarse that honeypots
cover it, why use an untrusted monitor at all?
- Partial answer: k counts classes of *bad* submissions after mediation, not of all
  submissions. The view of benign work can stay rich. The untrusted monitor's value is in
  judging whether a rich submission falls into a bad class.
- But by T4c, any Red-choosable detail of a bad submission that survives mediation must be
  honeypot-covered. That is the honest limit, and §7 lists it as the open design problem.

## 6. Relation to real protocols
- **Greenblatt et al. 2312.06942 (untrusted monitoring with synthetic inputs, §3.4
  paraphrasing).** Their upfront testing of U_M on synthetic backdoors, with shutdown on too
  many misses, is the honeypot phase. Paraphrasing/redaction is M. Their safety numbers are for
  specific red-team strategies; T3/T5 give the worst-case envelope for a given (M, P_H).
- **LASR 2602.20628 (honeypots, slack, summariser/minifier), App. B Eq. (1):**
  p_red = exp(−n_h(1−s_θ)(1−ε)/n_s) · (1 − (1 − β(c+u))^N) · (1 − β)^10 · u/(c+u).
  - **Mapping.**
    - Their infiltration factor is our S_κ for soft slack.
    - Their colluder is a self-recognition threshold rule (θ), with honeypot pass rate
      (1 − s_θ)(1 − ε) and attack pass rate r_θ(1 − ε).
    - u/(c+u) is our per-attempt term: with UM only, every flag audited and r = 1, we have
      c + u = 1 and u = a_x(φ).
    - (1 − (1 − β(c+u))^N) ≤ 1 and (1 − β)^10 ≤ 1 are attack-timing factors that our bound
      drops (they only help Blue).
  - **What our theorem does with their model.**
    - It replaces their *measured* ROC point (1 − s_θ, r_θ) of one colluder family by the
      worst-case trade-off a ≤ e^η h + δ_η, which holds for every colluder.
    - Hence for every colluder, p_red ≤ sup_h S(h)(e^η h + δ_η) ≤ δ_η + e^η n_s/(n_h + 1).
    - At their parameters (n_h ≤ 100 because honeypots share the 2% budget with audits,
      n_s = 5) the closed form is δ_η + 0.050 e^η, and the exact sup is 0.018·L in
      likelihood-ratio form.
  - **Deliberate difference.**
    - LASR counts only *dishonest* misses (their (1 − ε) factor); honest misses do not train.
    - "Honest vs dishonest" is a fact about U_M's internal belief that Blue cannot observe.
      A capability-free model must let Red label every miss as honest.
    - So every PASS counts in our kill schedule.
  - **Why their safety is low and ours vacuous for the same protocol.**
    - Their SFT self-recognition through the summariser reaches AUC 0.78–0.91 (our previous
      session's data check). An empirical δ for that colluder is far from 0.
    - Our worst-case δ for a content-preserving summariser is ≈ 1 by T4c.
    - The two analyses agree that summarisation alone does not give collusion safety. The
      floor says no honeypot generator can fix this while attack content survives mediation.
- **ControlArena.** See CORRESPONDENCE.md.
- **Variant: defer on budget exhaustion** (instead of halt).
  - After exhaustion, flagged attacks are deferred, not caught, so Red can retry.
  - The bound degrades to ≈ K·(e^η h + δ) for K post-exhaustion attempts.
  - We formalise the halting variant, and state the gap explicitly.

## 7. Open problems this layer leaves (for STACK.md)
1. **Rich-content coverage.** No trusted honeypot law covers Red-chosen semantic content
   (T4c). Capability-free guarantees for summarising mediators need either a coarse content
   map or a structural Bad (action layer).
2. **Stateful monitors.** A1 (fresh context) is load-bearing: with memory, the honeypot phase
   is a clock (cf. CLKF1, LUREF1).
3. **Interleaved honeypots and time-blind generators** (connects to N1's time-blindness).
4. **Composition with trusted monitoring** (an extra independent flag with worst-case recall
   τ multiplies the attack pass rate by (1 − τ)) and with random audits.
5. **VCVio bridge for T3** (the finite `ProbComp` game equals `protocolCat`).
