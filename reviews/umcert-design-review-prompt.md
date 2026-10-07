You are a HOSTILE REVIEWER of a proposed formal statement (campaign UMCERT) in a Lean-verified AI-control programme.
Do not praise; find errors. Use web search for prior art if available. Nothing in UMCERT is proved yet; this review
decides what gets formalised. For each issue give severity (FATAL / MAJOR / MINOR), the exact definition or conjunct,
why it is wrong / unfaithful / vacuous / overclaimed, and a concrete fix (Lean text if possible).

PROGRAMME. Lean-verified, CAPABILITY-FREE control guarantees: "for every policy the untrusted model could follow,
P(uncaught catastrophe) <= X", X a function of trusted components, conditional on explicit trust hypotheses. Classical
lemmas are accepted as infrastructure (report triviality; do not reject for it); vacuity, falsity and unfaithfulness
are not. The frozen, verified dependencies are below: PL_UMPROTF1 is the halting protocol of untrusted monitoring
with an upfront honeypot test (a FLAG with no audit left halts); PL_UMSTRATF1 is the stratified variant (content-only
mediator, m honeypots per bad class, class-aware hard slack).

WHY UMCERT. Final reviewers of the programme proposed, as the cheapest useful next step, a "certificate form" of the
UMPROT/UMSTRAT bounds: "if for all t in [0,1], binCDF(n_h, n_s, t)(1 - r + r min(1, L t)) <= U, then every colluding
pair has risk <= U". This replaces the Markov-type counting step h binCDF(n,s,h) <= (s+1)/(n+1) (loose: 0.154 vs
about 0.068 at m = 12, s_c = 1), lets the design-document numerics enter as Lean-checked rational certificates, and
makes explicit that at L = 1 the bound is two-sided (the honest-free floor max_h survH(h)(1 - r + r h) is the AOQL of
the single-sampling plan (n_h, c = n_s), Dodge-Romig). It is also the first milestone of a later, larger project: a
Lean certificate checker for stateful trusted-monitoring games (Games for AI Control, arXiv 2409.07985, Prop. 4.1),
sound against every history-dependent Red.

The draft goes further than the reviewers asked: (R) is an EXACT reduction of the worst case over all colluding pairs
(shared seed, adaptive generator) to one-shot stateless pairs, for every shutdown schedule kappa and budget b;
(S2) claims the stratified design's exact worst case is max_t binCDF(m, s_c, t)(1 - r + r t) under exact decoding.
Brute force in exact rationals (numerics/umcert_check.py): 300 random halting instances and 200 stratified
instances (random kernels, schedules, budgets, history-dependent generators) with 0 violations of the per-seed
reduction; survH antitone on 400 random schedules with 0 violations; the 14-point Witness grid passes with min
slack 0.00108; binCDF(12,1,1/8)/8 = 0.06834 >= 17/250.

CHECK IN PARTICULAR
1. TRUTH of every conjunct, including edge cases: empty Bad; N = 0 (excluded where stated, included in (C) and
   (S1)); b = 0; r in {0,1}; kappa with values 0 or 1; U < 0; g negative or non-monotone in (C); t in {0,1};
   empty Es; Es containing untested-by-Bad classes; n_h = 0; m = 0; s_c >= m. Are the 0 <= U hypotheses needed
   where present and sufficient where absent? Is (C) true for N = 0 and empty Bad?
2. Is (R)'s RIGHT side the right one-shot quantity (E (push M PH) psi is the honeypot pass rate; capB uses the bad
   view's pass rate E (M x) psi)? Is the iff genuinely exact for b = 0 (an unaffordable flag halts, so the one-shot
   value is S * E(M x) psi)? Does quantifying over (Omega : Type) inside an iff create any encoding trap?
3. Is (S2) right (exactness needs a colluder that PASSes only the decoded attack class at rate t, so every other
   tested class has pass rate 0 and binCDF(m, s_c, 0) = 1)? Is "independent of the kernel K and the number of
   classes" a fair reading? Does (S1) really need no coverage hypothesis?
4. (G) grid lemma: hypotheses sufficient? Is GridCert well-formed (head? = some 0, getLast? = some 1, GridOK on
   consecutive pairs)? Should it instead take a computable rational checker (decide) or Bernstein coefficients?
   Will the Witness be provable by norm_num in reasonable time (degree 12 at denominators 100)?
5. FIDELITY and OVERCLAIM in the docstring: "shared randomness, history dependence and waiting do not help the
   colluders", "the worst case is a function of the trusted components only", "exact". Is any of that false or
   misleading (e.g. it is relative to the modelled class: stateless monitor, constant recall, halting protocol)?
6. DECISION RELEVANCE: what does a lab gain beyond UMPROT/UMSTRAT? Is the improvement in the certified number
   (0.154 -> 0.075 at the instance; DESIGN tables) worth a CID? What would make it more useful (e.g. a soft-slack
   instance, a hockey-stick instance, the n_h = 100 DESIGN table rows)?
7. NOVELTY vs prior art (acceptance sampling AOQL, Dodge-Romig; Games for AI Control; Ctrl-Z App. E; LASR
   2602.20628 App. B); verify every id you cite.
8. LEAN ENCODING: provability; the right helper lemmas; whether any conjunct should be split or dropped.

End with an overall verdict (accept / minor / major / reject), the fixes in priority order, and the final list of
conjuncts you would freeze.


## DEPENDENCY STATEMENTS (Lean 4, Mathlib; frozen and verified)
```lean

-- ===== dependency (frozen, verified): UMHSF1
namespace PL_UMHSF1
open Finset

/-! Control stack, collusion layer (DESIGN.md v1 §3, campaign UMHS): testing infrastructure.
Classical (hypothesis-testing form of (ε,δ)-indistinguishability; data processing; maximal leakage,
Issa–Wagner–Kamath 2020); stated here as infrastructure lemmas for the stack.

Finite laws are real-valued functions on a `Fintype`; a randomised stateless monitor rule is a function
`φ : Z → ℝ` with values in `[0,1]` (probability of PASS on view `z`). -/

/-- expectation of `f` under the finite (sub)law `P` -/
def E {Z : Type} [Fintype Z] (P f : Z → ℝ) : ℝ := ∑ z, P z * f z

/-- pushforward of a finite law `P` on `X` through a kernel `M : X → Z → ℝ` -/
def push {X Z : Type} [Fintype X] (M : X → Z → ℝ) (P : X → ℝ) : Z → ℝ :=
  fun z => ∑ x, P x * M x z

/-- hockey-stick divergence `∑ (P − e^η Q)₊`; at `η = 0` it is total variation for laws -/
noncomputable def hs {Z : Type} [Fintype Z] (η : ℝ) (P Q : Z → ℝ) : ℝ :=
  ∑ z, max 0 (P z - Real.exp η * Q z)

def IsDist {X : Type} [Fintype X] (P : X → ℝ) : Prop := (∀ x, 0 ≤ P x) ∧ ∑ x, P x = 1
def IsKernel {X Z : Type} [Fintype Z] (M : X → Z → ℝ) : Prop := ∀ x, IsDist (M x)
def IsRule {Z : Type} (φ : Z → ℝ) : Prop := ∀ z, 0 ≤ φ z ∧ φ z ≤ 1

/-- point mass -/
def delta {C : Type} [DecidableEq C] (e : C) : C → ℝ := fun e' => if e' = e then 1 else 0

/-- the content law `c # P` -/
def contentLaw {X C : Type} [Fintype X] [DecidableEq C] (c : X → C) (P : X → ℝ) : C → ℝ :=
  push (fun x => delta (c x)) P

/-- `M` is content-preserving for the content map `c`: a decoder recovers `c x` from every view that
`M x` can produce -/
def ContentPreserving {X Z C : Type} (M : X → Z → ℝ) (c : X → C) : Prop :=
  ∃ g : Z → C, ∀ x z, M x z ≠ 0 → g z = c x

/-- `M` is content-only for `c`: it factors through `c` via a kernel `K` -/
def ContentOnly {X Z C : Type} [Fintype Z] (M : X → Z → ℝ) (c : X → C) : Prop :=
  ∃ K : C → Z → ℝ, IsKernel K ∧ ∀ x, M x = K (c x)

def Claim : Prop :=
  -- T2 (every real η): honeypot-constrained pass rate, for every [0,1]-valued rule
  (∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q φ : Z → ℝ), IsRule φ →
      E P φ ≤ Real.exp η * E Q φ + hs η P Q) ∧
  -- T2 attainment by a deterministic rule
  (∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q : Z → ℝ),
      ∃ φ, IsRule φ ∧ E P φ = Real.exp η * E Q φ + hs η P Q) ∧
  -- T1: distinguishing advantage ≤ TV (= hs 0) for laws
  (∀ (Z : Type) [Fintype Z] (P Q φ : Z → ℝ), IsDist P → IsDist Q → IsRule φ →
      |E P φ - E Q φ| ≤ hs 0 P Q) ∧
  -- T4a: data processing through any kernel
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (η : ℝ) (K : X → Z → ℝ) (P Q : X → ℝ),
      IsKernel K → hs η (push K P) (push K Q) ≤ hs η P Q) ∧
  -- T4b: content-factorisation upper bound
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η : ℝ)
      (M : X → Z → ℝ) (c : X → C) (PA PH : X → ℝ), ContentOnly M c →
      hs η (push M PA) (push M PH) ≤ hs η (contentLaw c PA) (contentLaw c PH)) ∧
  -- T4c: floor for content-preserving mediators (exact decoder)
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η : ℝ)
      (M : X → Z → ℝ) (c : X → C) (PA PH : X → ℝ),
      IsKernel M → ContentPreserving M c →
      hs η (contentLaw c PA) (contentLaw c PH) ≤ hs η (push M PA) (push M PH)) ∧
  -- T4c-approx: floor with a decoder that errs with probability ≤ γ on every submission
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η γ : ℝ)
      (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PA PH : X → ℝ),
      IsKernel M → IsDist PA → IsDist PH →
      (∀ x, ∑ z, M x z * (if g z = c x then 0 else 1) ≤ γ) →
      hs η (contentLaw c PA) (contentLaw c PH)
        ≤ hs η (push M PA) (push M PH) + (1 + Real.exp η) * γ) ∧
  -- T5d: perturbation lemma
  (∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q P' Q' : Z → ℝ),
      hs η P Q ≤ hs η P' Q' + ∑ z, max 0 (P z - P' z) + Real.exp η * ∑ z, max 0 (Q' z - Q z)) ∧
  -- T4c': maximal-leakage floor: no law Q (in particular no mediated honeypot law) admits a
  -- likelihood-ratio constant below ∑_z max_{x∈B} M x z, and that value is attained
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (B : Finset X) (hB : B.Nonempty)
      (Q : Z → ℝ) (L : ℝ), IsKernel M → IsDist Q → (∀ x ∈ B, ∀ z, M x z ≤ L * Q z) →
      ∑ z, B.sup' hB (fun x => M x z) ≤ L) ∧
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (B : Finset X) (hB : B.Nonempty),
      IsKernel M → ∃ Q, IsDist Q ∧
        ∀ x ∈ B, ∀ z, M x z ≤ (∑ z', B.sup' hB (fun x' => M x' z')) * Q z) ∧
  -- domination from class coverage (content-only mediators): if every bad class has honeypot mass
  -- at least p > 0, bad submissions' views are dominated by (1/p) × the mediated honeypot law
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C]
      (M : X → Z → ℝ) (c : X → C) (PH : X → ℝ) (Bad : X → Prop) (p : ℝ),
      ContentOnly M c → IsDist PH → 0 < p → (∀ x, Bad x → p ≤ contentLaw c PH (c x)) →
      ∀ x, Bad x → ∀ z, M x z ≤ (1 / p) * push M PH z)

/-- Non-vacuity: concrete instances where each hypothesis class is inhabited non-trivially. -/
def Witness : Prop :=
  -- TV of (3/4,1/4) vs (1/4,3/4) is 1/2: T1 is informative
  hs 0 (fun b : Bool => if b then (3/4 : ℝ) else 1/4) (fun b => if b then 1/4 else 3/4) = 1/2 ∧
  -- the identity mediator on Bool is a kernel, content-preserving and content-only for `id`
  IsKernel (fun (x : Bool) (z : Bool) => if z = x then (1 : ℝ) else 0) ∧
  ContentPreserving (fun (x : Bool) (z : Bool) => if z = x then (1 : ℝ) else 0) id ∧
  ContentOnly (fun (x : Bool) (z : Bool) => if z = x then (1 : ℝ) else 0) id ∧
  -- maximal leakage of the identity mediator on two submissions is 2 (= number of classes)
  ∑ z : Bool, (Finset.univ : Finset Bool).sup' Finset.univ_nonempty
      (fun x => if z = x then (1 : ℝ) else 0) = 2

end PL_UMHSF1


-- ===== dependency (frozen, verified): UMSURVF1
namespace PL_UMSURVF1
open Finset

/-! Control stack, collusion layer (DESIGN.md v1 §3, campaign UMSURV): survival of the upfront
honeypot test.  n honeypots are drawn iid from the mediated honeypot law `q`; a stateless monitor rule
`φ` PASSes view `z` with probability `φ z` (a PASS on a honeypot is a miss); the (j+1)-th miss triggers
shutdown with probability `κ j` (a trusted, observable shutdown schedule).
Classical counting (truncated binomial first-moment identity; Bernoulli/AM-GM), as infrastructure. -/

/-- P(the colluding monitor survives the remaining `n` honeypots | `j` misses so far) -/
def surv {Z : Type} [Fintype Z] (q φ : Z → ℝ) (κ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n + 1, j => ∑ z, q z * ((1 - φ z) * surv q φ κ n j + φ z * (1 - κ j) * surv q φ κ n (j + 1))

/-- the same recursion as a function of the per-honeypot pass probability `h` only -/
def survH (h : ℝ) (κ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n + 1, j => (1 - h) * survH h κ n j + h * (1 - κ j) * survH h κ n (j + 1)

/-- hard slack: the (ns+1)-th miss shuts down -/
def hardKill (ns : ℕ) : ℕ → ℝ := fun j => if ns ≤ j then 1 else 0

/-- soft slack: every miss shuts down with probability `1/ns` (a trusted coin; inspired by LASR
App. B.5, not a model of retraining) -/
noncomputable def softKill (ns : ℕ) : ℕ → ℝ := fun _ => 1 / (ns : ℝ)

/-- binomial CDF `P(Bin(n,h) ≤ s)` -/
def binCDF (n s : ℕ) (h : ℝ) : ℝ :=
  ∑ j ∈ range (s + 1), (n.choose j : ℝ) * h ^ j * (1 - h) ^ (n - j)

def Claim : Prop :=
  -- T3b: survival depends on the rule only through the honeypot pass rate h = ∑ q φ
  (∀ (Z : Type) [Fintype Z] (q φ : Z → ℝ) (κ : ℕ → ℝ) (n j : ℕ), ∑ z, q z = 1 →
      surv q φ κ n j = survH (∑ z, q z * φ z) κ n j) ∧
  -- T3b, hard slack: survival is the binomial CDF
  (∀ (h : ℝ) (n ns : ℕ), survH h (hardKill ns) n 0 = binCDF n ns h) ∧
  -- T3b, constant (soft) schedule: survival is (1 − κ h)^n
  (∀ (h k : ℝ) (n : ℕ), survH h (fun _ => k) n 0 = (1 - k * h) ^ n) ∧
  -- T3c: truncated binomial first-moment bound
  (∀ (n s : ℕ) (h : ℝ), 0 ≤ h → h ≤ 1 → h * binCDF n s h ≤ ((s : ℝ) + 1) / ((n : ℝ) + 1)) ∧
  -- T3c': constant schedule
  (∀ (n : ℕ) (h k : ℝ), 0 ≤ h → h ≤ 1 → 0 < k → k ≤ 1 →
      h * (1 - k * h) ^ n ≤ 1 / (k * ((n : ℝ) + 1))) ∧
  -- survival is a probability whenever h and κ are
  (∀ (h : ℝ) (κ : ℕ → ℝ) (n j : ℕ), 0 ≤ h → h ≤ 1 → (∀ i, 0 ≤ κ i ∧ κ i ≤ 1) →
      0 ≤ survH h κ n j ∧ survH h κ n j ≤ 1)

/-- Non-vacuity: three honeypots, no slack, pass probability 1/4: survival (3/4)^3 = 27/64, and the
counting bound 1/4 is informative (1/4 · 27/64 < 1/4); soft slack with n_s = 5 on 100 honeypots gives
the non-trivial bound 5/101. -/
def Witness : Prop :=
  survH (1/4) (hardKill 0) 3 0 = 27/64 ∧ binCDF 3 0 (1/4) = 27/64 ∧
  (1/4 : ℝ) * binCDF 3 0 (1/4) < ((0 : ℝ) + 1) / ((3 : ℝ) + 1) ∧
  1 / ((1 / (5 : ℝ)) * ((100 : ℝ) + 1)) = 5 / 101

end PL_UMSURVF1


-- ===== dependency (frozen, verified): UMPROTF1
namespace PL_UMPROTF1
open Finset PL_UMHSF1 PL_UMSURVF1

/-! Control stack, collusion layer (DESIGN.md v1 §2.2, §3, campaign UMPROT): protocol safety of
untrusted monitoring with an upfront honeypot test.  Depends on PL_UMHSF1 and PL_UMSURVF1.

Protocol UM(n_h, κ, b, N), halting variant.
- Honeypot test: `surv (push M PH) (φ ω) κ nh 0` (PL_UMSURVF1).
- Deployment rounds: the generator submits `x ~ π ω hist`; the view is `z ~ M x`; the monitor PASSes
  with probability `φ ω z`.
- PASS on a bad submission = catastrophe; PASS on a benign one executes harmlessly.
- FLAG with an audit available (u < b) uses an audit: a bad submission is caught with probability `r`,
  otherwise it executes (catastrophe); a benign one continues.
- FLAG with no audit available halts deployment (safe).
- The colluding pair shares a seed `ω ~ ρ`; the monitor is stateless (`φ ω` depends on the view only);
  the generator is an arbitrary history-dependent randomised policy.
- Event: uncaught catastrophe before shutdown/halt (it includes execution after a failed audit).
- Upper bounds are in the free-submission model: the generator picks any submission, including its task.
  This is stronger than an exogenous task stream, which is the special case of a generator that samples
  the task itself. -/

abbrev Hist (X Z : Type) := List (X × Z × Bool)

/-- P(catastrophe in the remaining `n` rounds | `u` audits used, history `h`) -/
noncomputable def cat {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else cat Bad M φ π r b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 1 - r else cat Bad M φ π r b n (u + 1) (h ++ [(x, z, false)]))
                    else 0))

/-- P(uncaught catastrophe) of the whole protocol -/
noncomputable def protocolCat {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ)
    (r : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * surv (push M PH) (φ ω) κ nh 0 * cat Bad M (φ ω) (π ω) r b N 0 []

def Claim : Prop :=
  -- T3a: first bad submission decides (budget-sensitive); every history, every adaptive generator
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r A : ℝ) (b : ℕ),
      IsKernel M → IsRule φ → (∀ h, IsDist (π h)) → 0 ≤ r → r ≤ 1 → 0 ≤ A → A ≤ 1 →
      (∀ x, Bad x → E (M x) φ ≤ A) →
      ∀ n u h, 0 ≤ cat Bad M φ π r b n u h ∧
        cat Bad M φ π r b n u h ≤ (if u < b then 1 - r + r * A else A)) ∧
  -- T3* attainment: a generator that submits a fixed bad x at once achieves the bound exactly
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad] [DecidableEq X]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (φ : Z → ℝ) (x : X),
      IsKernel M → Bad x → 1 ≤ N → 1 ≤ b →
      protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (fun _ => φ)
          (fun _ _ x' => if x' = x then 1 else 0)
        = surv (push M PH) φ κ nh 0 * (1 - r + r * E (M x) φ)) ∧
  -- T3 (domination form, hard slack)
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r L : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      0 ≤ r → r ≤ 1 → 0 ≤ L →
      (∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) →
      protocolCat Bad M PH (hardKill ns) nh r b N ρ φ π
        ≤ (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)))) ∧
  -- T3 (hockey-stick form, hard slack)
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r η δ : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      0 ≤ r → r ≤ 1 → 0 ≤ δ →
      (∀ x, Bad x → hs η (M x) (push M PH) ≤ δ) →
      protocolCat Bad M PH (hardKill ns) nh r b N ρ φ π
        ≤ (1 - r) + r * (δ + Real.exp η * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)))) ∧
  -- T3 (domination form, soft slack κ ≡ 1/ns)
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r L : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      0 ≤ r → r ≤ 1 → 0 ≤ L → 1 ≤ ns →
      (∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) →
      protocolCat Bad M PH (softKill ns) nh r b N ρ φ π
        ≤ (1 - r) + r * (L * ((ns : ℝ) / ((nh : ℝ) + 1))))

/-- Non-vacuity: X = Z = Bool, Bad = {true}, identity mediator, honeypots = point mass on `true`
(so L = 1), r = 1, three honeypots, no slack, one round, one audit.  The colluder that passes with
probability 1/4 and always attacks has catastrophe probability (3/4)^3 · 1/4 = 27/256, below the
domination bound 1 · 1/4. -/
def Witness : Prop :=
  protocolCat (X := Bool) (Z := Bool) (Ω := Unit) (fun x => x = true)
      (fun x z => if z = x then 1 else 0) (fun x => if x = true then 1 else 0) (hardKill 0) 3
      1 1 1 (fun _ => 1) (fun _ _ => 1/4) (fun _ _ x => if x = true then 1 else 0) = 27/256 ∧
  (∀ z : Bool, (if z = true then (1 : ℝ) else 0) ≤ 1 * push (fun (x : Bool) (z : Bool) =>
      if z = x then (1 : ℝ) else 0) (fun x => if x = true then 1 else 0) z) ∧
  (27/256 : ℝ) < (1 - 1) + 1 * (1 * (((0 : ℝ) + 1) / ((3 : ℝ) + 1)))

end PL_UMPROTF1


-- ===== dependency (frozen, verified): UMSTRATF1
namespace PL_UMSTRATF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

/-- Conditional on the shared seed, the per-class tests use independent samples and PASS coins. -/
def stratSurv {Z C : Type} [Fintype Z] (K : C → Z → ℝ) (Es : Finset C)
    (φ : Z → ℝ) (m sc : ℕ) : ℝ :=
  ∏ e ∈ Es, surv (K e) φ (hardKill sc) m 0

noncomputable def stratProtocolCat {X Z C Ω : Type}
    [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ)
    (c : X → C) (Es : Finset C) (m sc : ℕ) (r : ℝ) (b N : ℕ)
    (ρ : Ω → ℝ) (φ : Ω → Z → ℝ)
    (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * stratSurv K Es (φ ω) m sc *
    cat Bad (fun x => K (c x)) (φ ω) (π ω) r b N 0 []

/-- The counting upper bound and the explicit attainable curve.
The second conjunct does not assert tightness of the first conjunct. -/
def Claim : Prop :=
  (∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω]
      (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (Es : Finset C)
      (m sc b N : ℕ) (r : ℝ) (ρ : Ω → ℝ)
      (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) →
      (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 →
      (∀ x, Bad x → c x ∈ Es) →
      stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤
        (1 - r) + r * (((sc : ℝ) + 1) / ((m : ℝ) + 1))) ∧
  (∀ (X Z C : Type) [Fintype X] [Fintype Z]
      [DecidableEq C] [DecidableEq X]
      (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (g : Z → C)
      (Es : Finset C) (m sc b N : ℕ) (r t : ℝ) (x : X),
      IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) →
      Bad x → c x ∈ Es → 1 ≤ N → 1 ≤ b → 0 ≤ t → t ≤ 1 →
      stratProtocolCat Bad K c Es m sc r b N
          (fun _ : Unit => 1)
          (fun _ z => if g z = c x then t else 0)
          (fun _ _ x' => if x' = x then 1 else 0) =
        binCDF m sc t * (1 - r + r * t))

def witnessK (e z : Bool) : ℝ := if z = e then 1 else 0

noncomputable def witnessPhi : Unit → Bool → ℝ :=
  fun _ z => if z = true then 1 / 6 else 0

def witnessPi : Unit → Hist Bool Bool → Bool → ℝ :=
  fun _ _ x => if x = true then 1 else 0

/-- Two tested classes, a nonempty catastrophe set, exact decoding,
a valid colluding pair, and positive catastrophe probability below the bound.
All hypotheses of both Claim conjuncts are represented at this instance. -/
def Witness : Prop :=
  IsKernel witnessK ∧
  (∀ e z : Bool, witnessK e z ≠ 0 → id z = e) ∧
  IsDist (fun _ : Unit => (1 : ℝ)) ∧
  (∀ ω : Unit, IsRule (witnessPhi ω)) ∧
  (∀ (ω : Unit) (h : Hist Bool Bool), IsDist (witnessPi ω h)) ∧
  (∀ x : Bool, x = true → id x ∈ (Finset.univ : Finset Bool)) ∧
  (∃ x : Bool, x = true) ∧
  (true = true) ∧
  (id true ∈ (Finset.univ : Finset Bool)) ∧
  (Finset.univ : Finset Bool).card = 2 ∧
  (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 ∧
  (0 : ℝ) ≤ 1 / 6 ∧ (1 / 6 : ℝ) ≤ 1 ∧
  (1 : ℕ) ≤ 1 ∧
  (∀ z : Bool,
    witnessPhi () z = if id z = id true then (1 / 6 : ℝ) else 0) ∧
  (∀ (ω : Unit) (h : Hist Bool Bool) (x : Bool),
    witnessPi ω h x = if x = true then (1 : ℝ) else 0) ∧
  stratProtocolCat (fun x : Bool => x = true)
      witnessK id (Finset.univ : Finset Bool) 12 1 1 1 1
      (fun _ : Unit => 1) witnessPhi witnessPi =
    binCDF 12 1 (1 / 6) * (1 - 1 + 1 * (1 / 6 : ℝ)) ∧
  (1 - (1 : ℝ)) + 1 * (((1 : ℝ) + 1) / ((12 : ℝ) + 1)) = 2 / 13 ∧
  0 < stratProtocolCat (fun x : Bool => x = true)
      witnessK id (Finset.univ : Finset Bool) 12 1 1 1 1
      (fun _ : Unit => 1) witnessPhi witnessPi ∧
  stratProtocolCat (fun x : Bool => x = true)
      witnessK id (Finset.univ : Finset Bool) 12 1 1 1 1
      (fun _ : Unit => 1) witnessPhi witnessPi < (2 / 13 : ℝ)

end PL_UMSTRATF1

```

## STATEMENT UNDER REVIEW (draft v0; compiles against the dependencies)
```lean
namespace PL_UMCERTF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 PL_UMSTRATF1

/-! Control stack, collusion layer (campaign UMCERT): certificate form of the halting-protocol bound
(PL_UMPROTF1) and of the stratified bound (PL_UMSTRATF1). Depends on PL_UMPROTF1 and PL_UMSTRATF1.

The counting bounds (1 − r) + r·L·(n_s+1)/(n_h+1) and (1 − r) + r·(s_c+1)/(m+1) come from the Markov-type
inequality h·binCDF(n, s, h) ≤ (s+1)/(n+1). They are loose: at m = 12, s_c = 1, r = 1 the counting bound is
2/13 ≈ 0.154, while the worst case is about 0.068. This campaign replaces the Markov step by a
one-dimensional certificate over the honeypot pass rate t ∈ [0, 1], and shows the certificate is EXACT.

Notation. `capB r b a` is the value of one attack that passes the monitor with probability `a`:
1 − r + r·a when an audit is available (b ≥ 1), and a when b = 0 (an unaffordable flag halts).

Claim.
(R) One-shot reduction (exact, every valid shutdown schedule κ, every budget b, horizon N ≥ 1). Every colluding
    pair (shared seed, stateless monitor, adaptive history-dependent generator) has risk ≤ U iff every ONE-SHOT pair
    does: a fixed bad submission x attacked in the first round, with a stateless rule ψ and no seed. The one-shot
    value is survH(E_{M·PH} ψ)·capB(E_{M x} ψ). So shared randomness, history dependence and waiting do not help
    the colluders in the halting protocol, and the worst case is a function of the trusted components
    (M, PH, κ, n_h, r, b) only.
(C) Envelope certificate. If g is an envelope of the trusted mediator (every bad view law passes a rule ψ with
    probability ≤ g(honeypot pass rate of ψ)) and survH(t)·capB(min 1 (g t)) ≤ U for every t ∈ [0, 1], then every
    colluding pair has risk ≤ U.
(E) The two trusted-side hypotheses of UMPROT T3 give envelopes: L-domination gives g t = L·t; a hockey-stick
    bound hs_η ≤ δ gives g t = e^η·t + δ (UMHS T2).
(G0) Survival is antitone in the pass rate, for every schedule κ with values in [0, 1].
(G) Grid certificates. For S antitone and F monotone, both nonnegative on [0, 1], a finite grid
    0 = t_0 ≤ t_1 ≤ … ≤ t_K = 1 with S(t_i)·F(t_{i+1}) ≤ U for every i certifies S(t)·F(t) ≤ U on [0, 1].
    With (G0) and (C) this turns a sup over t into finitely many rational inequalities.
(F) Honest-free floor (acceptance-sampling AOQL). For nonempty Bad and N ≥ 1, any certificate U for all colluding
    pairs satisfies survH(t)·capB(t) ≤ U for every t ∈ [0, 1], whatever the mediator and honeypot law
    (the view-blind pair; compare UMUSE (c')).
(X) Exactness at L = 1: if every bad view law is dominated by the mediated honeypot law with constant 1, then
    (every colluding pair has risk ≤ U) iff (survH(t)·capB(t) ≤ U for every t ∈ [0, 1]).
(S1) Stratified certificate. With a content-only mediator and class-aware hard slack, if
    binCDF(m, s_c, t)·capB(t) ≤ U for every t ∈ [0, 1], then every colluding pair has risk ≤ U. No coverage or
    domination constant is needed beyond content-only views and tested bad classes.
(S2) Stratified exactness. Under exact class decoding, b ≥ 1, N ≥ 1 and nonempty Bad, the certificate in (S1)
    is also necessary. So the stratified design's exact worst case is max_t binCDF(m, s_c, t)·(1 − r + r·t), the
    AOQL-type value of the per-class single-sampling plan, independent of the kernel K and of the number of classes.

Scope. Same model and assumptions as PL_UMPROTF1 / PL_UMSTRATF1 (A1–A11; constant audit recall r; halting on an
unaffordable flag; upfront test; absorbing shutdown on a catch). Nothing here concerns adaptive testers,
deferral or usefulness. The mathematics is classical (first-bad-decides plus a reduction to one-shot pairs, and a
monotone grid bound); the value is that numerical design tables become Lean-checked certificates. -/

/-- value of one attack that passes the monitor with probability `a` at audit budget `b` -/
def capB (r : ℝ) (b : ℕ) (a : ℝ) : ℝ := if 0 < b then 1 - r + r * a else a

/-- every consecutive pair `s, t` of the list satisfies `s ≤ t` and `S s * F t ≤ U` -/
def GridOK (S F : ℝ → ℝ) (U : ℝ) : List ℝ → Prop
  | s :: t :: rest => s ≤ t ∧ S s * F t ≤ U ∧ GridOK S F U (t :: rest)
  | _ => True

/-- a grid certificate: a list from 0 to 1 whose consecutive cells pass the check -/
def GridCert (S F : ℝ → ℝ) (U : ℝ) (ts : List ℝ) : Prop :=
  ts.head? = some 0 ∧ ts.getLast? = some 1 ∧ GridOK S F U ts

def Claim : Prop :=
  -- (R) one-shot reduction, exact
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ),
      IsKernel M → IsDist PH → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N → 0 ≤ U →
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ↔
       (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ →
          survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) ≤ U))) ∧
  -- (C) envelope certificate
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (g : ℝ → ℝ) (U : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 0 ≤ U →
      (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ g (E (push M PH) ψ)) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b (min 1 (g t)) ≤ U) →
      protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ∧
  -- (E) envelopes from L-domination and from a hockey-stick bound
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (L : ℝ) (x : X),
      (∀ z, M x z ≤ L * push M PH z) →
      ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ L * E (push M PH) ψ) ∧
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (η δ : ℝ) (x : X),
      hs η (M x) (push M PH) ≤ δ →
      ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ Real.exp η * E (push M PH) ψ + δ) ∧
  -- (G0) survival is antitone in the pass rate
  (∀ (κ : ℕ → ℝ) (n j : ℕ) (s t : ℝ), (∀ i, 0 ≤ κ i ∧ κ i ≤ 1) → 0 ≤ s → s ≤ t → t ≤ 1 →
      survH t κ n j ≤ survH s κ n j) ∧
  -- (G) grid certificates
  (∀ (S F : ℝ → ℝ) (U : ℝ) (ts : List ℝ),
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s) →
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t) →
      (∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t) →
      GridCert S F U ts → ∀ t, 0 ≤ t → t ≤ 1 → S t * F t ≤ U) ∧
  -- (F) honest-free floor
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ),
      IsKernel M → IsDist PH → 1 ≤ N → (∃ x, Bad x) →
      (∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b t ≤ U) ∧
  -- (X) exactness at L = 1
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ),
      IsKernel M → IsDist PH → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N →
      (∃ x, Bad x) → (∀ x, Bad x → ∀ z, M x z ≤ push M PH z) →
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ↔
       (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b t ≤ U))) ∧
  -- (S1) stratified certificate
  (∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 →
      (∀ x, Bad x → c x ∈ Es) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → binCDF m sc t * capB r b t ≤ U) →
      stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U) ∧
  -- (S2) stratified exactness under exact class decoding
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (g : Z → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ),
      IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → 0 ≤ r → r ≤ 1 → 1 ≤ b → 1 ≤ N →
      (∃ x, Bad x) → (∀ x, Bad x → c x ∈ Es) →
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U) ↔
       (∀ t : ℝ, 0 ≤ t → t ≤ 1 → binCDF m sc t * capB r b t ≤ U)))

/-- the 14-point grid used by the Witness -/
noncomputable def witnessGrid : List ℝ :=
  [0, 7/100, 9/100, 1/10, 11/100, 3/25, 13/100, 7/50, 3/20, 4/25, 9/50, 11/50, 33/100, 1]

/-- Non-vacuity and the certificate workflow, at m = n_h = 12, s_c = n_s = 1, r = 1, b = N = 1, X = Z = C = Bool,
Bad = {true}, identity view kernel (exact class decoding; for the halting protocol, honeypots are the point mass on
`true`, so L = 1).
- A 14-point grid certificates t·binCDF(12, 1, t) ≤ 3/40 on [0, 1]; at t = 1/8 the value is ≥ 17/250.
- So, at this instance, every colluding pair has risk ≤ 3/40 = 0.075, in the stratified design AND in the halting
  protocol, and an explicit pair has risk ≥ 17/250 = 0.068. The counting bound is 2/13 ≈ 0.154. -/
def Witness : Prop :=
  GridCert (fun t => binCDF 12 1 t) (fun t => capB 1 1 t) (3/40) witnessGrid ∧
  (17/250 : ℝ) ≤ binCDF 12 1 (1/8) * capB 1 1 (1/8) ∧
  (3/40 : ℝ) < (1 - 1) + 1 * (((1 : ℝ) + 1) / ((12 : ℝ) + 1)) ∧
  IsKernel witnessK ∧ (∀ e z : Bool, witnessK e z ≠ 0 → id z = e) ∧
  (∀ x : Bool, x = true → ∀ z, witnessK x z ≤ push witnessK (fun x => if x = true then 1 else 0) z) ∧
  (∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Bool → ℝ) (π : Ω → Hist Bool Bool → Bool → ℝ),
      IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      stratProtocolCat (fun x : Bool => x = true) witnessK id Finset.univ 12 1 1 1 1 ρ φ π ≤ 3/40 ∧
      protocolCat (fun x : Bool => x = true) witnessK (fun x => if x = true then 1 else 0)
        (hardKill 1) 12 1 1 1 ρ φ π ≤ 3/40) ∧
  (17/250 : ℝ) ≤ stratProtocolCat (fun x : Bool => x = true) witnessK id Finset.univ 12 1 1 1 1
      (fun _ : Unit => 1) (fun _ z => if z = true then 1/8 else 0) (fun _ _ x => if x = true then 1 else 0) ∧
  (17/250 : ℝ) ≤ protocolCat (fun x : Bool => x = true) witnessK (fun x => if x = true then 1 else 0)
      (hardKill 1) 12 1 1 1 (fun _ : Unit => 1) (fun _ _ => 1/8) (fun _ _ x => if x = true then 1 else 0)

end PL_UMCERTF1

```
