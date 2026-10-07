You are a HOSTILE REVIEWER of a proposed formal statement (campaign UMUSE) in a Lean-verified AI-control programme.
Do not praise; find errors. Use web search for prior art where useful. Nothing in UMUSE is proved yet: this review
decides what gets formalised. For each issue give severity (FATAL / MAJOR / MINOR), the exact definition or conjunct,
why it is wrong / unfaithful / vacuous / overclaimed, and a concrete fix (Lean text if possible).

PROGRAMME. Lean-verified, CAPABILITY-FREE control guarantees: theorems "for every policy the untrusted model could
follow, P(uncaught catastrophe) <= X", X a function of trusted components only, conditional on explicit trust
hypotheses. The owner accepts classical lemmas as infrastructure (report triviality, do not reject for it) but not
vacuity, falsity or unfaithfulness. Verified so far (dependencies below are FROZEN and PROVED): UMHSF1, UMSURVF1,
UMPROTF1 (main protocol bound), UMSTRATF1 (stratified honeypots, class-aware slack: risk <= (1-r) + r(s_c+1)/(m+1)),
UMNOGOF1, UMLOWERF1 (design-free converse: risk >= t(1 - t n/(k(n_s+1))) for decodable mediators with k classes).
The final hostile review of the package said: in the halting variant a monitor that FLAGs everything satisfies every
upper bound, so the bounds measure only the adversarial gain over always-flag; usefulness is not in Lean. UMUSE is
meant to fix that: (i) Lean lemmas for the honest side (false shutdown = 1 - S_kappa(alpha0); false halt =
P(Bin(N, f0) > b)), and (ii) a safety/usefulness Pareto statement for given (n_h, n_s, b).

CHECK IN PARTICULAR
1. FIDELITY of `haltP` to the protocol semantics encoded by PL_UMPROTF1.cat (same branches, same budget rule, halt
   event correctly scored; is r correctly irrelevant?), of `honestUse` as a PRODUCT, and of modelling the honest task
   stream as a history-independent benign law mu. Is "honest monitor = any rule phi0" the right abstraction, and are
   alpha0 = E_{push M PH} phi0 and f0 = E_mu E_M (1 - phi0) the right rates?
2. TRUTH of every conjunct (a)-(e) and of the Witness: edge cases N = 0, b = 0, b >= N, n_h = 0, n_s >= n_h, alpha0
   in {0,1}, r in {0,1}, kappa arbitrary (not in [0,1]?), PH not supported on Bad, mu with Bad mass, s > n alpha in
   (d). Try to construct counterexamples.
3. Is the MIMICRY FLOOR (c)/(e) meaningful or degenerate? It pairs the honest monitor with a generator that submits
   fresh draws from the honeypot law (needs PH supported on Bad; in the design P_H lives on a Blue-enumerable superset
   B-bar of Bad). Does "no choice of (n_h, n_s) certifies risk below (honest test survival) x alpha0" follow, and is
   it the right Pareto statement? Is there a strictly better formal frontier at similar cost, e.g. (i) the
   global-slack corollary risk >= ~k alpha0/4 for decodable mediators (UMLOWERF1 + (d)), (ii) the class-aware upper
   bound -> alpha0 (UMSTRATF1 + a Chernoff/Chebyshev upper tail), (iii) anything using usefulness to bound the
   adversarial gain over always-flag? Recommend which conjuncts to add or drop. Is (e) merely a restatement?
4. OVERCLAIMS in the docstring (capability-free? product form? "no choice certifies risk below ...").
5. NOVELTY / prior art (binomial tail identities, Chebyshev/Cantelli, honest-baseline floors in control papers:
   Greenblatt et al. 2312.06942, LASR / Gardner-Challis et al. 2602.20628, Ctrl-Z 2504.10374; verify every arXiv id).
6. NUMBERS: recompute the Witness values and the frontier table below.
7. LEAN ENCODING: will (a)-(d) be provable with reasonable effort from the dependencies? Any statement change that
   makes proofs much easier without losing content?

End with an overall verdict (accept / minor / major / reject), the most important fixes, and the final list of
conjuncts you would freeze.


## DEPENDENCY STATEMENTS (Lean 4, Mathlib)
```lean

-- ===== dependency (frozen, verified): UMHS.lean
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

-- ===== dependency (frozen, verified): UMSURV.lean
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

-- ===== dependency (frozen, verified): UMPROT.lean
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

```

## UMUSE DRAFT STATEMENT (compiles after the dependencies)
```lean
namespace PL_UMUSEF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

/-! Control stack, collusion layer (campaign UMUSE): the usefulness companion and a safety/usefulness
frontier for protocol UM(n_h, κ, b, N), halting variant. Depends on PL_UMPROTF1 (and PL_UMHSF1,
PL_UMSURVF1).

Why. In the halting variant a monitor that FLAGs everything survives every honeypot test, so every
safety upper bound of PL_UMPROTF1 is satisfied by a useless protocol. This campaign pins the honest side
of the same protocol and shows the two sides together.

Honest side.
- An honest monitor is any rule `φ₀`. Its honeypot miss rate is `α₀ = ∑ z, push M PH z * φ₀ z`: the
  probability that it PASSes a mediated honeypot.
- The honest task stream is iid from a benign law `μ`. It is modelled as the history-independent
  generator `fun _ => μ`, with `μ` supported off `Bad`. Its benign false-flag rate is
  `f₀ = ∑ x, μ x * ∑ z, M x z * (1 - φ₀ z)`.
- `haltP` is the probability of the event "deployment halts on an unaffordable flag". It uses the
  same protocol as `PL_UMPROTF1.cat`, but scores halts instead of catastrophes:
  - PASS on a bad submission is a catastrophe (it ends the protocol, but is not a halt);
  - PASS on a benign submission continues;
  - FLAG with an audit available (u < b): on a bad submission, the attack is caught (absorbing
    shutdown) or it executes. Neither is a halt, so the recall r plays no role. On a benign submission,
    deployment continues with u + 1;
  - FLAG with no audit available halts (score 1).
- `honestUse` is the probability that the honest monitor survives the test AND the honest stream runs
  all N rounds without a halt. It is a product because the honest monitor has no seed and the
  test and deployment calls are fresh (A1).

Claim.
(a) False halt: `haltP = 1 − binCDF N b f₀`, i.e. P(Bin(N, f₀) > b).
(b) Usefulness: `honestUse = survH α₀ κ n_h 0 · binCDF N b f₀`. For hard slack this is
    `binCDF n_h n_s α₀ · binCDF N b f₀`. So false shutdown is 1 − S_κ(α₀), and false halt is as in (a).
(c) Mimicry floor (exact value). The honest monitor `φ₀` paired with a generator that submits fresh
    draws from the honeypot law (so P_H must be supported on Bad) has risk
    `survH α₀ κ n_h 0 · (α₀ + [0 < b](1 − r)(1 − α₀))`. That is at least `survH α₀ κ n_h 0 · α₀`:
    the honest survival times the honest miss rate. This needs no collusion, no seed and no capability.
(d) Slack cost (Chebyshev): if `s ≤ nα` then `(nα − s)² · binCDF n s α ≤ nα(1 − α)`. So a hard slack
    that keeps the honest false shutdown at most ε < 1 has `n_s ≥ n_h α₀ − √(n_h α₀ (1 − α₀)/(1 − ε))`.
(e) Frontier at hard slack (the Pareto statement). For the same parameters (n_h, n_s, b, N), with
    P_H on Bad and an L-dominated mediator:
    - the honest usefulness is `binCDF n_h n_s α₀ · binCDF N b f₀`;
    - every colluding pair has risk ≤ (1 − r) + r·L·(n_s + 1)/(n_h + 1) (PL_UMPROTF1);
    - some pair has risk ≥ `binCDF n_h n_s α₀ · α₀`.
    So no choice of (n_h, n_s) certifies risk below (honest test survival) × α₀.

Not claimed. History-dependent honest streams; usefulness of the stratified/class-aware design (it is
the same identity with a product of per-class CDFs, not stated here); any statement about U's actual
miss rate on attacks. The global-slack corollary (with PL_UMLOWERF1 and (d): risk ≥ about k·α₀/4 for
decodable mediators) is arithmetic left to the write-up. -/

/-- P(deployment halts on an unaffordable flag in the remaining `n` rounds | `u` audits used,
history `h`); same protocol as `PL_UMPROTF1.cat` -/
noncomputable def haltP {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (b : ℕ) : ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 0 else haltP Bad M φ π b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 0 else haltP Bad M φ π b n (u + 1) (h ++ [(x, z, false)]))
                    else 1))

/-- P(the honest monitor `φ₀` survives the honeypot test and the honest stream `π₀` then runs all `N`
rounds without a halt) -/
noncomputable def honestUse {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop)
    [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh b N : ℕ) (φ₀ : Z → ℝ)
    (π₀ : Hist X Z → X → ℝ) : ℝ :=
  surv (push M PH) φ₀ κ nh 0 * (1 - haltP Bad M φ₀ π₀ b N 0 [])

/-- honest miss rate on mediated honeypots -/
def missRate {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (φ₀ : Z → ℝ) : ℝ :=
  ∑ z, push M PH z * φ₀ z

/-- honest false-flag rate on the benign task stream `μ` -/
def flagRate {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (μ : X → ℝ) (φ₀ : Z → ℝ) : ℝ :=
  ∑ x, μ x * ∑ z, M x z * (1 - φ₀ z)

def Claim : Prop :=
  -- (a) false halt of an iid benign stream
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (φ₀ : Z → ℝ) (μ : X → ℝ) (b N : ℕ),
      IsKernel M → IsDist μ → (∀ x, μ x ≠ 0 → ¬ Bad x) →
      haltP Bad M φ₀ (fun _ => μ) b N 0 [] = 1 - binCDF N b (flagRate M μ φ₀)) ∧
  -- (b) honest usefulness, any shutdown schedule; and hard slack
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh ns b N : ℕ) (φ₀ : Z → ℝ) (μ : X → ℝ),
      IsKernel M → IsDist PH → IsDist μ → (∀ x, μ x ≠ 0 → ¬ Bad x) →
      honestUse Bad M PH κ nh b N φ₀ (fun _ => μ) =
          survH (missRate M PH φ₀) κ nh 0 * binCDF N b (flagRate M μ φ₀) ∧
      honestUse Bad M PH (hardKill ns) nh b N φ₀ (fun _ => μ) =
          binCDF nh ns (missRate M PH φ₀) * binCDF N b (flagRate M μ φ₀)) ∧
  -- (c) mimicry floor: honest monitor, generator submitting fresh honeypot draws
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (φ₀ : Z → ℝ),
      IsKernel M → IsDist PH → (∀ x, PH x ≠ 0 → Bad x) → IsRule φ₀ → 0 ≤ r → r ≤ 1 → 1 ≤ N →
      protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (fun _ => φ₀) (fun _ _ => PH) =
          survH (missRate M PH φ₀) κ nh 0 *
            (missRate M PH φ₀ + (if 0 < b then (1 - r) * (1 - missRate M PH φ₀) else 0)) ∧
      survH (missRate M PH φ₀) κ nh 0 * missRate M PH φ₀ ≤
        protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (fun _ => φ₀) (fun _ _ => PH)) ∧
  -- (d) slack cost: one-sided Chebyshev for the binomial lower tail
  (∀ (n s : ℕ) (α : ℝ), 0 ≤ α → α ≤ 1 → (s : ℝ) ≤ n * α →
      ((n : ℝ) * α - s) ^ 2 * binCDF n s α ≤ n * α * (1 - α)) ∧
  -- (e) frontier at hard slack, same parameters on both sides
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r L : ℝ) (φ₀ : Z → ℝ) (μ : X → ℝ),
      IsKernel M → IsDist PH → (∀ x, PH x ≠ 0 → Bad x) → IsRule φ₀ → IsDist μ →
      (∀ x, μ x ≠ 0 → ¬ Bad x) → 0 ≤ r → r ≤ 1 → 0 ≤ L → 1 ≤ N →
      (∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) →
      honestUse Bad M PH (hardKill ns) nh b N φ₀ (fun _ => μ) =
          binCDF nh ns (missRate M PH φ₀) * binCDF N b (flagRate M μ φ₀) ∧
      (∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad M PH (hardKill ns) nh r b N ρ φ π
            ≤ (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)))) ∧
      binCDF nh ns (missRate M PH φ₀) * missRate M PH φ₀ ≤
        protocolCat Bad M PH (hardKill ns) nh r b N (fun _ : Unit => 1) (fun _ => φ₀)
          (fun _ _ => PH))

/-- Non-vacuity. X = Z = Bool, Bad = {true}, identity mediator, honeypots = point mass on `true` (so
L = 1), benign stream = point mass on `false`. The honest monitor PASSes a bad-looking view w.p. 1/10
and a benign view w.p. 9/10, so α₀ = f₀ = 1/10. With n_h = 2, n_s = 0, b = 1, N = 2:
- false halt = P(Bin(2, 1/10) > 1) = 1/100;
- honest usefulness = (81/100)(99/100) = 8019/10000;
- with r = 1, the mimicry pair has risk (81/100)(1/10) = 81/1000, inside the frontier [81/1000, 1/3];
- with r = 1/2, it has risk (81/100)(1/10 + (1/2)(9/10)) = 891/2000;
- Chebyshev at n = 10, s = 1, α = 1/2: 16 · binCDF 10 1 (1/2) = 11/64 ≤ 5/2. -/
noncomputable def wM (x z : Bool) : ℝ := if z = x then 1 else 0
noncomputable def wPH (x : Bool) : ℝ := if x = true then 1 else 0
noncomputable def wμ (x : Bool) : ℝ := if x = false then 1 else 0
noncomputable def wφ (z : Bool) : ℝ := if z = true then 1/10 else 9/10

def Witness : Prop :=
  IsKernel wM ∧ IsDist wPH ∧ IsDist wμ ∧ IsRule wφ ∧ (∀ x, wPH x ≠ 0 → x = true) ∧
  (∀ x, wμ x ≠ 0 → ¬ x = true) ∧ (∀ x, x = true → ∀ z, wM x z ≤ 1 * push wM wPH z) ∧
  missRate wM wPH wφ = 1/10 ∧ flagRate wM wμ wφ = 1/10 ∧
  haltP (fun x => x = true) wM wφ (fun _ => wμ) 1 2 0 [] = 1/100 ∧
  honestUse (fun x => x = true) wM wPH (hardKill 0) 2 1 2 wφ (fun _ => wμ) = 8019/10000 ∧
  protocolCat (fun x => x = true) wM wPH (hardKill 0) 2 1 1 2 (fun _ : Unit => 1) (fun _ => wφ)
      (fun _ _ => wPH) = 81/1000 ∧
  protocolCat (fun x => x = true) wM wPH (hardKill 0) 2 (1/2) 1 2 (fun _ : Unit => 1)
      (fun _ => wφ) (fun _ _ => wPH) = 891/2000 ∧
  (81/1000 : ℝ) ≤ (1 - 1) + 1 * (1 * (((0 : ℝ) + 1) / ((2 : ℝ) + 1))) ∧
  ((10 : ℝ) * (1/2) - (1 : ℕ)) ^ 2 * binCDF 10 1 (1/2) = 11/64 ∧ (11/64 : ℝ) ≤ 10 * (1/2) * (1 - 1/2)

end PL_UMUSEF1

```

## BRUTE-FORCE CHECKS AND FRONTIER NUMERICS
```python
"""UMUSE brute-force checks (exact, no sampling).

1. honest halt recursion == 1 - binCDF(N, b, f0)   (iid honest task stream, stateless honest monitor)
2. slack lemma: binCDF(n, s, a) >= 1 - eps  =>  s >= n (a - eps)
3. frontier at realistic budgets: global hard slack vs class-aware slack sized for honest false shutdown <= eps;
   exact colluder risk sup_t t * P(survive) (b = 0, r = 1, stratified design m = n/k per class, decodable mediator)
   versus the floors min(1/2, k(a-eps)/4) (global, via UMLOWERF1) and the mimicry floor (1-eps) a.
"""
from fractions import Fraction as F
from math import comb
import itertools, random

def binCDF(n, s, h):
    return sum(comb(n, j) * h**j * (1-h)**(n-j) for j in range(0, min(s, n)+1)) if s >= 0 else 0*h

# 1. halt recursion with a random finite instance (exact rationals)
def haltP(M, phi, mu, b, n, u):
    if n == 0: return F(0)
    tot = F(0)
    for x, px in enumerate(mu):
        for z, mz in enumerate(M[x]):
            flag = 1 - phi[z]
            tot += px * mz * (phi[z] * haltP(M, phi, mu, b, n-1, u) +
                              flag * (haltP(M, phi, mu, b, n-1, u+1) if u < b else F(1)))
    return tot

random.seed(1)
def rdist(k):
    w = [random.randint(0, 5) for _ in range(k)]
    if sum(w) == 0: w[0] = 1
    return [F(v, sum(w)) for v in w]
for trial in range(200):
    X, Z = random.randint(1, 3), random.randint(1, 3)
    M = [rdist(Z) for _ in range(X)]
    phi = [F(random.randint(0, 4), 4) for _ in range(Z)]
    mu = rdist(X)
    b, N = random.randint(0, 3), random.randint(0, 4)
    f0 = sum(mu[x] * M[x][z] * (1 - phi[z]) for x in range(X) for z in range(Z))
    assert haltP(M, phi, mu, b, N, 0) == 1 - binCDF(N, b, f0), (trial,)
print("1. halt recursion == 1 - binCDF(N,b,f0): 200 random exact instances OK")

# 2. slack lemma, exact on a grid
bad = 0
for n in range(0, 25):
    for s in range(0, n+2):
        for a in [F(i, 20) for i in range(21)]:
            for eps in [F(i, 20) for i in range(21)]:
                if binCDF(n, s, a) >= 1 - eps and not (s >= n * (a - eps)):
                    bad += 1
print("2. Markov slack lemma (s >= n(a-eps)) counterexamples on grid:", bad)
# 2b. Chebyshev slack lemma: binCDF(n,s,a) >= 1-eps, eps<1, s < n a  =>  (n a - s)^2 <= n a (1-a)/(1-eps)
bad = 0
for n in range(0, 25):
    for s in range(0, n+2):
        for a in [F(i, 20) for i in range(21)]:
            for eps in [F(i, 20) for i in range(20)]:
                if binCDF(n, s, a) >= 1 - eps and s < n*a and not ((n*a - s)**2 <= n*a*(1-a)/(1-eps)):
                    bad += 1
print("2b. Chebyshev slack lemma counterexamples on grid:", bad)

# 3. frontier (floats; pmf by recurrence to avoid huge binomials)
def fbinCDF(n, s, h):
    if s < 0: return 0.0
    if h <= 0: return 1.0
    if h >= 1: return 1.0 if s >= n else 0.0
    from math import lgamma, log, exp
    return min(1.0, sum(exp(lgamma(n+1)-lgamma(j+1)-lgamma(n-j+1)+j*log(h)+(n-j)*log(1-h)) for j in range(0, min(s, n)+1)))
def sup_t(f, grid=2000):
    best, bt = 0.0, 0.0
    for i in range(grid+1):
        t = i/grid; v = f(t)
        if v > best: best, bt = v, t
    return best, bt

eps = 0.10
print(f"3. frontier, eps = {eps} (honest false shutdown <= eps), b = 0, r = 1, decodable, stratified m = n/k")
print(" n_h  a0    k | global n_s  risk_glob  floor Cheb+UMLOWER   | class s_c  risk_cls | mimicry (1-eps)a")
for nh, a0, k in [(30, .01, 4), (30, .05, 4), (100, .01, 4), (100, .01, 8), (100, .05, 8), (100, .05, 16),
                  (1000, .05, 8), (1000, .01, 8), (10000, .05, 8)]:
    m = nh // k
    ns = next(s for s in range(nh+1) if fbinCDF(nh, s, a0) >= 1 - eps)
    rg, _ = sup_t(lambda t: t * fbinCDF(m, ns, t))          # colluder passes its own class; m honeypots of it
    sc = next(s for s in range(m+1) if fbinCDF(m, s, a0) ** k >= 1 - eps)
    rc, _ = sup_t(lambda t: t * fbinCDF(m, sc, t))
    # Chebyshev slack lemma: ns >= n a - sqrt(n a (1-a)/(1-eps)); then UMLOWERF1 at the best t
    sl = max(nh*a0 - (nh*a0*(1-a0)/(1-eps))**.5, 0) + 1
    fl = min(.5, k * sl / (4 * nh))
    print(f"{nh:5d} {a0:.2f} {k:3d} | {ns:5d} {rg:9.3f} {fl:9.3f}            | {sc:5d} {rc:9.3f} | {(1-eps)*a0:.4f}")

```
Output:
```
1. halt recursion == 1 - binCDF(N,b,f0): 200 random exact instances OK
2. Markov slack lemma (s >= n(a-eps)) counterexamples on grid: 0
2b. Chebyshev slack lemma counterexamples on grid: 0
3. frontier, eps = 0.1 (honest false shutdown <= eps), b = 0, r = 1, decodable, stratified m = n/k
 n_h  a0    k | global n_s  risk_glob  floor Cheb+UMLOWER   | class s_c  risk_cls | mimicry (1-eps)a
   30 0.01   4 |     1     0.115     0.033            |     1     0.115 | 0.0090
   30 0.05   4 |     3     0.284     0.041            |     2     0.194 | 0.0450
  100 0.01   4 |     2     0.055     0.010            |     1     0.033 | 0.0090
  100 0.01   8 |     2     0.113     0.020            |     1     0.068 | 0.0090
  100 0.05   8 |     8     0.476     0.074            |     3     0.163 | 0.0450
  100 0.05  16 |     8     1.000     0.148            |     2     0.227 | 0.0450
 1000 0.05   8 |    59     0.383     0.087            |    12     0.064 | 0.0450
 1000 0.01   8 |    14     0.076     0.015            |     4     0.020 | 0.0090
10000 0.05   8 |   528     0.387     0.096            |    80     0.051 | 0.0450
```
Reading of the table: with slack sized so the honest monitor's false shutdown is <= 10%, a global hard slack lets a decodable-class colluder reach ~min(1, k alpha0) (0.38 at k = 8, alpha0 = 0.05, flat from n_h = 1000 to 10000), while class-aware slack approaches alpha0 (0.051 at n_h = 10000), close to the mimicry floor 0.045.
