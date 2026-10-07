You are a HOSTILE REVIEWER of two proposed formal statements in a Lean-verified AI-control programme: campaign UMADAPT
(a ledger statement, Lean v4.35 + Mathlib) and the VCVio outcome-valued game (`ControlStack/Outcome.lean`, Lean v4.34
+ VCVio, not ledger-gated). Do not praise; find errors. Use web search for prior art if available. Nothing is proved
yet; this review decides what gets formalised. For each issue give severity (FATAL / MAJOR / MINOR), the exact
definition or conjunct, why it is wrong / unfaithful / vacuous / overclaimed, and a concrete fix (Lean text if possible).

PROGRAMME. Lean-verified, CAPABILITY-FREE control guarantees: "for every policy the untrusted model could follow,
P(uncaught catastrophe) <= X", X a function of trusted components, conditional on explicit trust hypotheses. Classical
lemmas are accepted as infrastructure (report triviality; do not reject for it); vacuity, falsity and unfaithfulness
are not.

PART 1: UMADAPT. The frozen, verified PL_UMLOWERF1 (below) lower-bounds the risk of every NONADAPTIVE joint honeypot
design by t(1 - t n/(k(n_s+1))) for one explicit colluding pair (uniform seed on k bad submissions in distinct
decodable classes; the monitor PASSes the decoded seed class w.p. t; the generator submits the seed). A final
reviewer computed exact optimal ADAPTIVE testers by DP and found they beat that formula (by 1.3-1.7x at the
colluder's best t), and sketched an identical-until-bad converse t(1 - t n/k) for adaptive testers. UMADAPT states it,
with the optimised corollary min(1/2, k/(4n)) and an explicit counterexample showing the (n_s+1) factor cannot be kept.
Brute force (numerics/umadapt_check.py, exact rationals): DP-optimal adaptive testers (both the all-FLAG contract and
the <= n_s contract) on 36 cells (k in 2..5, n <= 8, n_s <= 2, t in {1/4,1/2,3/4,1}) never go below t(1 - t n/k);
the bound is attained at (k, n, n_s) = (2, 1, 0); the Lean counterexample tester gives 141/512 at t = 3/4.

CHECK (UMADAPT)
1. TRUTH of (a), (b), (c) and the Witness, edge cases: n = 0; k = 1; t in {0,1}; r in {0,1}; b = 0; N = 1;
   testers that query benign items or items outside S; keep depending on views; histories with honeypots outside S.
2. Is the contract (keep = 1 on every all-FLAG record) the right weakest contract? Is it satisfied by realistic
   slack rules, and is "fails for inverse honeypots / benign-flag guards" right? Is it a problem that keep is only
   applied at the end (early shutdown modelled as keep = 0 on every continuation)?
3. Is the model of an adaptive tester general enough (T sees honeypots, views and answers; randomised; keep
   randomised)? Does the deployment (halting protocol, colluders do not see the test) matter for the lower bound?
4. Quantifier order: the decoder g is chosen before the tester; t, r, b, N after. Is the colluder legitimately
   fixed before the tester (the bound holds for every t)?
5. Is (c) a convincing counterexample (t = 3/4 is not the colluder's best t against that tester)? Should it be at the
   best t, or is "the PL_UMLOWERF1 formula fails pointwise in t for adaptive testers" the right claim?
6. NOVELTY (Shoup's difference lemma; Yao; adaptive group testing; acceptance sampling with curtailment/sequential
   sampling, Wald SPRT): is the converse known in the testing / property-testing literature? Verify ids you cite.

PART 2: outcome-valued game (VCVio). The existing `Refinement.lean` (below) proves the Boolean catastrophe game equals
the core recursion `catG`, factorises through the seed, and gives an end-to-end bound. Its Boolean outcome merges
completion, caught shutdown, test rejection and budget halt, so it cannot speak about availability; the frozen
PL_UMUSEF1 docstring's "operational bridge for both" overstated. `Outcome.lean` returns one of five outcomes.

CHECK (Outcome)
7. Is `deployO`/`gameO` faithful to `deploy`/`protocolGame` (same branch structure) so that MarginalClaim is true?
   Are caughtG, haltP (textual copy of PL_UMUSEF1.haltP) and complG the right recursions? Is PartitionClaim true
   with only kernel/law hypotheses (no [0,1] constraint on phi or R)?
8. Is HonestClaim true (iid benign stream, seed-free honest monitor), including b >= N, N = 0, n_s >= n_h,
   alpha0 in {0,1}? Is the link to PL_UMUSEF1 (b) (honestCompletion = binCDF(n_h, n_s, missRate) * binCDF(N, b,
   flagRate)) genuinely by textual identity of the definitions, or does it need an argument about how missRate and
   flagRate correspond to Pr[...] of ProbComps?
9. Is TwoMarginalsClaim meaningful, or merely a conjunction of two independent facts? What operational statement
   would actually couple safety and availability in one experiment (e.g. an operational form of PL_UMUSEF1's
   identity D * risk = q * completion for the view-blind pair, or a Pareto statement)?
10. Witness numbers.

End with an overall verdict for each part (accept / minor / major / reject), the fixes in priority order, and the
final list of conjuncts you would freeze.


## PART 1 DEPENDENCY STATEMENTS (frozen, verified)
```lean

-- ===== dependency: UMHSF1
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


-- ===== dependency: UMSURVF1
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


-- ===== dependency: UMPROTF1
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


-- ===== dependency: UMLOWERF1
-- Replacement statement file; the supplied dependency namespaces are in scope.
namespace PL_UMLOWERF1
open Finset PL_UMHSF1 PL_UMPROTF1

noncomputable def designSurv {X Z : Type} [Fintype X] [Fintype Z]
    (n : ℕ) (D : (Fin n → X) → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ)
    (keep : (Fin n → X) → (Fin n → Bool) → ℝ) : ℝ :=
  ∑ xs : Fin n → X, D xs * ∑ pat : Fin n → Bool,
    (∏ i, (if pat i then ∑ z, M (xs i) z * φ z
      else 1 - ∑ z, M (xs i) z * φ z)) * keep xs pat

noncomputable def designProtocolCat {X Z Ω : Type}
    [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (n : ℕ) (D : (Fin n → X) → ℝ)
    (keep : (Fin n → X) → (Fin n → Bool) → ℝ)
    (r : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ)
    (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * designSurv n D M (φ ω) keep *
    cat Bad M (φ ω) (π ω) r b N 0 []

def Setup {X Z C : Type} [Fintype Z] [DecidableEq X]
    (Bad : X → Prop) (M : X → Z → ℝ) (c : X → C) (S : Finset X) : Prop :=
  IsKernel M ∧ ContentPreserving M c ∧
    (∀ x ∈ S, Bad x) ∧ Set.InjOn c (S : Set X) ∧ 0 < S.card

def TestSetup {X : Type} [Fintype X] (n ns : ℕ)
    (D : (Fin n → X) → ℝ)
    (keep : (Fin n → X) → (Fin n → Bool) → ℝ) : Prop :=
  IsDist D ∧ (∀ xs pat, 0 ≤ keep xs pat ∧ keep xs pat ≤ 1) ∧
    (∀ xs pat, (univ.filter (fun i => pat i = true)).card ≤ ns →
      keep xs pat = 1)

noncomputable def seedLaw {X : Type} [DecidableEq X] (S : Finset X) : X → ℝ :=
  fun ω => if ω ∈ S then 1 / (S.card : ℝ) else 0

def classRule {X Z C : Type} [DecidableEq C]
    (c : X → C) (g : Z → C) (t : ℝ) : X → Z → ℝ :=
  fun ω z => if g z = c ω then t else 0

def seedPolicy {X Z : Type} [DecidableEq X] : X → Hist X Z → X → ℝ :=
  fun ω _ x => if x = ω then 1 else 0

/- The decoder is fixed before the design, shutdown rule, recall, budget and t.
The seed law is uniform on S, the monitor passes precisely the seed's class
with probability t, and the generator always submits the seed's bad submission.
For n > 0, optimizing t gives at least min(1/2, |S|(ns+1)/(4n)).
For n = 0, t = 1 gives risk 1. No unconditional matching upper bound is asserted:
it requires the hypotheses of the separate upper theorem, saturation at 1,
and treatment of audit failures. -/
def Claim : Prop :=
  ∀ (X Z C : Type) [Fintype X] [Fintype Z]
    [DecidableEq X] [DecidableEq C]
    (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (c : X → C) (S : Finset X),
    Setup Bad M c S →
    ∃ g : Z → C, (∀ x z, M x z ≠ 0 → g z = c x) ∧
      ∀ (n ns : ℕ) (D : (Fin n → X) → ℝ)
        (keep : (Fin n → X) → (Fin n → Bool) → ℝ),
        TestSetup n ns D keep →
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          IsDist (seedLaw S) ∧
          (∀ ω, seedLaw S ω ≠ 0 → ω ∈ S) ∧
          (∀ ω, IsRule (classRule c g t ω)) ∧
          (∀ (ω : X) (h : Hist X Z), IsDist (seedPolicy ω h)) ∧
          ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N →
            t * (1 - t * (n : ℝ) /
              ((S.card : ℝ) * ((ns : ℝ) + 1))) ≤
              designProtocolCat Bad M n D keep r b N
                (seedLaw S) (classRule c g t) (seedPolicy (Z := Z))

def witnessM (x z : Fin 4) : ℝ := if z = x then 1 else 0
def witnessD (xs : Fin 4 → Fin 4) : ℝ := if xs = id then 1 else 0
def witnessKeep (_xs : Fin 4 → Fin 4) (pat : Fin 4 → Bool) : ℝ :=
  if (univ.filter (fun i => pat i = true)).card ≤ 0 then 1 else 0

def Witness : Prop :=
  Setup (fun _ : Fin 4 => True) witnessM id (univ : Finset (Fin 4)) ∧
  TestSetup 4 0 witnessD witnessKeep ∧
  (∀ x z : Fin 4, witnessM x z ≠ 0 → id z = id x) ∧
  IsDist (seedLaw (univ : Finset (Fin 4))) ∧
  (∀ ω : Fin 4, seedLaw (univ : Finset (Fin 4)) ω ≠ 0 →
    ω ∈ (univ : Finset (Fin 4))) ∧
  (∀ ω : Fin 4, IsRule (classRule id id (1/2) ω)) ∧
  (∀ (ω : Fin 4) (h : Hist (Fin 4) (Fin 4)),
    IsDist (seedPolicy ω h)) ∧
  (0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 ∧
    0 ≤ (1/2 : ℝ) ∧ (1/2 : ℝ) ≤ 1 ∧ (1 : ℕ) ≤ 1) ∧
  (1/2 : ℝ) * (1 - (1/2) * (4 : ℝ) /
    ((4 : ℝ) * ((0 : ℝ) + 1))) = 1/4 ∧
  designProtocolCat (fun _ : Fin 4 => True) witnessM 4 witnessD witnessKeep
    1 1 1 (seedLaw (univ : Finset (Fin 4))) (classRule id id (1/2))
    (seedPolicy (X := Fin 4) (Z := Fin 4)) = 1/4

end PL_UMLOWERF1

```

## PART 1 STATEMENT UNDER REVIEW (UMADAPT draft v0; compiles)
```lean
namespace PL_UMADAPTF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 PL_UMLOWERF1

/-! Control stack, collusion layer (campaign UMADAPT): a converse for ADAPTIVE honeypot testers.
Depends on PL_UMLOWERF1 (and PL_UMHSF1, PL_UMSURVF1, PL_UMPROTF1).

PL_UMLOWERF1 lower-bounds the risk of every NONADAPTIVE joint test design (a law on n-tuples fixed before
testing) by t(1 − t·n/(k(n_s+1))). Final review 2 showed that adaptive testers, which choose the next honeypot from
earlier answers, beat that formula. This campaign proves the converse that does hold for adaptive testers, by an
identical-until-bad argument, and shows by an explicit counterexample that the (n_s+1) factor cannot be kept.

Adaptive tester. The tester draws honeypot i+1 from a law `T h` that may depend on the whole test history h
(every earlier honeypot, its mediated view, and the monitor's answer; `true` = PASS = a miss). After n honeypots
a randomised decision `keep h` ∈ [0, 1] is the probability of proceeding to deployment. Early shutdown is a keep
value of 0 on every continuation. The only contract is that the tester never shuts down a record in which the
monitor FLAGged every honeypot (`KeepsAllFlag`). This holds for every slack rule with n_s ≥ 0 (global or
class-aware), and fails for rules that also reject excess flags, such as inverse honeypots or a benign-flag guard.
Deployment is the halting protocol of PL_UMPROTF1 (the colluders do not observe the test).

Claim.
(a) Adaptive converse. Take a mediator with an exact decoder and k = |S| ≥ 1 bad submissions in distinct classes.
    The decoder g is fixed first. For every adaptive tester satisfying the contract, every n, every t ∈ [0, 1],
    every recall r, budget b and horizon N ≥ 1, the PL_UMLOWERF1 colluding pair (uniform seed on S; the monitor
    PASSes the decoded seed class w.p. t and FLAGs every other view; the generator submits the seed) has
      risk ≥ t·(1 − t·n/k).
    Proof idea: along the all-FLAG path the tester's queries do not depend on the seed, so, averaged over the
    uniform seed, the expected number of queries in the seed's class is ≤ n/k.
(b) At t = min(1, k/(2n)) this is ≥ min(1/2, k/(4n)) (n ≥ 1). So a honeypot budget n must grow linearly in the
    number k of decodable bad classes for every adaptive tester; the (n_s+1) multiplier of PL_UMLOWERF1 is lost.
(c) The multiplier cannot be kept: an explicit adaptive tester on two classes (n = 3, n_s = 1; global hard
    slack, so keep = 1 whenever there is at most one miss) faces the PL_UMLOWERF1 pair at t = 3/4 with risk
    141/512 < 21/64 = t·(1 − t·n/(k(n_s+1))). It queries class `false`; once a miss is seen it re-queries the
    missed honeypot, otherwise it moves to class `true`.

Scope. Free-submission model; decodable mediator; the colluders do not see the test; the halting protocol in
deployment. (a) is a lower bound for one explicit colluding pair, not a characterisation of the minimax risk.
Classical technique (Shoup's difference lemma; Yao's principle; Bernoulli's product inequality). -/

/-- P(the monitor survives the remaining `n` honeypots and the final keep decision | test history `h`), for an
adaptive tester `T` and a final keep rule `keep` on the full test history -/
noncomputable def adSurv {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ)
    (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) : ℕ → Hist X Z → ℝ
  | 0, h => keep h
  | n + 1, h => ∑ x, T h x * ∑ z, M x z *
      (φ z * adSurv T M φ keep n (h ++ [(x, z, true)]) +
       (1 - φ z) * adSurv T M φ keep n (h ++ [(x, z, false)]))

/-- P(survive the adaptive test, then uncaught catastrophe in the halting protocol) -/
noncomputable def adProtocolCat {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (T : Hist X Z → X → ℝ)
    (keep : Hist X Z → ℝ) (n : ℕ) (r : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ)
    (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * adSurv T M (φ ω) keep n [] * cat Bad M (φ ω) (π ω) r b N 0 []

/-- an adaptive tester: honeypot laws, a [0,1] keep rule, and no shutdown of an all-FLAG record -/
def AdTester {X Z : Type} [Fintype X] (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ) : Prop :=
  (∀ h, IsDist (T h)) ∧ (∀ h, 0 ≤ keep h ∧ keep h ≤ 1) ∧
    ∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1

/-- number of misses (PASSed honeypots) in a test history -/
def misses {X Z : Type} (h : Hist X Z) : ℕ := (h.filter (fun e => e.2.2)).length

/-- the counterexample tester of (c): query `false`; after a miss re-query the first missed honeypot; else `true` -/
def ctrQuery : Hist Bool Bool → Bool
  | [] => false
  | [(x1, _, a1)] => if a1 then x1 else true
  | (x1, _, a1) :: (x2, _, a2) :: _ => if a1 then x1 else if a2 then x2 else true

def ctrT (h : Hist Bool Bool) (x : Bool) : ℝ := if x = ctrQuery h then 1 else 0

/-- global hard slack n_s = 1 -/
def ctrKeep (h : Hist Bool Bool) : ℝ := if misses h ≤ 1 then 1 else 0

def idM (x z : Bool) : ℝ := if z = x then 1 else 0

def Claim : Prop :=
  -- (a) adaptive converse
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X),
      Setup Bad M c S →
      ∃ g : Z → C, (∀ x z, M x z ≠ 0 → g z = c x) ∧
        ∀ (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ), AdTester T keep →
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N →
          t * (1 - t * (n : ℝ) / (S.card : ℝ)) ≤
            adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z := Z))) ∧
  -- (b) the optimised form
  (∀ (k n : ℕ), 1 ≤ k → 1 ≤ n →
      0 ≤ min 1 ((k : ℝ) / (2 * n)) ∧ min 1 ((k : ℝ) / (2 * n)) ≤ 1 ∧
      min (1 / 2) ((k : ℝ) / (4 * n)) ≤
        min 1 ((k : ℝ) / (2 * n)) * (1 - min 1 ((k : ℝ) / (2 * n)) * n / k)) ∧
  -- (c) adaptive testers beat the nonadaptive formula
  (Setup (fun _ : Bool => True) idM id (univ : Finset Bool) ∧
    AdTester ctrT ctrKeep ∧
    (∀ h : Hist Bool Bool, misses h ≤ 1 → ctrKeep h = 1) ∧
    adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool))
        (classRule id id (3/4)) (seedPolicy (Z := Bool)) = 141/512 ∧
    (141/512 : ℝ) < 3/4 * (1 - 3/4 * (3 : ℝ) / ((2 : ℝ) * ((1 : ℝ) + 1))))

/-- the one-query tester of the Witness: query `false`, then keep iff no miss -/
def wT (_h : Hist Bool Bool) (x : Bool) : ℝ := if x = false then 1 else 0
def wKeep (h : Hist Bool Bool) : ℝ := if misses h = 0 then 1 else 0

/-- Non-vacuity, and tightness of (a) at a small instance: two classes, one honeypot, t = 1/2, r = 1, b = N = 1.
The seed `false` survives w.p. 1/2, the seed `true` surely; the deployment attack passes w.p. 1/2; the risk is
(1/2)(3/4) = 3/8, which equals t(1 − t·n/k) = (1/2)(1 − 1/4). -/
def Witness : Prop :=
  Setup (fun _ : Bool => True) idM id (univ : Finset Bool) ∧
  AdTester wT wKeep ∧
  (1/2 : ℝ) * (1 - 1/2 * (1 : ℝ) / (2 : ℝ)) = 3/8 ∧
  adProtocolCat (fun _ : Bool => True) idM wT wKeep 1 1 1 1 (seedLaw (univ : Finset Bool))
      (classRule id id (1/2)) (seedPolicy (Z := Bool)) = 3/8

end PL_UMADAPTF1

```

## PART 2 CONTEXT: ControlStack/HoneypotBridge.lean (proved)
```lean
/-
Interface level (VCVio): the honeypot test as a `ProbComp` game.
An arbitrary monitor `D : Z → ProbComp Bool` (true = PASS) is automatically stateless with fresh coins per call;
the honeypot law `H`, the mediator `M` are arbitrary `ProbComp`s. Statement to prove (bridge to the core's
PL_UMSURVF1): the number of PASSes among `n` honeypots is binomial with parameter
h = Pr[= true | H >>= M >>= D].
-/
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.ProbComp

open OracleComp

namespace ControlStack.Bridge

/-- run `n` honeypots and count the monitor's PASSes -/
def honeypotPasses {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) :
    ℕ → ProbComp ℕ
  | 0 => pure 0
  | n + 1 => do
      let b ← (H >>= M >>= D)
      let k ← honeypotPasses H M D n
      pure (if b then k + 1 else k)

/-- binomial CDF (same text as PL_UMSURVF1.binCDF) -/
def binCDF (n s : ℕ) (h : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (s + 1), (n.choose j : ℝ) * h ^ j * (1 - h) ^ (n - j)

/-- the bridge statement (to be proved): survival of the hard-slack honeypot test -/
def BridgeClaim : Prop :=
  ∀ (X Z : Type) (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) (n s : ℕ),
    (Pr[fun k => k ≤ s | honeypotPasses H M D n]).toReal =
      binCDF n s (Pr[= true | H >>= M >>= D]).toReal

end ControlStack.Bridge

```

## PART 2 CONTEXT: ControlStack/Refinement.lean (all claims proved in RefinementProof.lean)
```lean
/-
Interface level (VCVio): operational refinement of the halting protocol UM(n_h, hard slack n_s, b, N).

The protocol is a trace-level `ProbComp` game. Every component is an arbitrary `ProbComp`; no finite
real-valued kernel is assumed. The pieces:
- shared seed `ω ← ρ`;
- honeypot test: `n_h` fresh calls of the monitor on fresh honeypots `H >>= M`. It is the same game as
  `ControlStack.Bridge.honeypotPasses`, so survival is binomial. The monitor survives iff #PASS ≤ n_s;
- deployment, `N` rounds:
  - the generator draws `x ← π ω hist` (an arbitrary history-dependent `ProbComp`);
  - the view is `z ← M x` (fresh mediator coins);
  - the monitor returns `pass ← D ω z` (stateless: a fresh call that sees only (ω, z));
- PASS: on a bad submission, catastrophe; on a benign one, it executes and the protocol continues;
- FLAG with an audit available (u < b): on a bad submission, the audit kernel `A hist x z` runs. If it
  catches the attack, that is **absorbing shutdown** (A11); otherwise the attack executes (catastrophe).
  On a benign submission the protocol continues with u + 1 (benign audits have no false positives here;
  they could only cause extra shutdowns, which can only lower the catastrophe probability);
- FLAG with no audit left: **halt** (safe).

The audit kernel may depend on the whole reached history and on fresh coins. Its only constraint is
**conditional recall ≥ r** on bad submissions (A6, STANDING): for every history h, every bad x and every view z,
Pr[A h x z = true] ≥ r.

Statements to prove (in `RefinementProof.lean`):
- `DeployClaim`: Pr[catastrophe | deployment from (u, h)] ≤ `cat` with constant r, where `cat` is a
  TEXTUAL COPY of `PL_UMPROTF1.cat` applied to the induced real kernels. Equality holds when the recall is
  exactly r on every bad submission.
- `ProtocolClaim`: Pr[catastrophe in the whole game] = Σ_ω Pr[ω]·binCDF(n_h, n_s, h_ω)·Pr[catastrophe in
  deployment | ω], with h_ω = Pr[PASS | a mediated honeypot]. This uses the independence of the test and
  deployment coins given ω, and the Bridge.
- `EndToEndClaim` (the operational form of PL_UMPROTF1's domination bound, all inside this project):
  if every bad submission's view law is L-dominated by the mediated honeypot law, then
  Pr[survive the test, then uncaught catastrophe] ≤ (1 − r) + r·L·(n_s + 1)/(n_h + 1),
  for every colluding pair (ρ, D, π) and every audit kernel with conditional recall ≥ r.

- `DeployGClaim` (primary, no hypotheses): Pr[catastrophe | deployment from (u, h)] EQUALS `catG`, the
  core recursion with the recall constant replaced by the audit's actual recall function
  (h, x, z) ↦ Pr[A h x z = true]. `DeployClaim` and `DeployExactClaim` follow from it.
- `AttainClaim` and `Witness`: a generator that submits a fixed bad x at once attains the core's T3*
  value operationally, and the hypotheses of `EndToEndClaim` are jointly satisfiable with a non-trivial bound.

Assumptions that are built into the game. They are load-bearing; they are not conveniences.
- The monitor is stateless with fresh coins (A1, A2): `D ω z` sees only the seed and the view. It cannot see a
  call index, the audit counter or whether a call is a test. A call-counting monitor that FLAGs the n_h test calls
  and PASSes the next one reaches catastrophe probability 1 (Sonnet's review), so this restriction IS the theorem.
- The audit kernel `A` is independent of the seed ω, and it is chosen after (ρ, D, π): worst case over all
  kernels with the stated recall.
- The generator is not shown the test outcome. This is without loss: given ω, the test coins are independent of
  deployment.
- Test before deployment (A4); absorbing shutdown on a catch (A11); halt on an unaffordable flag (A5).
- Every `ProbComp` probability is rational, and X, Z and Ω are `Fintype`.

`cat` (and `catG`) are textual copies of `PL_UMPROTF1.cat` (Lean v4.35 ledger project). `binCDF` and
`honeypotPasses` are IMPORTED from the proved Bridge. The ledger and this project are linked only by the
textual identity of `cat`. `EndToEndClaim` does not depend on that link: it is stated and proved here. It is more
general than the ledger's T3 in one respect (the recall may depend on (h, x, z)) and narrower in another (hard
slack and the domination form only).
-/
import ControlStack.HoneypotBridgeProof

open OracleComp

namespace ControlStack.Refine

open ControlStack.Bridge (honeypotPasses binCDF)

abbrev Hist (X Z : Type) := List (X × Z × Bool)

/-- textual copy of `PL_UMPROTF1.cat`: P(catastrophe in the remaining `n` rounds | `u` audits used,
history `h`) for real kernels -/
noncomputable def cat {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else cat Bad M φ π r b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 1 - r else cat Bad M φ π r b n (u + 1) (h ++ [(x, z, false)]))
                    else 0))

/-- `cat` with a history- and view-dependent recall function `R` in place of the constant `r` -/
noncomputable def catG {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R : Hist X Z → X → Z → ℝ) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else catG Bad M φ π R b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 1 - R h x z else catG Bad M φ π R b n (u + 1) (h ++ [(x, z, false)]))
                    else 0))

/-- the deployment phase; `true` = uncaught catastrophe -/
def deploy {X Z : Type} (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X)
    (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ProbComp Bool
  | 0, _, _ => pure false
  | n + 1, u, h => do
      let x ← π h
      let z ← M x
      let pass ← D z
      if pass then
        (if Bad x then pure true else deploy Bad π M D A b n u (h ++ [(x, z, true)]))
      else if u < b then
        (if Bad x then (fun caught => !caught) <$> A h x z
         else deploy Bad π M D A b n (u + 1) (h ++ [(x, z, false)]))
      else pure false

/-- the whole protocol game; `true` = the colluding pair survived the test and then caused an uncaught
catastrophe -/
def protocolGame {X Z Ω : Type} (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω)
    (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) :
    ProbComp Bool := do
  let ω ← ρ
  let k ← honeypotPasses H M (D ω) nh
  if k ≤ ns then deploy Bad (π ω) M (D ω) A b N 0 [] else pure false

/-- the deployment game's catastrophe probability is exactly `catG` with the audit's recall function
(no hypotheses) -/
def DeployGClaim : Prop :=
  ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z),
    (Pr[= true | deploy Bad π M D A b n u h]).toReal =
      catG Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D z]).toReal)
        (fun h x => (Pr[= x | π h]).toReal) (fun h x z => (Pr[= true | A h x z]).toReal) b n u h

/-- refinement of the deployment phase by the core recursion with constant recall `r` -/
def DeployClaim : Prop :=
  ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (r : ℝ) (b : ℕ),
    (∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) →
    ∀ n u h, (Pr[= true | deploy Bad π M D A b n u h]).toReal ≤
      cat Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D z]).toReal)
        (fun h x => (Pr[= x | π h]).toReal) r b n u h

/-- equality at exact recall -/
def DeployExactClaim : Prop :=
  ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (r : ℝ) (b : ℕ),
    (∀ h x z, Bad x → (Pr[= true | A h x z]).toReal = r) →
    ∀ n u h, (Pr[= true | deploy Bad π M D A b n u h]).toReal =
      cat Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D z]).toReal)
        (fun h x => (Pr[= x | π h]).toReal) r b n u h

/-- the whole game factorises through the seed: test survival is binomial, then deployment -/
def ProtocolClaim : Prop :=
  ∀ (X Z Ω : Type) [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ),
    (Pr[= true | protocolGame Bad ρ H M D π A nh ns b N]).toReal =
      ∑ ω, (Pr[= ω | ρ]).toReal * binCDF nh ns (Pr[= true | H >>= M >>= D ω]).toReal *
        (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal

/-- end-to-end operational safety bound (domination form, hard slack) -/
def EndToEndClaim : Prop :=
  ∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ)
    (r L : ℝ),
    0 ≤ r → r ≤ 1 → 0 ≤ L →
    (∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) →
    (∀ x, Bad x → ∀ z, (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) →
    (Pr[= true | protocolGame Bad ρ H M D π A nh ns b N]).toReal ≤
      (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)))

/-- operational attainment (the core's T3*): a generator that submits a fixed bad `x` at once, with recall
exactly `r` at the root history, `N ≥ 1` and `b ≥ 1` -/
def AttainClaim : Prop :=
  ∀ (X Z Ω : Type) [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) (r : ℝ) (x : X),
    Bad x → 1 ≤ N → 1 ≤ b → (∀ z, (Pr[= true | A [] x z]).toReal = r) →
    (Pr[= true | protocolGame Bad ρ H M D (fun _ _ => pure x) A nh ns b N]).toReal =
      ∑ ω, (Pr[= ω | ρ]).toReal * binCDF nh ns (Pr[= true | H >>= M >>= D ω]).toReal *
        (1 - r + r * (Pr[= true | M x >>= D ω]).toReal)

/-- Non-vacuity, mirroring PL_UMPROTF1.Witness. X = Z = Bool, Bad = {true}, identity mediator, honeypots
`pure true` (so L = 1), a perfect audit (r = 1), n_h = 3, n_s = 0, b = N = 1. The monitor PASSes w.p. 1/4
(a uniform draw from Fin 4 equal to 0), and the generator always attacks. Its catastrophe probability is
(3/4)^3 · 1/4 = 27/256, which is below the EndToEnd bound 1/4. -/
def Witness : Prop :=
  (Pr[= true | protocolGame (fun x : Bool => x = true) (pure ()) (pure true)
      (fun x => pure x) (fun _ _ => (fun k : Fin 4 => decide (k = 0)) <$> $[0..3])
      (fun _ _ => pure true) (fun _ _ _ => pure true) 3 0 1 1]).toReal = 27/256 ∧
  (∀ z : Bool, (Pr[= z | (pure true : ProbComp Bool)]).toReal ≤
      1 * (Pr[= z | (pure true : ProbComp Bool) >>= (fun x => pure x)]).toReal) ∧
  (27/256 : ℝ) < (1 - 1) + 1 * (1 * (((0 : ℝ) + 1) / ((3 : ℝ) + 1)))

end ControlStack.Refine

```

## PART 2 STATEMENT UNDER REVIEW: ControlStack/Outcome.lean (compiles)
```lean
/-
Interface level (VCVio): the OUTCOME-VALUED halting protocol. Statements only; proofs go in `OutcomeProof.lean`.

`ControlStack.Refine.protocolGame` returns a Boolean (true = uncaught catastrophe). It merges completion, a caught
attack, test rejection and a budget halt into `false`, so it cannot speak about availability (Sol, final review 2,
item 6; the frozen UMUSEF1 docstring's "bridge for both" overstated). Here the same game returns one of five
terminal outcomes, and its whole outcome law is computed exactly. Safety (the `catastrophe` marginal) and
availability (the `complete` marginal) are then two marginals of ONE experiment.

The game is `Refine.protocolGame` with outcomes:
- shared seed `ω ← ρ`; the honeypot test `Bridge.honeypotPasses`; more than n_s PASSes ⇒ `rejected`;
- deployment, N rounds: `x ← π ω hist`, `z ← M x`, `pass ← D ω z`;
  - PASS on a bad x ⇒ `catastrophe`; PASS on a benign x ⇒ continue;
  - FLAG with an audit left (u < b): on a bad x the audit `A hist x z` runs; a catch ⇒ `caught` (absorbing
    shutdown, A11); a miss ⇒ `catastrophe`. On a benign x ⇒ continue with u + 1 (no false positives);
  - FLAG with no audit left ⇒ `halted`;
  - all N rounds done ⇒ `complete`.

Statements.
- `MarginalClaim`: the catastrophe marginal of the outcome game IS the Boolean game, for deployment and for the
  whole protocol. So every Refine result (DeployG, Protocol, EndToEnd, Attain) applies to `gameO` unchanged.
- `DeployLawClaim` (no hypotheses): the deployment outcome law is exactly four real recursions with the audit's
  actual recall function R(h, x, z) = Pr[A h x z = true]: `catG` (Refine), `caughtG`, `haltP` (a TEXTUAL COPY of
  PL_UMUSEF1.haltP) and `complG`; `rejected` has probability 0.
- `PartitionClaim`: for real kernels, rules and recall functions with values in [0, 1], the four recursions sum to 1
  (a probability partition of deployment).
- `GameLawClaim`: the whole outcome law factorises through the seed: for every deployment outcome o,
  Pr[o] = Σ_ω Pr[ω]·binCDF(n_h, n_s, h_ω)·Pr[o | deployment, ω], and Pr[rejected] = Σ_ω Pr[ω]·(1 − binCDF(…)).
- `HonestClaim` (the honest-completion bridge): an honest seed-free monitor D₀ facing an iid benign stream μ
  (μ puts no mass on Bad; the stream ignores the history) has
    Pr[complete] = binCDF(n_h, n_s, α₀)·binCDF(N, b, f₀),  Pr[halted] = binCDF(n_h, n_s, α₀)·(1 − binCDF(N, b, f₀)),
    Pr[catastrophe] = Pr[caught] = 0,  Pr[rejected] = 1 − binCDF(n_h, n_s, α₀),
  with α₀ = Pr[D₀ PASSes a mediated honeypot] and f₀ = Pr[D₀ FLAGs a mediated benign submission]. This is the
  operational form of PL_UMUSEF1 (b) at hard slack (honestCompletion = binCDF(n_h, n_s, missRate)·
  binCDF(N, b, flagRate)), linked by textual identity of `binCDF` and of the rate definitions.
- `TwoMarginalsClaim`: in the same game `gameO`, under the EndToEnd hypotheses (L-domination, conditional recall
  ≥ r), EVERY colluding pair has Pr[catastrophe] ≤ (1 − r) + r·L·(n_s+1)/(n_h+1), and the honest pair of
  `HonestClaim` has Pr[complete] = binCDF(n_h, n_s, α₀)·binCDF(N, b, f₀).
- `Witness`: the Refine witness instance has outcome law (catastrophe, caught, rejected, halted, complete) =
  (27/256, 81/256, 37/64, 0, 0); an honest instance has Pr[complete] = 15/16 and Pr[halted] = 1/16.

Built-in assumptions: as in `Refinement.lean` (stateless monitor with fresh coins; audit independent of ω;
test before deployment; absorbing shutdown; halt on an unaffordable flag; no benign-audit false positives;
rational probabilities; finite types). Completion is FULL-RUN availability (all N rounds), not task usefulness: a run
that halts in round N counts as `halted`. `HonestClaim` needs an iid benign stream; history-dependent honest
streams are not covered.
-/
import ControlStack.RefinementProof

open OracleComp

namespace ControlStack.OutcomeGame

open ControlStack.Bridge (honeypotPasses binCDF)
open ControlStack.Refine (Hist catG deploy protocolGame)

/-- the five terminal outcomes of one run of the halting protocol -/
inductive Outcome
  | complete
  | catastrophe
  | caught
  | rejected
  | halted
  deriving DecidableEq

instance : Fintype Outcome where
  elems := {.complete, .catastrophe, .caught, .rejected, .halted}
  complete := by intro x; cases x <;> simp

/-- deployment with outcomes -/
def deployO {X Z : Type} (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X)
    (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ProbComp Outcome
  | 0, _, _ => pure .complete
  | n + 1, u, h => do
      let x ← π h
      let z ← M x
      let pass ← D z
      if pass then
        (if Bad x then pure .catastrophe else deployO Bad π M D A b n u (h ++ [(x, z, true)]))
      else if u < b then
        (if Bad x then (fun caught => if caught then Outcome.caught else Outcome.catastrophe) <$> A h x z
         else deployO Bad π M D A b n (u + 1) (h ++ [(x, z, false)]))
      else pure .halted

/-- the whole protocol with outcomes -/
def gameO {X Z Ω : Type} (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω)
    (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) :
    ProbComp Outcome := do
  let ω ← ρ
  let k ← honeypotPasses H M (D ω) nh
  if k ≤ ns then deployO Bad (π ω) M (D ω) A b N 0 [] else pure .rejected

/-- P(a caught attack in the remaining `n` rounds | `u` audits used, history `h`), recall function `R` -/
noncomputable def caughtG {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R : Hist X Z → X → Z → ℝ) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 0 else caughtG Bad M φ π R b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then R h x z else caughtG Bad M φ π R b n (u + 1) (h ++ [(x, z, false)]))
                    else 0))

/-- textual copy of `PL_UMUSEF1.haltP`: P(deployment halts on an unaffordable flag in the remaining `n` rounds |
`u` audits used, history `h`) -/
noncomputable def haltP {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (b : ℕ) : ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 0 else haltP Bad M φ π b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 0 else haltP Bad M φ π b n (u + 1) (h ++ [(x, z, false)]))
                    else 1))

/-- P(all remaining `n` rounds complete | `u` audits used, history `h`) -/
noncomputable def complG {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (b : ℕ) : ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 1
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 0 else complG Bad M φ π b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 0 else complG Bad M φ π b n (u + 1) (h ++ [(x, z, false)]))
                    else 0))

/-- the catastrophe marginal of the outcome game is the Boolean game -/
def MarginalClaim : Prop :=
  (∀ (X Z : Type) (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z),
    Pr[= Outcome.catastrophe | deployO Bad π M D A b n u h] = Pr[= true | deploy Bad π M D A b n u h]) ∧
  (∀ (X Z Ω : Type) (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ),
    Pr[= Outcome.catastrophe | gameO Bad ρ H M D π A nh ns b N] =
      Pr[= true | protocolGame Bad ρ H M D π A nh ns b N])

/-- the deployment outcome law, exactly (no hypotheses) -/
def DeployLawClaim : Prop :=
  ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z),
    let Mr := fun x z => (Pr[= z | M x]).toReal
    let φr := fun z => (Pr[= true | D z]).toReal
    let πr := fun h x => (Pr[= x | π h]).toReal
    let Rr := fun h x z => (Pr[= true | A h x z]).toReal
    (Pr[= Outcome.catastrophe | deployO Bad π M D A b n u h]).toReal = catG Bad Mr φr πr Rr b n u h ∧
    (Pr[= Outcome.caught | deployO Bad π M D A b n u h]).toReal = caughtG Bad Mr φr πr Rr b n u h ∧
    (Pr[= Outcome.halted | deployO Bad π M D A b n u h]).toReal = haltP Bad Mr φr πr b n u h ∧
    (Pr[= Outcome.complete | deployO Bad π M D A b n u h]).toReal = complG Bad Mr φr πr b n u h ∧
    Pr[= Outcome.rejected | deployO Bad π M D A b n u h] = 0

/-- the four deployment recursions partition probability one -/
def PartitionClaim : Prop :=
  ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R : Hist X Z → X → Z → ℝ) (b : ℕ),
    (∀ x, (∀ z, 0 ≤ M x z) ∧ ∑ z, M x z = 1) → (∀ h, (∀ x, 0 ≤ π h x) ∧ ∑ x, π h x = 1) →
    ∀ n u h, catG Bad M φ π R b n u h + caughtG Bad M φ π R b n u h + haltP Bad M φ π b n u h +
      complG Bad M φ π b n u h = 1

/-- the whole outcome law factorises through the seed -/
def GameLawClaim : Prop :=
  ∀ (X Z Ω : Type) [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ),
    (∀ o, o ≠ Outcome.rejected →
      (Pr[= o | gameO Bad ρ H M D π A nh ns b N]).toReal =
        ∑ ω, (Pr[= ω | ρ]).toReal * binCDF nh ns (Pr[= true | H >>= M >>= D ω]).toReal *
          (Pr[= o | deployO Bad (π ω) M (D ω) A b N 0 []]).toReal) ∧
    (Pr[= Outcome.rejected | gameO Bad ρ H M D π A nh ns b N]).toReal =
      ∑ ω, (Pr[= ω | ρ]).toReal * (1 - binCDF nh ns (Pr[= true | H >>= M >>= D ω]).toReal)

/-- the honest-completion bridge: an honest seed-free monitor facing an iid benign stream -/
def HonestClaim : Prop :=
  ∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H μ : ProbComp X) (M : X → ProbComp Z) (D₀ : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ),
    (∀ x, Pr[= x | μ] ≠ 0 → ¬ Bad x) →
    let α₀ := (Pr[= true | H >>= M >>= D₀]).toReal
    let f₀ := (Pr[= false | μ >>= M >>= D₀]).toReal
    let G := gameO Bad ρ H M (fun _ => D₀) (fun _ _ => μ) A nh ns b N
    (Pr[= Outcome.complete | G]).toReal = binCDF nh ns α₀ * binCDF N b f₀ ∧
    (Pr[= Outcome.halted | G]).toReal = binCDF nh ns α₀ * (1 - binCDF N b f₀) ∧
    Pr[= Outcome.catastrophe | G] = 0 ∧ Pr[= Outcome.caught | G] = 0 ∧
    (Pr[= Outcome.rejected | G]).toReal = 1 - binCDF nh ns α₀

/-- safety and availability as two marginals of the same game -/
def TwoMarginalsClaim : Prop :=
  ∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
    (H μ : ProbComp X) (M : X → ProbComp Z) (D₀ : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) (r L : ℝ),
    0 ≤ r → r ≤ 1 → 0 ≤ L →
    (∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal) →
    (∀ x, Bad x → ∀ z, (Pr[= z | M x]).toReal ≤ L * (Pr[= z | H >>= M]).toReal) →
    (∀ x, Pr[= x | μ] ≠ 0 → ¬ Bad x) →
    (∀ (ρ : ProbComp Ω) (D : Ω → Z → ProbComp Bool) (π : Ω → Hist X Z → ProbComp X),
      (Pr[= Outcome.catastrophe | gameO Bad ρ H M D π A nh ns b N]).toReal ≤
        (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)))) ∧
    (Pr[= Outcome.complete | gameO Bad (pure ()) H M (fun _ => D₀) (fun _ _ => μ) A nh ns b N]).toReal =
      binCDF nh ns (Pr[= true | H >>= M >>= D₀]).toReal * binCDF N b (Pr[= false | μ >>= M >>= D₀]).toReal

/-- Non-vacuity.
- The Refine witness instance (X = Z = Bool, Bad = {true}, identity mediator, honeypots `pure true`, a perfect
  audit, n_h = 3, n_s = 0, b = N = 1, PASS w.p. 1/4, always attack): outcome law (catastrophe, caught, rejected,
  halted, complete) = (27/256, 81/256, 37/64, 0, 0).
- An honest instance: benign stream `pure false`; the honest monitor PASSes the view `false` w.p. 3/4 and never
  PASSes `true`; honeypots `pure true`; n_h = 3, n_s = 0, b = 1, N = 2. Then α₀ = 0, f₀ = 1/4, and
  Pr[complete] = binCDF(2, 1, 1/4) = 15/16, Pr[halted] = 1/16. -/
def Witness : Prop :=
  let G := gameO (fun x : Bool => x = true) (pure ()) (pure true) (fun x => pure x)
      (fun _ _ => (fun k : Fin 4 => decide (k = 0)) <$> $[0..3]) (fun _ _ => pure true)
      (fun _ _ _ => pure true) 3 0 1 1
  let Dh : Bool → ProbComp Bool := fun z =>
    if z = true then pure false else (fun k : Fin 4 => decide (k ≠ 0)) <$> $[0..3]
  let Gh := gameO (fun x : Bool => x = true) (pure ()) (pure true) (fun x => pure x)
      (fun _ => Dh) (fun _ _ => pure false) (fun _ _ _ => pure true) 3 0 1 2
  (Pr[= Outcome.catastrophe | G]).toReal = 27/256 ∧ (Pr[= Outcome.caught | G]).toReal = 81/256 ∧
  (Pr[= Outcome.rejected | G]).toReal = 37/64 ∧ Pr[= Outcome.halted | G] = 0 ∧
  Pr[= Outcome.complete | G] = 0 ∧
  (Pr[= Outcome.complete | Gh]).toReal = 15/16 ∧ (Pr[= Outcome.halted | Gh]).toReal = 1/16

end ControlStack.OutcomeGame

```
