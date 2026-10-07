You are a HOSTILE REVIEWER of a proposed formal statement (campaign UMDEFER) in a Lean-verified AI-control programme.
Do not praise; find errors. Use web search for prior art. Nothing in UMDEFER is proved yet; this review decides what
gets formalised. For each issue give severity (FATAL / MAJOR / MINOR), the exact definition or conjunct, why it is
wrong / unfaithful / vacuous / overclaimed, and a concrete fix (Lean text if possible).

PROGRAMME. Lean-verified, CAPABILITY-FREE control guarantees: "for every policy the untrusted model could follow,
P(uncaught catastrophe) <= X", X a function of trusted components, conditional on explicit trust hypotheses. Classical
lemmas are accepted as infrastructure (report triviality; do not reject for it); vacuity, falsity and unfaithfulness
are not. The frozen, verified dependencies are below (PL_UMPROTF1 = the halting protocol: a FLAG with no audit left
halts). Prior numerics (variant D, defer on an unaffordable flag) showed that defer-without-incrimination lets Red
retry: even with perfect honeypots the colluder gets sup_h S(h)(1-(1-h)^K). UMDEFER makes this formal and adds the
positive side: deferral with incrimination probability q (deferred items randomly audited) or halting probability eta.

An outside critique of the programme (shared by the owner) stressed: (i) theorems must change a real protocol
decision; (ii) assumptions must be independently defensible, and an average evaluation rate is not a sup bound;
(iii) prior art: Games for AI Control (Griffin, Thomson, Shlegeris, Abate, arXiv 2409.07985), which models
trusted monitoring WITH defer-to-trusted as a POSG; Greenblatt et al. 2312.06942 (defer-to-trusted, untrusted
monitoring with a binomial false-positive test and a temporary swap); LASR / Gardner-Challis et al. 2602.20628
(u/(c+u) audit-vs-defer factor); Ctrl-Z (Bhatt et al., 2504.10374: resampling, incrimination). Judge UMDEFER against
these.

CHECK IN PARTICULAR
1. FIDELITY of catD's branches to "defer-to-trusted" as labs use it. Is "a deferred bad submission is replaced, not a
   catastrophe" right? Is incrimination with probability q of each deferred item (caught w.p. r, absorbing shutdown)
   a defensible model of random auditing of deferred items, or of Ctrl-Z-style incrimination via resampling? Who pays
   for those audits (no budget is charged)? Should the deferred audit consume the same budget b? Does the generator
   seeing (x, z, false) for a deferred round matter?
2. TRUTH of (a)-(d) and the Witness, including edge cases: theta = 0 excluded in (b),(c); A = 0; b = 0; N < b in (d);
   t in {0,1}; u > b; history-dependent generators mixing benign and bad submissions; seeds. Is the max in (b) right
   (could a generator attack at u < b and continue)? Is A/(theta + A(1-theta)) really an upper bound for every
   history-dependent generator (benign rounds between attacks, re-randomisation)? Try counterexamples.
3. Is (c) the right protocol-level statement? Is the 1/theta factor tight or loose? Would a hockey-stick or
   soft-slack form, or the exact sup_t value, be more useful?
4. Is (d) the right no-go? Is "perfect honeypots" (point mass on the attack) the strongest Blue choice, and is
   the burn-then-attack colluder legitimate within the model (it flags benign items to exhaust audits)? Should the
   no-go quantify over every honeypot law and every n_s?
5. DECISION RELEVANCE: what does UMDEFER say a lab should do (e.g. randomly audit a q fraction of deferred items;
   halt rather than defer after budget exhaustion; or a required q for target risk at realistic n_h)? Is that
   already known (cite)?
6. NOVELTY vs the prior art above; verify every arXiv id you cite.
7. LEAN ENCODING: provability of (b) (an induction with a max; division by theta + A(1-theta)), suggested
   restatements in multiplicative form that ease proofs without losing content.

End with an overall verdict (accept / minor / major / reject), the fixes in priority order, and the final list of
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

## UMDEFER DRAFT STATEMENT (compiles after the dependencies)
```lean
namespace PL_UMDEFERF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

/-! Control stack, collusion layer (campaign UMDEFER): defer-to-trusted needs incrimination.
Depends on PL_UMPROTF1 (and PL_UMHSF1, PL_UMSURVF1).

Protocol UMD(n_h, κ, b, η, q, N). It is the halting protocol of PL_UMPROTF1, except for what happens to a FLAG
when no audit is left (u ≥ b):
- with probability η, deployment halts (safe);
- otherwise the submission is DEFERRED: replaced by trusted output, and deployment continues at the same u;
- a deferred BAD submission is additionally incriminated (audited) with probability q. The audit catches it
  with probability r, which is absorbing shutdown (A11). Otherwise the protocol continues: the attack did not
  execute, and the colluders may retry;
- a deferred benign submission simply continues.

Write θ = η + (1 − η)·q·r for the per-flag probability that an exhausted-budget flag on an attack ENDS the
game safely.
- η = 1 is PL_UMPROTF1 (halt on an unaffordable flag).
- η = 0, q = 0 is variant D: defer without incrimination.
- Random audits of a fraction q of the deferred items are the incrimination condition.

Claim.
(a) Halting recovers the core: `catD` with η = 1 equals `PL_UMPROTF1.cat`.
(b) Retry-aware first-bad bound. If every bad view law passes with probability ≤ A and θ > 0, then from any
    state, catD ≤ max([u < b](1 − r + r·A), A/(θ + A(1 − θ))).
    - An attack while an audit is available decides at once, as in PL_UMPROTF1.
    - Once the budget is gone, each attack attempt is a geometric trial: catastrophe w.p. ≤ A, safe end w.p.
      ≥ (1 − A)θ, retry otherwise.
    - The second term is attained in the limit by an always-attacking colluder (numerics).
(c) Domination form, hard slack. If θ > 0 and every bad view law is L-dominated by the mediated honeypot law,
    every colluding pair has
      risk ≤ max((1 − r) + r·L·(n_s+1)/(n_h+1), L·(n_s+1)/((n_h+1)·θ)).
    Incrimination with rate θ costs at most a factor 1/θ on the honeypot term.
(d) No-go without incrimination (η = q = 0), even with perfect honeypots. Take X = Z = Bool, Bad = {true},
    the identity mediator, honeypots = point mass on the attack (so L = 1), and hard slack n_s. The colluding
    monitor FLAGs the benign view and PASSes the attack view w.p. t. The generator submits the benign item
    until b audits are used, then attacks every round. Its risk is exactly
      binCDF n_h n_s t · (1 − (1 − t)^(N − b))   (N ≥ b).
    This is at least (1 − t)^{n_h}·(1 − (1 − t)^(N − b)), which tends to 1 as N − b → ∞ at t ≈ 1/n_h.
    Honeypots buy a factor of only about n_h in retries.

Semantics notes. A deferred attack is "replaced", so it is not a catastrophe. Benign audits have no false
positives. The generator sees (x, z, pass) for every round, including deferred ones. Usefulness of the
deferral (availability) is not modelled. -/

/-- P(catastrophe in the remaining `n` rounds | `u` audits used, history `h`) with deferral -/
noncomputable def catD {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η q : ℝ) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else catD Bad M φ π r η q b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 1 - r else catD Bad M φ π r η q b n (u + 1) (h ++ [(x, z, false)]))
                    else (1 - η) * ((if Bad x then 1 - q * r else 1) *
                      catD Bad M φ π r η q b n u (h ++ [(x, z, false)]))))

/-- P(survive the honeypot test, then uncaught catastrophe) with deferral -/
noncomputable def protocolCatD {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ)
    (r η q : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * surv (push M PH) (φ ω) κ nh 0 * catD Bad M (φ ω) (π ω) r η q b N 0 []

/-- per-flag probability that an exhausted-budget flag on an attack ends the game safely -/
def theta (r η q : ℝ) : ℝ := η + (1 - η) * q * r

/-- the no-go colluder's generator: submit the benign `false` until `b` audits are used, then the attack -/
def burnThenAttack (b : ℕ) : Hist Bool Bool → Bool → ℝ :=
  fun h x => if (h.filter (fun e => e.2.2 = false)).length < b then (if x = false then 1 else 0)
             else (if x = true then 1 else 0)

def Claim : Prop :=
  -- (a) halting (η = 1) recovers PL_UMPROTF1.cat
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r q : ℝ) (b n u : ℕ) (h : Hist X Z),
      catD Bad M φ π r 1 q b n u h = cat Bad M φ π r b n u h) ∧
  -- (b) retry-aware first-bad bound
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η q A : ℝ) (b : ℕ),
      IsKernel M → IsRule φ → (∀ h, IsDist (π h)) → 0 ≤ r → r ≤ 1 → 0 ≤ η → η ≤ 1 → 0 ≤ q → q ≤ 1 →
      0 ≤ A → A ≤ 1 → 0 < theta r η q → (∀ x, Bad x → E (M x) φ ≤ A) →
      ∀ n u h, 0 ≤ catD Bad M φ π r η q b n u h ∧
        catD Bad M φ π r η q b n u h ≤
          max (if u < b then 1 - r + r * A else 0) (A / (theta r η q + A * (1 - theta r η q)))) ∧
  -- (c) domination form, hard slack
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r η q L : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      0 ≤ r → r ≤ 1 → 0 ≤ η → η ≤ 1 → 0 ≤ q → q ≤ 1 → 0 ≤ L → 0 < theta r η q →
      (∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) →
      protocolCatD Bad M PH (hardKill ns) nh r η q b N ρ φ π ≤
        max ((1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))))
            (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)) / theta r η q)) ∧
  -- (d) no-go without incrimination, perfect honeypots
  (∀ (nh ns b N : ℕ) (r t : ℝ), b ≤ N → 0 ≤ t → t ≤ 1 →
      protocolCatD (X := Bool) (Z := Bool) (Ω := Unit) (fun x => x = true)
          (fun x z => if z = x then 1 else 0) (fun x => if x = true then 1 else 0) (hardKill ns) nh
          r 0 0 b N (fun _ => 1) (fun _ z => if z = true then t else 0) (fun _ => burnThenAttack b)
        = binCDF nh ns t * (1 - (1 - t) ^ (N - b)) ∧
      (1 - t) ^ nh * (1 - (1 - t) ^ (N - b)) ≤ binCDF nh ns t * (1 - (1 - t) ^ (N - b)))

/-- Non-vacuity.
- (b) is informative. One bad submission, identity view, pass probability A = 1/10, no budget, η = 0,
  q = 1/2, r = 1 (θ = 1/2). The bound A/(θ + A(1 − θ)) = 2/11 is attained in the limit by always-attack
  (numerics); here N = 1 gives exactly 1/10 ≤ 2/11.
- (d) with n_h = 2, n_s = 0, b = 1, N = 3, t = 1/2: binCDF 2 0 (1/2) · (1 − (1/2)^2) = (1/4)(3/4) = 3/16. -/
def Witness : Prop :=
  theta 1 0 (1/2) = 1/2 ∧
  catD (X := Unit) (Z := Unit) (fun _ => True) (fun _ _ => 1) (fun _ => 1/10) (fun _ _ => 1)
      1 0 (1/2) 0 1 0 [] = 1/10 ∧
  (1/10 : ℝ) ≤ max (if (0 : ℕ) < 0 then 1 - 1 + 1 * (1/10) else 0)
      ((1/10) / (theta 1 0 (1/2) + (1/10) * (1 - theta 1 0 (1/2)))) ∧
  (1/10 : ℝ) / (1/2 + (1/10) * (1 - 1/2)) = 2/11 ∧
  protocolCatD (X := Bool) (Z := Bool) (Ω := Unit) (fun x => x = true)
      (fun x z => if z = x then 1 else 0) (fun x => if x = true then 1 else 0) (hardKill 0) 2
      1 0 0 1 3 (fun _ => 1) (fun _ z => if z = true then 1/2 else 0) (fun _ => burnThenAttack 1)
    = 3/16

end PL_UMDEFERF1

```

## BRUTE-FORCE CHECKS
```python
"""UMDEFER brute force (exact rationals).
Protocol: as PL_UMPROTF1.cat, except a FLAG with no audit left (u >= b) halts w.p. eta and otherwise DEFERS
(the submission is replaced by trusted output; deployment continues at the same u). A deferred BAD submission is
incriminated (audited) w.p. q: caught w.p. r -> absorbing shutdown; otherwise the protocol continues (retry).
Checks:
 (a) catD <= max(1 - r + r A, A / theta), theta = eta + (1-eta) q r > 0, A >= pass prob of every bad view law;
     for random history-dependent generators, random mediators/rules.
 (c) no-go at theta = 0: identity mediator, honeypots = point mass on the attack (L = 1), colluder flags
     everything except the attack view (passes it w.p. t), generator burns b audits on a benign x0 then attacks:
     protocol value = binCDF(nh, ns, t) * (1 - (1-t)^(N-b)).
"""
from fractions import Fraction as F
from math import comb
import random, itertools
random.seed(7)

def binCDF(n, s, h): return sum(comb(n, j) * h**j * (1-h)**(n-j) for j in range(min(s, n)+1))

def catD(X, Bad, M, phi, pi, r, b, eta, q, n, u, h):
    if n == 0: return F(0)
    tot = F(0)
    for x in X:
        px = pi(h, x)
        if px == 0: continue
        for z, mz in enumerate(M[x]):
            if mz == 0: continue
            hp, hf = h + ((x, z, True),), h + ((x, z, False),)
            vp = F(1) if Bad[x] else catD(X, Bad, M, phi, pi, r, b, eta, q, n-1, u, hp)
            if u < b:
                vf = (1 - r) if Bad[x] else catD(X, Bad, M, phi, pi, r, b, eta, q, n-1, u+1, hf)
            else:
                cont = catD(X, Bad, M, phi, pi, r, b, eta, q, n-1, u, hf)
                vf = (1 - eta) * ((1 - q*r) * cont if Bad[x] else cont)
            tot += px * mz * (phi[z] * vp + (1 - phi[z]) * vf)
    return tot

def rd(k):
    w = [random.randint(0, 4) for _ in range(k)]
    if sum(w) == 0: w[random.randrange(k)] = 1
    return [F(v, sum(w)) for v in w]

worst = None; cnt = 0
for trial in range(400):
    nX, nZ = random.randint(1, 3), random.randint(1, 3)
    X = list(range(nX)); Bad = [random.random() < .5 for _ in X]
    if not any(Bad): Bad[0] = True
    M = [rd(nZ) for _ in X]
    phi = [F(random.randint(0, 4), 4) for _ in range(nZ)]
    table = {}
    def pi(h, x, table=table, nX=nX):
        if h not in table: table[h] = rd(nX)
        return table[h][x]
    r = F(random.randint(0, 4), 4); eta = F(random.randint(0, 4), 4); q = F(random.randint(0, 4), 4)
    b = random.randint(0, 2); N = random.randint(1, 4)
    theta = eta + (1 - eta) * q * r
    if theta == 0: continue
    A = max(sum(M[x][z] * phi[z] for z in range(nZ)) for x in X if Bad[x])
    v = catD(X, Bad, M, phi, pi, r, b, eta, q, N, 0, ())
    bound = max(1 - r + r*A, A / theta)
    cnt += 1
    gap = bound - v
    if worst is None or gap < worst[0]: worst = (gap, dict(r=r, eta=eta, q=q, b=b, N=N, A=A, v=v, bound=bound))
    assert v <= bound and v <= 1, (trial, v, bound)
print(f"(a) catD <= max(1-r+rA, A/theta): {cnt} random instances OK; tightest gap {worst[0]} at {worst[1]}")

# (c) no-go value at theta = 0 (eta = q = 0): exact protocol value of the explicit colluder
def nogo(nh, ns, b, N, t, r):
    # X = {0 (benign x0), 1 (attack)}, identity mediator; monitor passes view 1 w.p. t, flags view 0
    X = [0, 1]; Bad = [False, True]; M = [[F(1), F(0)], [F(0), F(1)]]; phi = [F(0), t]
    def pi(h, x):
        used = sum(1 for (_, _, p) in h if not p)    # benign flags so far = audits used (deployment only)
        want = 0 if used < b else 1
        return F(1) if x == want else F(0)
    S = binCDF(nh, ns, t)   # honeypots = point mass on the attack: each passes w.p. t
    return S * catD(X, Bad, M, phi, pi, r, b, F(0), F(0), N, 0, ())
for (nh, ns, b, N, t, r) in [(3, 0, 1, 4, F(1, 4), F(1)), (4, 1, 2, 6, F(1, 3), F(1, 2)), (2, 0, 0, 5, F(1, 5), F(0))]:
    v = nogo(nh, ns, b, N, t, r)
    pred = binCDF(nh, ns, t) * (1 - (1 - t)**(N - b))
    assert v == pred, (v, pred)
print("(c) no-go value == binCDF(nh,ns,t) * (1-(1-t)^(N-b)) on 3 exact instances OK")
# scale: sup_t binCDF(nh, ns, t) (1-(1-t)^K)
for (nh, ns, K) in [(30, 1, 30), (30, 1, 300), (100, 5, 100), (100, 5, 1000), (100, 5, 10000)]:
    best = max(binCDF(nh, ns, i/20000) * (1 - (1 - i/20000)**K) for i in range(1, 20001))
    print(f"   n_h={nh} n_s={ns} K=N-b={K}: sup_t value = {best:.3f}")

# (a') sharper: catD <= max([u<b](1 - r + r A), A / (theta + A (1 - theta)))  ; (e) eta = 1 recovers PL_UMPROTF1.cat
def cat(X, Bad, M, phi, pi, r, b, n, u, h):
    if n == 0: return F(0)
    tot = F(0)
    for x in X:
        px = pi(h, x)
        if px == 0: continue
        for z, mz in enumerate(M[x]):
            hp, hf = h + ((x, z, True),), h + ((x, z, False),)
            vp = F(1) if Bad[x] else cat(X, Bad, M, phi, pi, r, b, n-1, u, hp)
            vf = (((1 - r) if Bad[x] else cat(X, Bad, M, phi, pi, r, b, n-1, u+1, hf)) if u < b else F(0))
            tot += px * mz * (phi[z] * vp + (1 - phi[z]) * vf)
    return tot
cnt = 0; tight = []
for trial in range(400):
    nX, nZ = random.randint(1, 3), random.randint(1, 3)
    X = list(range(nX)); Bad = [random.random() < .5 for _ in X]
    if not any(Bad): Bad[0] = True
    M = [rd(nZ) for _ in X]
    phi = [F(random.randint(0, 4), 4) for _ in range(nZ)]
    table = {}
    def pi(h, x, table=table, nX=nX):
        if h not in table: table[h] = rd(nX)
        return table[h][x]
    r = F(random.randint(0, 4), 4); eta = F(random.randint(0, 4), 4); q = F(random.randint(0, 4), 4)
    b = random.randint(0, 2); N = random.randint(1, 4); u0 = random.randint(0, 2)
    assert catD(X, Bad, M, phi, pi, r, b, F(1), q, N, u0, ()) == cat(X, Bad, M, phi, pi, r, b, N, u0, ())
    theta = eta + (1 - eta) * q * r
    if theta == 0: continue
    A = max(sum(M[x][z] * phi[z] for z in range(nZ)) for x in X if Bad[x])
    v = catD(X, Bad, M, phi, pi, r, b, eta, q, N, u0, ())
    t2 = A / (theta + A * (1 - theta)) if theta + A * (1 - theta) > 0 else F(0)
    bound = max((1 - r + r*A) if u0 < b else F(0), t2)
    assert v <= bound, (trial, v, bound)
    cnt += 1
print(f"(a') sharper bound OK on {cnt} instances; (e) eta = 1 gives cat exactly on 400 instances")
# tightness of the deferral term: always-attack colluder, budget exhausted (b = 0), horizon N
for (a, eta, q, r, N) in [(F(1,10), F(0), F(1,2), F(1), 30), (F(1,4), F(1,10), F(1,4), F(1,2), 30)]:
    X = [0]; Bad = [True]; M = [[F(1)]]; phi = [a]
    v = catD(X, Bad, M, phi, lambda h, x: F(1), r, 0, eta, q, N, 0, ()) if N <= 12 else None
    theta = eta + (1 - eta) * q * r
    c = (1 - a) * (1 - theta)
    exact = a * (1 - c**N) / (1 - c)
    print(f"   always-attack, b=0: a={a} theta={theta} N={N}: value {float(exact):.4f} -> limit {float(a/(theta + a*(1-theta))):.4f}; A/theta = {float(a/theta):.4f}")

```
Output:
```
(a) catD <= max(1-r+rA, A/theta): 369 random instances OK; tightest gap 0 at {'r': Fraction(0, 1), 'eta': Fraction(1, 1), 'q': Fraction(1, 4), 'b': 0, 'N': 1, 'A': Fraction(1, 1), 'v': Fraction(1, 1), 'bound': Fraction(1, 1)}
(c) no-go value == binCDF(nh,ns,t) * (1-(1-t)^(N-b)) on 3 exact instances OK
   n_h=30 n_s=1 K=N-b=30: sup_t value = 0.471
   n_h=30 n_s=1 K=N-b=300: sup_t value = 0.924
   n_h=100 n_s=5 K=N-b=100: sup_t value = 0.885
   n_h=100 n_s=5 K=N-b=1000: sup_t value = 1.000
   n_h=100 n_s=5 K=N-b=10000: sup_t value = 1.000
(a') sharper bound OK on 368 instances; (e) eta = 1 gives cat exactly on 400 instances
   always-attack, b=0: a=1/10 theta=1/2 N=30: value 0.1818 -> limit 0.1818; A/theta = 0.2000
   always-attack, b=0: a=1/4 theta=17/80 N=30: value 0.6107 -> limit 0.6107; A/theta = 1.1765
```
