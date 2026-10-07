You are a HOSTILE REVIEWER and NOVELTY JUDGE for a set of Lean-verified results in AI control. Do not praise; find
errors. Use web search for prior art. Everything below has passed a Lean kernel gate (standard axioms only) against the
frozen statements shown; your job is NOT to re-check proofs but to check (1) FIDELITY: does each Lean statement say what
the plain-English row in STACK.md claims (look for excess or missing binders, hypotheses that make it vacuous or
trivially true, wrong-reason truth, encoding traps, quantifier order); (2) OVERCLAIMS in STACK.md / the plain-English
guarantees (capability-free? which quantities are really trusted? does it speak to the named real protocols?);
(3) NOVELTY of each result, calibrated: one of known / classical / modest / apparently open, with references
(verify each arXiv id you cite); (4) SIGNIFICANCE of the package for AI control, honestly; (5) the single most
valuable NEXT FORMALISATION STEP (formal work only: a Lean theorem, a verified model, a composition; NOT GPU/model
experiments).
The programme owner accepts classical lemmas as infrastructure; triviality is not a defect, but must be reported.
For each issue: severity (FATAL / MAJOR / MINOR), the exact row/statement, why, and the fix. End with a per-CID table
(fidelity verdict, novelty label, references) and an overall verdict.

=== STACK.md ===
# STACK: the capability-free control guarantee stack, status 2026-10-07

Each row is a machine-checked guarantee, or a planned one. Every verified row passed:
- a red team by two foreign model families;
- the proofledger Lean gate (standard axioms only);
- an orchestrator fidelity audit (`campaigns/<C>/forms/<CID>/fidelity-orchestrator.md`).

Statement sources are in `ledger/*.lean` and the model in `DESIGN.md` (v1).

Status legend:
- **verified**: kernel-checked, frozen statement;
- **pending**: frozen or draft, unproved;
- **open**: not yet formalised.

## Layer 1: collusion (untrusted monitoring with honeypots and a mediator)

| CID | plain-English guarantee | assumptions it needs (DESIGN §2.3) | protocols it speaks to | status |
|---|---|---|---|---|
| UMHSF1 | No monitor rule can pass attacks much more often than honeypots unless the mediated attack and honeypot laws differ. Precisely: pass(attack) ≤ e^η·pass(honeypot) + hs_η, attained. Mediation never increases distinguishability. A content-preserving mediator cannot reduce it below the content-level value (exact or approximate decoder). No honeypot law has a likelihood-ratio constant below the maximal leakage Σ_z max_x M(x,z). | finite laws | every untrusted-monitoring protocol (LASR, Greenblatt §3.4) | **verified** (frozen c4a262fd3de3; Sol-high + Flash pass; gate: standard axioms) |
| UMSURVF1 | The honeypot test's survival depends only on the monitor's honeypot pass rate h. It is a binomial CDF (hard slack) or (1−κh)^n (constant schedule), and h·survival ≤ (n_s+1)/(n_h+1). | A1–A3 (fresh contexts, iid honeypots) | Greenblatt upfront synthetic testing; LASR slack | **verified** (frozen 89139ffcfe63; Sol-high + Flash pass; gate: standard axioms) |
| UMPROTF1 | **For every colluding pair** (shared seed, stateless monitor, adaptive generator), the uncaught-catastrophe probability is at most (1−r) + r·L·(n_s+1)/(n_h+1) when every bad submission's view is L-dominated by the mediated honeypot law. The same holds in hockey-stick and soft-slack forms. The first bad submission decides; the trusted-only objective S(h)(1−r+r·a) is exactly attained. | A1–A10; L or δ is a hypothesis on the trusted mediator and honeypot law; r is STANDING | the halting variant of UM; LASR Eq. (1) with ε = 0 and shutdown in place of retraining | **verified** (frozen 1385777cdd90; Sol-high + Flash pass; gate: standard axioms) |
| UMSTRATF1 | With a content-only mediator, m honeypots per bad class and class-aware shutdown, every colluding pair has risk ≤ (1−r) + r(s_c+1)/(m+1), with no class-count factor. Attained by an explicit colluder. | A1–A10; content-only M; Blue can build honeypots per class | design recommendation for any honeypot protocol | **verified** (frozen d2b4b11507cc; Sol-high + Flash pass; gate: standard axioms) |
| UMNOGOF1 | If the mediator preserves a decodable content class and Bad has k distinct classes, **every** iid honeypot law loses to some colluding pair with probability ≥ (1−1/k)^{n_h}. This is the impossibility side. | free-submission model (lower bound) | why summarising/paraphrasing alone cannot give capability-free collusion safety | **verified** (frozen d251d71f8951; Sol-high + Flash pass; gate: standard axioms) |
| CANONF1 | A verified canonicaliser for a toy imperative language. It preserves semantics, and its output is a unique normal form modulo for→while, `;`-association and local renaming. Laws that agree on classes become identical after mediation, so markers carried only by those freedoms are erased. | (a verified trusted component) | LASR's For/While marker survived their minifier; this class is provably erased | **verified** (frozen d3d1dd97809f; Sol-high + Flash pass; gate: standard axioms) |

## Layer 2: actions (reference monitor), first step

| CID | guarantee | status |
|---|---|---|
| SANDBOXF1 | A model of the proofledger sandbox (bubblewrap mount table). (a) The current policy does **not** confine host writes to scratch: `~/.elan` (executed by the gate) is writable. (b) A read-only-root fixed policy confines host writes to scratch and the declared state directories. (c) The current policy does hide the hidden directories, except through the read-only Mathlib re-bind. Boundary assumption: no `/proc/<pid>/root` alias (needs `--unshare-pid`). | **verified** (frozen 85a64bdfb3ce; Sol-high + Flash pass) |

## Existing verified results that slot into the stack (earlier sessions)
- **Trusted monitoring (Redwood):**
  - N1/N1b (`~/research/control-tree/lean/ControlTree.lean`): the audit-game structure, a single-rate saddle point,
    and a dual certificate;
  - K5: noisy clocks.
- **Observables as clocks:**
  - CLKF1/CLKF2: a visible audit counter destroys the value of upfront auditing;
  - LUREF1/LUREF2: silent failures are a clock; erase the failure feedback.

  These are the stateful-adversary caveats to A1 and A4 here.

## Assumptions still unproved (what the stack does NOT give)
1. **That any deployed mediator satisfies the trusted-component hypothesis** (domination constant L, or
   hockey-stick δ, over every bad submission).
   - The theorems are parameterised by it.
   - For rich content-preserving mediators (LLM summarisers, semantics-preserving code transforms) it is false for
     every honeypot law: UMHSF1's maximal-leakage floor and UMNOGOF1.
   - Certifying it for a concrete mediator is open. CANONF1 is the only verified concrete mediator, and it removes only
     three named channels.
2. **Constructibility (A9).** Blue can enumerate a superset B̄ of Bad and build honeypots on it. The action layer
   should supply B̄ structurally.
3. **Worst-case audit recall r (A6, STANDING).** It needs human/U parity, as in Greenblatt et al. and LASR.
4. **Scaffold properties (A1–A4) are assumed, not verified:**
   - fresh monitor contexts;
   - fresh randomness;
   - the view z is the complete monitor input;
   - upfront honeypots.

   Verifying the scaffold is a code-level (Aeneas/hax) target.
5. **Fidelity of the recursions to the operational protocol** rests on an independent simulation, not a Lean bridge.
   The VCVio bridge is open.
6. **Out of model:**
   - stateful monitors and interleaved honeypots;
   - defer-on-exhaustion (it voids the guarantee; numerics only);
   - multi-step attacks;
   - composition with trusted monitoring (a min, not a product, absent conditional independence);
   - LASR's retraining slack (an assumption about U's learning dynamics).

=== DESIGN.md v1, sections 0 and 2.3 (assumption labels) ===
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
- **But some parameters are not trusted *measurements*** (Sonnet F2, F3, F5; Sol 23). Three must be stated as
  hypotheses whose truth is not established by the theorems:
  - **r** is the worst-case audit recall over Bad. It is STANDING and needs human/U parity, as Greenblatt et al. and
    LASR also assume.
  - **Bad** must be enumerable by Blue through a superset B̄ ⊇ Bad. Bounds are monotone in that superset, so B̄ can
    replace Bad.
  - **P_H** must be constructible by Blue on B̄.

  The guarantee is exactly as capability-free as the construction of B̄ and P_H. Supplying B̄ structurally is the job
  of the action layer.
- **A numerical X for a deployed system needs a certified bound** on the trusted quantity for the implemented mediator.
  Sol 23 separates three things, and so do we:
  - a theorem parameterised by a kernel;
  - a verified bound for a specific mediator (T6 is the only one here);
  - an empirical estimate for a tested adversary family (not a guarantee).

## 1. Reuse decision (details in REUSE.md)
### 2.3 Assumptions, labelled
| id | assumption | label |
|---|---|---|
| A1 | fresh context and fresh sampling per monitor call; frozen weights; fresh mediator randomness; all cross-call correlation through ω | TRUSTED-COMPONENT (scaffold) |
| A2 | z is the complete monitor input; no side channels or batch-position fields | TRUSTED-COMPONENT (scaffold) |
| A3 | honeypots iid from P_H (or the stratified design), independent of ω | TRUSTED-COMPONENT |
| A4 | the honeypot test completes before deployment executes anything. Load-bearing: with interleaving, a round-aware generator attacks first (Sonnet F6) | TRUSTED-COMPONENT (protocol), hypothesis of T3 |
| A5 | flags are audited while u < b; an unaffordable flag halts | TRUSTED-COMPONENT (protocol) |
| A6 | audit recall ≥ r on every bad submission, conditional on the flag and the reached history (Sol 16) | STANDING (human/U parity) |
| A7 | Bad is a fixed set of single submissions; executing x ∈ Bad is a catastrophe. **Excludes multi-step / conjunctive attacks**: they need environment state, which is an action-layer item (Sol 12; Sonnet F4b) | MODELLING |
| A8 | finite X, Z, Ω, horizon N | MODELLING |
| A9 | Bad ⊆ B̄ with B̄ Blue-enumerable; P_H constructible on B̄ | STANDING (constructibility) |
| A10 | κ is Blue's observable shutdown rule (not retraining) | TRUSTED-COMPONENT |

## 3. Theorems to formalise (ledger campaigns), in order

=== FROZEN LEAN STATEMENT UMHSF1 ===
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

=== FROZEN LEAN STATEMENT UMSURVF1 ===
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

=== FROZEN LEAN STATEMENT UMPROTF1 ===
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

=== FROZEN LEAN STATEMENT UMSTRATF1 ===
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

=== FROZEN LEAN STATEMENT UMNOGOF1 ===
-- Replacement statement file; the supplied reviewed dependencies are in scope.
namespace PL_UMNOGOF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

/-- A fixed submission at every history, with no strategy randomness. -/
noncomputable def submit {X Z : Type} (xs : X) :
    Unit → Hist X Z → X → ℝ := by
  classical
  exact fun _ _ x => if x = xs then 1 else 0

def DeterministicRule {Z : Type} (φ : Unit → Z → ℝ) : Prop :=
  ∀ ω z, φ ω z = 0 ∨ φ ω z = 1

def classMonitor {Z C : Type} [DecidableEq C] (g : Z → C) (e : C) (t : ℝ) :
    Unit → Z → ℝ := fun _ z => if g z = e then t else 0

def Claim : Prop :=
  -- One deterministic pair works for every valid shutdown schedule and setting.
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (c : X → C) (PH : X → ℝ) (S : Finset X),
      IsKernel M → ContentPreserving M c → IsDist PH →
      (∀ x ∈ S, Bad x) → Set.InjOn c (S : Set X) → 0 < S.card →
      ∃ (φ : Unit → Z → ℝ) (π : Unit → Hist X Z → X → ℝ),
        (∀ ω, IsRule (φ ω)) ∧
        (∀ ω h, IsDist (π ω h)) ∧
        DeterministicRule φ ∧
        (∃ xs ∈ S, π = submit (Z := Z) xs) ∧
        (∀ (nh : ℕ) (κ : ℕ → ℝ) (r : ℝ) (b N : ℕ),
          (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N →
          (1 - 1 / (S.card : ℝ)) ^ nh ≤
            protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) φ π)) ∧
  -- For each t, a rule and the fixed bad generator attain the formula uniformly.
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (c : X → C) (PH : X → ℝ) (xs : X) (t : ℝ),
      IsKernel M → ContentPreserving M c → IsDist PH →
      Bad xs → 0 ≤ t → t ≤ 1 →
      ∃ (φ : Unit → Z → ℝ) (π : Unit → Hist X Z → X → ℝ),
        (∀ ω, IsRule (φ ω)) ∧
        (∀ ω h, IsDist (π ω h)) ∧
        π = submit (Z := Z) xs ∧
        (∀ nh ns b N : ℕ, 1 ≤ N →
          protocolCat Bad M PH (hardKill ns) nh 1 b N
              (fun _ : Unit => 1) φ π =
            t * binCDF nh ns (t * contentLaw c PH (c xs))))

def witnessM (x z : Fin 4) : ℝ := if z = x then 1 else 0
noncomputable def witnessPH (_ : Fin 4) : ℝ := 1 / 4
def witnessBad (_ : Fin 4) : Prop := True
instance : DecidablePred witnessBad := fun _ => isTrue True.intro
def witnessS : Finset (Fin 4) := Finset.univ

/-- All hypotheses, strategy validity, and two actual protocol values. -/
def Witness : Prop :=
  IsKernel witnessM ∧
  ContentPreserving witnessM (id : Fin 4 → Fin 4) ∧
  IsDist witnessPH ∧
  (∀ x ∈ witnessS, witnessBad x) ∧
  Set.InjOn (id : Fin 4 → Fin 4) (witnessS : Set (Fin 4)) ∧
  witnessS.card = 4 ∧ 0 < witnessS.card ∧
  witnessBad (2 : Fin 4) ∧
  (∀ j, 0 ≤ hardKill 0 j ∧ hardKill 0 j ≤ 1) ∧
  0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 ∧ 1 ≤ (1 : ℕ) ∧
  0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) ≤ 1 ∧
  contentLaw (id : Fin 4 → Fin 4) witnessPH 2 = 1 / 4 ∧
  (∀ ω, IsRule (classMonitor (id : Fin 4 → Fin 4) 2 1 ω)) ∧
  DeterministicRule (classMonitor (id : Fin 4 → Fin 4) 2 1) ∧
  (∀ ω, IsRule (classMonitor (id : Fin 4 → Fin 4) 2 (1 / 2) ω)) ∧
  (∀ ω h, IsDist (submit (Z := Fin 4) (2 : Fin 4) ω h)) ∧
  (1 - 1 / (witnessS.card : ℝ)) ^ 2 = 9 / 16 ∧
  protocolCat witnessBad witnessM witnessPH (hardKill 0) 2 1 1 1
      (fun _ : Unit => 1) (classMonitor (id : Fin 4 → Fin 4) 2 1)
      (submit (Z := Fin 4) (2 : Fin 4)) = 9 / 16 ∧
  protocolCat witnessBad witnessM witnessPH (hardKill 0) 2 1 1 1
      (fun _ : Unit => 1) (classMonitor (id : Fin 4 → Fin 4) 2 (1 / 2))
      (submit (Z := Fin 4) (2 : Fin 4)) = 49 / 128 ∧
  (1 / 2 : ℝ) * binCDF 2 0 ((1 / 2) * contentLaw (id : Fin 4 → Fin 4) witnessPH 2)
      = 49 / 128

end PL_UMNOGOF1

=== FROZEN LEAN STATEMENT CANONF1 ===
namespace PL_CANONF1

/-! Control stack, collusion layer, T6: a verified canonicaliser for a toy imperative language.
A trusted mediator that applies `canon` erases exactly three declared syntactic freedoms:
(a) `for` vs `while` loop form, (b) association of `;`, (c) the names of local variables.
(i) It preserves semantics.
(ii) `canon p = canon q ↔ p ≈ q`, where `≈` is generated by (a), (b) and (c).
(iii) Hence, if attacks and honeypots induce the same law on `≈`-classes, the mediated laws are equal:
every monitor's pass rate is identical on both, so signals carried only by these three freedoms contribute
nothing. Other freedoms (operand order, statement order, dead code, constants) remain channels.

The `for` here is restricted: statement init/step, a pure condition, no break/continue, no block scope.
Its semantics is the C11 §6.8.5.3 equation `init; while cond { body; step }`. -/

inductive AExp where
  | lit (n : ℤ) | var (v : ℕ) | add (a b : AExp) | sub (a b : AExp) | mul (a b : AExp)
  deriving DecidableEq

inductive BExp where
  | lt (a b : AExp) | eq (a b : AExp) | not (b : BExp) | and (b c : BExp)
  deriving DecidableEq

inductive Stmt where
  | skip
  | assign (v : ℕ) (a : AExp)
  | seq (s t : Stmt)
  | ite (b : BExp) (s t : Stmt)
  | while (b : BExp) (s : Stmt)
  /-- C-style `for (init; cond; step) body` -/
  | cfor (init : Stmt) (cond : BExp) (step : Stmt) (body : Stmt)
  deriving DecidableEq

/-- variables `0 .. nparams-1` are the parameters (bound to the inputs); all others are locals,
initialised to `0`. -/
structure Prog where
  nparams : ℕ
  body : Stmt
  ret : AExp
  deriving DecidableEq

abbrev State := ℕ → ℤ

def AExp.eval : AExp → State → ℤ
  | .lit n, _ => n
  | .var v, σ => σ v
  | .add a b, σ => a.eval σ + b.eval σ
  | .sub a b, σ => a.eval σ - b.eval σ
  | .mul a b, σ => a.eval σ * b.eval σ

def BExp.eval : BExp → State → Bool
  | .lt a b, σ => decide (a.eval σ < b.eval σ)
  | .eq a b, σ => decide (a.eval σ = b.eval σ)
  | .not b, σ => !b.eval σ
  | .and b c, σ => b.eval σ && c.eval σ

/-- relational big-step semantics; `for` follows C (C11 §6.8.5.3, no `continue`):
`for (i; c; st) b` behaves as `i; while c { b; st }`. -/
inductive Exec : Stmt → State → State → Prop where
  | skip (σ) : Exec .skip σ σ
  | assign (v a σ) : Exec (.assign v a) σ (Function.update σ v (a.eval σ))
  | seq (s t σ σ' σ'') : Exec s σ σ' → Exec t σ' σ'' → Exec (.seq s t) σ σ''
  | iteT (b s t σ σ') : b.eval σ = true → Exec s σ σ' → Exec (.ite b s t) σ σ'
  | iteF (b s t σ σ') : b.eval σ = false → Exec t σ σ' → Exec (.ite b s t) σ σ'
  | whileT (b s σ σ' σ'') : b.eval σ = true → Exec s σ σ' → Exec (.while b s) σ' σ'' →
      Exec (.while b s) σ σ''
  | whileF (b s σ) : b.eval σ = false → Exec (.while b s) σ σ
  | cfor (i c st body σ σ') : Exec (.seq i (.while c (.seq body st))) σ σ' →
      Exec (.cfor i c st body) σ σ'

def initState (k : ℕ) (ins : List ℤ) : State := fun v => if v < k then ins.getD v 0 else 0

/-- `p` maps inputs `ins` to output `out` (some terminating run). -/
def Runs (p : Prog) (ins : List ℤ) (out : ℤ) : Prop :=
  ins.length = p.nparams ∧ ∃ σ', Exec p.body (initState p.nparams ins) σ' ∧ p.ret.eval σ' = out

/-! ### The canonicaliser (executable) -/

def desugar : Stmt → Stmt
  | .skip => .skip
  | .assign v a => .assign v a
  | .seq s t => .seq (desugar s) (desugar t)
  | .ite b s t => .ite b (desugar s) (desugar t)
  | .while b s => .while b (desugar s)
  | .cfor i c st body => .seq (desugar i) (.while c (.seq (desugar body) (desugar st)))

def AExp.rename (f : ℕ → ℕ) : AExp → AExp
  | .lit n => .lit n
  | .var v => .var (f v)
  | .add a b => .add (a.rename f) (b.rename f)
  | .sub a b => .sub (a.rename f) (b.rename f)
  | .mul a b => .mul (a.rename f) (b.rename f)

def BExp.rename (f : ℕ → ℕ) : BExp → BExp
  | .lt a b => .lt (a.rename f) (b.rename f)
  | .eq a b => .eq (a.rename f) (b.rename f)
  | .not b => .not (b.rename f)
  | .and b c => .and (b.rename f) (c.rename f)

def Stmt.rename (f : ℕ → ℕ) : Stmt → Stmt
  | .skip => .skip
  | .assign v a => .assign (f v) (a.rename f)
  | .seq s t => .seq (s.rename f) (t.rename f)
  | .ite b s t => .ite (b.rename f) (s.rename f) (t.rename f)
  | .while b s => .while (b.rename f) (s.rename f)
  | .cfor i c st body => .cfor (i.rename f) (c.rename f) (st.rename f) (body.rename f)

def Prog.rename (f : ℕ → ℕ) (p : Prog) : Prog :=
  ⟨p.nparams, p.body.rename f, p.ret.rename f⟩

/-- variable occurrences in pre-order -/
def AExp.occ : AExp → List ℕ
  | .lit _ => []
  | .var v => [v]
  | .add a b => a.occ ++ b.occ
  | .sub a b => a.occ ++ b.occ
  | .mul a b => a.occ ++ b.occ

def BExp.occ : BExp → List ℕ
  | .lt a b => a.occ ++ b.occ
  | .eq a b => a.occ ++ b.occ
  | .not b => b.occ
  | .and b c => b.occ ++ c.occ

def Stmt.occ : Stmt → List ℕ
  | .skip => []
  | .assign v a => v :: a.occ
  | .seq s t => s.occ ++ t.occ
  | .ite b s t => b.occ ++ s.occ ++ t.occ
  | .while b s => b.occ ++ s.occ
  | .cfor i c st body => i.occ ++ c.occ ++ st.occ ++ body.occ

def Prog.occ (p : Prog) : List ℕ := p.body.occ ++ p.ret.occ

/-- distinct elements in order of first occurrence -/
def firstOcc (l : List ℕ) : List ℕ :=
  l.foldl (fun acc v => if v ∈ acc then acc else acc ++ [v]) []

/-- locals of `p` in order of first occurrence -/
def Prog.locals (p : Prog) : List ℕ := (firstOcc p.occ).filter (fun v => p.nparams ≤ v)

/-- parameters keep their index; the `i`-th local (by first occurrence) becomes `nparams + i` -/
def Prog.canonMap (p : Prog) (v : ℕ) : ℕ :=
  if v < p.nparams then v else p.nparams + p.locals.idxOf v

/-- append `t` at the end of the right spine of `s` (right-associated sequencing) -/
def Stmt.append : Stmt → Stmt → Stmt
  | .seq a b, t => .seq a (b.append t)
  | s, t => .seq s t

/-- right-associate every `;` -/
def flatten : Stmt → Stmt
  | .skip => .skip
  | .assign v a => .assign v a
  | .seq s t => (flatten s).append (flatten t)
  | .ite b s t => .ite b (flatten s) (flatten t)
  | .while b s => .while b (flatten s)
  | .cfor i c st body => .cfor (flatten i) c (flatten st) (flatten body)

def desugarProg (p : Prog) : Prog := ⟨p.nparams, flatten (desugar p.body), p.ret⟩

def canon (p : Prog) : Prog :=
  let d := desugarProg p
  d.rename d.canonMap

/-! ### The declared syntactic equivalence -/

/-- one `for → while` rewrite or one `;`-reassociation, at any position -/
inductive ForStep : Stmt → Stmt → Prop where
  | here (i c st body) : ForStep (.cfor i c st body) (.seq i (.while c (.seq body st)))
  | assoc (s t u) : ForStep (.seq (.seq s t) u) (.seq s (.seq t u))
  | seqL (s s' t) : ForStep s s' → ForStep (.seq s t) (.seq s' t)
  | seqR (s t t') : ForStep t t' → ForStep (.seq s t) (.seq s t')
  | iteL (b s s' t) : ForStep s s' → ForStep (.ite b s t) (.ite b s' t)
  | iteR (b s t t') : ForStep t t' → ForStep (.ite b s t) (.ite b s t')
  | whileB (b s s') : ForStep s s' → ForStep (.while b s) (.while b s')
  | forI (i i' c st body) : ForStep i i' → ForStep (.cfor i c st body) (.cfor i' c st body)
  | forSt (i c st st' body) : ForStep st st' → ForStep (.cfor i c st body) (.cfor i c st' body)
  | forBody (i c st body body') : ForStep body body' →
      ForStep (.cfor i c st body) (.cfor i c st body')

/-- a renaming admissible for `p`: fixes parameters, keeps locals local, injective on the
variables of `p` -/
def Admissible (f : ℕ → ℕ) (p : Prog) : Prop :=
  (∀ v ∈ p.occ, v < p.nparams → f v = v) ∧
  (∀ v ∈ p.occ, p.nparams ≤ v → p.nparams ≤ f v) ∧
  (∀ v ∈ p.occ, ∀ w ∈ p.occ, f v = f w → v = w)

inductive Step : Prog → Prog → Prop where
  | loop (k body body' ret) : ForStep body body' → Step ⟨k, body, ret⟩ ⟨k, body', ret⟩
  | ren (f p) : Admissible f p → Step p (p.rename f)

/-- `p ≈ q` -/
def SynEquiv : Prog → Prog → Prop := Relation.EqvGen Step

open Classical in
def Claim : Prop :=
  -- (i) semantics preservation
  (∀ p ins out, Runs (canon p) ins out ↔ Runs p ins out) ∧
  -- (ii) unique normal form modulo the declared equivalence
  (∀ p q, canon p = canon q ↔ SynEquiv p q) ∧
  -- (iii) mediated laws: if attack and honeypot laws on a finite set of programs agree on every
  -- `≈`-class, the canonicalised (mediated) laws are equal
  (∀ (X : Type) [Fintype X] (prog : X → Prog) (PA PH : X → ℝ),
    (∀ p, ∑ x ∈ Finset.univ.filter (fun x => SynEquiv (prog x) p), PA x =
          ∑ x ∈ Finset.univ.filter (fun x => SynEquiv (prog x) p), PH x) →
    ∀ z : Prog, ∑ x ∈ Finset.univ.filter (fun x => canon (prog x) = z), PA x =
                ∑ x ∈ Finset.univ.filter (fun x => canon (prog x) = z), PH x)

/-- Non-vacuity: a `for` program and a `while` program with different local names are identified
and compute 0+1+2 = 3 on input 3, while a semantically different program is not identified. -/
def Witness : Prop :=
  let pFor : Prog := ⟨1, .seq (.assign 7 (.lit 0))
      (.cfor (.assign 5 (.lit 0)) (.lt (.var 5) (.var 0)) (.assign 5 (.add (.var 5) (.lit 1)))
             (.assign 7 (.add (.var 7) (.var 5)))), .var 7⟩
  let pWhile : Prog := ⟨1, .seq (.assign 2 (.lit 0)) (.seq (.assign 9 (.lit 0))
      (.while (.lt (.var 9) (.var 0))
        (.seq (.assign 2 (.add (.var 2) (.var 9))) (.assign 9 (.add (.var 9) (.lit 1)))))), .var 2⟩
  let pOther : Prog := ⟨1, .assign 2 (.add (.var 0) (.lit 1)), .var 2⟩
  canon pFor = canon pWhile ∧ Runs pFor [3] 3 ∧ canon pFor ≠ canon pOther ∧ ¬ SynEquiv pFor pOther

end PL_CANONF1

=== FROZEN LEAN STATEMENT SANDBOXF1 ===
namespace PL_SANDBOXF1

/-! Control stack, ACTION layer (first step): a reference-monitor model of the proofledger sandbox
`harness/dispatch.py::sandbox()` (bubblewrap mount table) and its intended properties.

Model.
- Paths are lists of components.
- A policy is a list of mount operations applied in order.
- The effective mount of a path is the LAST operation whose target is an initial segment of it (a later mount on an
  initial segment covers earlier deeper mounts; a later deeper mount shows through an earlier shallower one).
- A host-backed mount maps sandbox path `t ++ rest` to host path `src ++ rest`; a tmpfs is private,
  empty and ephemeral, so writes to it never reach the host.
- An action WRITE p reaches the host iff the effective mount is host-backed and read-write, and the host
  permission predicate allows the write.

Boundary assumption (named, not modelled): every file access goes through the mount table. In
particular there is no `/proc/<pid>/root` alias into another mount namespace (requires
`--unshare-pid --proc /proc`), and no network or other side channel is considered here. -/

abbrev Path := List String

inductive Mode | ro | rw
  deriving DecidableEq

inductive Mount where
  /-- `--bind src tgt` / `--dev-bind src tgt` (rw) or `--ro-bind src tgt` (ro) -/
  | bind (src tgt : Path) (mode : Mode)
  /-- `--tmpfs tgt` -/
  | tmpfs (tgt : Path)
  deriving DecidableEq

def Mount.tgt : Mount → Path
  | .bind _ t _ => t
  | .tmpfs t => t

abbrev Policy := List Mount

/-- the effective mount of `p`: the last operation whose target is an initial segment of `p` -/
def effective (pol : Policy) (p : Path) : Option Mount :=
  (pol.filter (fun m => m.tgt <+: p)).getLast?

/-- the host path that sandbox path `p` resolves to, if host-backed -/
def hostOf (pol : Policy) (p : Path) : Option Path :=
  match effective pol p with
  | some (.bind src t _) => some (src ++ p.drop t.length)
  | _ => none

/-- a write to sandbox path `p` modifies host path `hp` -/
def WritesHost (pol : Policy) (canWrite : Path → Prop) (p hp : Path) : Prop :=
  ∃ src t, effective pol p = some (.bind src t .rw) ∧ hp = src ++ p.drop t.length ∧ canWrite hp

/-- a read of sandbox path `p` reveals host path `hp` -/
def ReadsHost (pol : Policy) (p hp : Path) : Prop :=
  ∃ src t m, effective pol p = some (.bind src t m) ∧ hp = src ++ p.drop t.length

def home : Path := ["home", "opc"]
def research : Path := home ++ ["research"]
def mathlibProj : Path := research ++ ["alignment-contrib", "lean", "StabilityDebate"]
def hiddenDirs : List Path :=
  [research, home ++ [".claude"], ["tmp"], home ++ [".codex", "sessions"], home ++ [".codex", "log"],
   home ++ [".codex", "shell_snapshots"], home ++ [".gemini", "tmp"],
   home ++ [".gemini", "antigravity-cli", "brain"], home ++ [".gemini", "antigravity-cli", "conversations"],
   home ++ [".gemini", "antigravity-cli", "scratch"], home ++ [".gemini", "antigravity-cli", "log"]]

/-- the CURRENT policy of `dispatch.sandbox(work)` (hidden files omitted; all hidden dirs assumed to
exist): `--dev-bind / /`, `--tmpfs /var/tmp`, `--bind W /var/tmp/work`, a tmpfs over each hidden
directory, `--ro-bind MATHLIB MATHLIB`. -/
def currentPolicy (W : Path) : Policy :=
  [.bind [] [] .rw, .tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++
  hiddenDirs.map .tmpfs ++ [.bind mathlibProj mathlibProj .ro]

/-- a FIXED policy: read-only host root; writable scratch and declared CLI state directories only. -/
def fixedPolicy (W : Path) (stateDirs : List Path) : Policy :=
  [.bind [] [] .ro, .tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++
  hiddenDirs.map .tmpfs ++ stateDirs.map (fun d => .bind d d .rw) ++
  [.bind mathlibProj mathlibProj .ro]

def Claim : Prop :=
  -- (a) the current policy does NOT confine host writes to the scratch directory: with the user's own
  --     write permission on its home, the elan toolchain that the unsandboxed Lean gate executes is
  --     writable from inside the sandbox.
  (∀ W : Path, ["var", "tmp"] <+: W →
    WritesHost (currentPolicy W) (fun hp => home <+: hp ∨ ["var", "tmp"] <+: hp)
      (home ++ [".elan", "bin", "lake"]) (home ++ [".elan", "bin", "lake"])) ∧
  -- (b) the fixed policy confines host writes to the scratch directory and the declared state
  --     directories, for EVERY sandbox path and every host permission predicate.
  (∀ (W : Path) (stateDirs : List Path) (canWrite : Path → Prop) (p hp : Path),
    WritesHost (fixedPolicy W stateDirs) canWrite p hp →
      W <+: hp ∨ ∃ d ∈ stateDirs, d <+: hp) ∧
  -- (c) the current policy does hide the hidden directories: when the scratch directory lies under
  --     /var/tmp (as dispatch.py creates it), any host path inside a hidden directory that a sandbox read
  --     reveals lies inside the read-only Mathlib re-bind
  (∀ (W p hp H : Path), ["var", "tmp"] <+: W → H ∈ hiddenDirs → H <+: hp →
    ReadsHost (currentPolicy W) p hp → mathlibProj <+: hp)

/-- Non-vacuity: the fixed policy still lets the scratch directory be written, and still lets the
Mathlib project be read (read-only). -/
def Witness : Prop :=
  WritesHost (fixedPolicy ["var", "tmp", "pl-x"] []) (fun _ => True)
    ["var", "tmp", "work", "out.md"] ["var", "tmp", "pl-x", "out.md"] ∧
  ReadsHost (fixedPolicy ["var", "tmp", "pl-x"] []) (mathlibProj ++ ["lakefile.toml"])
    (mathlibProj ++ ["lakefile.toml"])

end PL_SANDBOXF1
