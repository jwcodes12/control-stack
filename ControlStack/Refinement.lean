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
  and PASSes the next one reaches catastrophe probability 1 (Reviewer B's review), so this restriction IS the theorem.
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
