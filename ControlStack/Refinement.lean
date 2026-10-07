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

The definitions `IsKernel`, `cat` and `binCDF` are textual copies of the ledger statements
(PL_UMHSF1, PL_UMPROTF1, PL_UMSURVF1; Lean v4.35 project). The two projects are linked only by this
textual identity. `EndToEndClaim` does not depend on the link: it is stated and proved here.
-/
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.ProbComp

open OracleComp

namespace ControlStack.Refine

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

/-- textual copy of `PL_UMSURVF1.binCDF` -/
def binCDF (n s : ℕ) (h : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (s + 1), (n.choose j : ℝ) * h ^ j * (1 - h) ^ (n - j)

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

/-- the honeypot test: number of PASSes among `n` fresh mediated honeypots (as in the Bridge) -/
def honeypotPasses {X Z : Type} (H : ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool) :
    ℕ → ProbComp ℕ
  | 0 => pure 0
  | n + 1 => do
      let b ← (H >>= M >>= D)
      let k ← honeypotPasses H M D n
      pure (if b then k + 1 else k)

/-- the whole protocol game; `true` = the colluding pair survived the test and then caused an uncaught
catastrophe -/
def protocolGame {X Z Ω : Type} (Bad : X → Prop) [DecidablePred Bad] (ρ : ProbComp Ω)
    (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (π : Ω → Hist X Z → ProbComp X) (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) :
    ProbComp Bool := do
  let ω ← ρ
  let k ← honeypotPasses H M (D ω) nh
  if k ≤ ns then deploy Bad (π ω) M (D ω) A b N 0 [] else pure false

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
  ∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
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

end ControlStack.Refine
