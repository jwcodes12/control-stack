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
