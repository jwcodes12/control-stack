namespace PL_UMPROTF1
open Finset PL_UMHSF1

/-! Control stack, collusion layer, T3: protocol safety of untrusted monitoring with honeypots.
Depends on PL_UMHSF1 (definitions `E`, `push`, `hs`, `IsDist`, `IsKernel`, `IsRule`).

Protocol UM(n_h, κ, b, N): an upfront honeypot phase (n_h iid honeypots from `PH`, mediated by `M`;
each PASS on a honeypot is a miss; the (j+1)-th miss shuts the monitor down with probability
`κ j`), then N deployment rounds. In each round the generator submits `x ~ π ω hist`; the view is
`z ~ M x`; the monitor PASSes with probability `φ ω z`. PASS on a bad submission is a catastrophe.
FLAG is audited while fewer than `b` audits are used (a bad submission is caught with probability
`r`, else it executes = catastrophe); FLAG with the budget exhausted halts deployment (safe).
The colluding pair shares a seed `ω ~ ρ`; the monitor is stateless (`φ ω` depends on the view only);
the generator is an arbitrary history-dependent randomised policy. -/

/-- survival of the honeypot phase: `n` honeypots left, `j` misses so far -/
def surv {Z : Type} [Fintype Z] (q φ : Z → ℝ) (κ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n + 1, j => ∑ z, q z * ((1 - φ z) * surv q φ κ n j + φ z * (1 - κ j) * surv q φ κ n (j + 1))

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

/-- P(catastrophe) of the whole protocol -/
noncomputable def protocolCat {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ)
    (r : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * surv (push M PH) (φ ω) κ nh 0 * cat Bad M (φ ω) (π ω) r b N 0 []

/-- hard slack: the (ns+1)-th honeypot miss shuts down -/
def hardKill (ns : ℕ) : ℕ → ℝ := fun j => if ns ≤ j then 1 else 0
/-- soft slack (LASR App. B.5): every miss shuts down (retrains) with probability 1/ns -/
noncomputable def softKill (ns : ℕ) : ℕ → ℝ := fun _ => 1 / (ns : ℝ)

def Claim : Prop :=
  ∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r η δ : ℝ)
    (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
    IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
    0 ≤ r → r ≤ 1 → 0 ≤ δ →
    -- trusted-component hypothesis: every bad submission's mediated view is (e^η, δ)-close to
    -- the mediated honeypot law
    (∀ x, Bad x → hs η (M x) (push M PH) ≤ δ) →
    protocolCat Bad M PH (hardKill ns) nh r b N ρ φ π
        ≤ (1 - r) + δ + Real.exp η * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)) ∧
    (1 ≤ ns → protocolCat Bad M PH (softKill ns) nh r b N ρ φ π
        ≤ (1 - r) + δ + Real.exp η * ((ns : ℝ) / ((nh : ℝ) + 1)))

/-- Non-vacuity: X = Z = Bool, Bad = {true}, identity mediator, honeypots = point mass on `true`
(so δ = 0 at η = 0), r = 1, n_h = 3, hard slack 0, one round. The colluder that passes with
probability 1/4 everywhere and always attacks has catastrophe probability (3/4)^3 · 1/4 = 27/256,
below the bound (0+1)/(3+1) = 1/4. -/
def Witness : Prop :=
  protocolCat (X := Bool) (Z := Bool) (Ω := Unit) (fun x => x = true)
      (fun x z => if z = x then 1 else 0) (fun x => if x = true then 1 else 0) (hardKill 0) 3
      1 1 1 (fun _ => 1) (fun _ _ => 1/4) (fun _ _ x => if x = true then 1 else 0) = 27/256 ∧
  hs 0 (fun z : Bool => if z = true then (1 : ℝ) else 0)
      (push (fun (x : Bool) (z : Bool) => if z = x then (1 : ℝ) else 0)
            (fun x => if x = true then 1 else 0)) = 0

end PL_UMPROTF1
