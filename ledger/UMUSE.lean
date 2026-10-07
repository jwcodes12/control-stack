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
