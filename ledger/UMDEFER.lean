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
