namespace PL_UMDEFERF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

/-! Control stack, collusion layer (campaign UMDEFER, v2 after the Sol xhigh design review): audit, then defer
after audit exhaustion. Retries need a stopping hazard. Depends on PL_UMPROTF1 (and PL_UMHSF1, PL_UMSURVF1).

Protocol. It is the halting protocol of PL_UMPROTF1 while audits remain (u < b). A FLAG on a bad submission is then
audited: caught w.p. r, which is absorbing shutdown; otherwise the attack executes. A FLAG with NO audit left
(u ≥ b) is handled as follows:
- with probability η, halt (safe);
- otherwise DEFER: the submission is replaced by trusted output, and deployment continues at the same u. A
  deferred BAD submission ends the game safely with probability α (incrimination, then absorbing shutdown);
  otherwise the colluders may retry. A deferred benign submission continues.
θ = η + (1 − η)·α is the stopping hazard of an exhausted-budget flag on an attack. The special cases:
η = 1 is PL_UMPROTF1; η = α = 0 is defer without incrimination (variant D).

Contracts (assumptions, not theorems).
- α is a UNIFORM CONDITIONAL FLOOR. On every reachable exhausted-budget flag of a bad submission, the probability
  of a safe end must be ≥ α, conditional on the history. Fresh, independent audit coins that select a fraction q of
  deferred items, each caught with recall r, give α = q·r. An average rate does not: a single deployment-wide coin
  that audits all deferred items w.p. 1/2 and none otherwise has "q = 1/2" and violates the bound (Sol: 371/2000 >
  2/11 at A = 1/10, three rounds).
- Resource. The deferred-item audits are a SEPARATELY FUNDED service: they are not charged to b. Their expected
  load is q times the number of exhausted-budget flags, honest ones included.
- Replacement. A submission has no effect before it executes; replacement removes the attack completely; and the
  trusted replacement cannot itself cause the catastrophe. Shutdown on incrimination is immediate.
- This is "audit-then-defer-after-exhaustion". It is not a general model of labs' defer-to-trusted routing
  (Greenblatt et al. defer by suspicion band), and it is not a model of Ctrl-Z resampling.

Claim.
(a) Halting recovery: η = 1 gives `cat` and `protocolCat`; and 0 ≤ catD ≤ 1.
(b) Finite state bound. Suppose every bad view law passes w.p. ≤ A. Then from any state,
    catD n u h ≤ finiteCap r A θ b n u. Here `retry A θ n` is the always-attack value of n exhausted-budget
    attempts. An attack while audits remain decides at once (1 − r + rA). Burning the b − u remaining audits
    takes b − u benign rounds, which leaves at most n − (b − u) retries. This holds for every θ ∈ [0, 1],
    including θ = 0.
(c) Attainment and closed form. A view-blind monitor (PASS w.p. A) with a fixed bad submission at u ≥ b has
    catD = retry A θ n exactly, and (θ + A(1 − θ))·retry A θ n = A(1 − ((1 − A)(1 − θ))^n). So retry ≤
    A/(θ + A(1 − θ)) whenever the denominator is positive; this is the win/(win + safe-stop) ratio.
(d) Protocol certificate, hard slack, domination. If survH t (hardKill n_s) n_h 0 · finiteCap r (min 1 (L t))
    θ b N 0 ≤ U for every t ∈ [0, 1], then every colluding pair has risk ≤ U.
    Coarse corollary for θ > 0, with H = L(n_s + 1)/(n_h + 1):
      risk ≤ max([0 < b]((1 − r) + rH), H/θ).
    So target risk ε is certified when [0 < b]((1 − r) + rH) ≤ ε and θ ≥ H/ε. For η = 0 and r = 1 this means
    q ≥ H/ε: e.g. L = 1, n_s = 5, n_h = 10⁴ and ε = 10⁻³ need about 60% of deferred items audited.
(e) No-go without a stopping hazard (η = α = 0), for EVERY honeypot law and every horizon. Take Bool, the identity
    mediator, honeypot law PH and hard slack n_s. The colluding monitor FLAGs the benign view and PASSes the attack
    view w.p. t. The generator submits the benign item until b audits are used, then attacks. The risk is exactly
      binCDF n_h n_s (PH(true)·t) · (1 − (1 − t)^(N − b))
    (natural subtraction), which is ≥ (1 − t)^{n_h}·(1 − (1 − t)^(N − b)).
(e') Along t_K = 1/√(K+1), with K = N − b retries, this lower bound tends to 1 as K → ∞ for every fixed n_h.
    So over arbitrarily long deployments, honeypots alone give no guarantee. At a fixed t the value tends only to
    binCDF n_h n_s t; the optimising t shrinks as the horizon grows.
    Scope: this is the free-submission protocol WITHOUT a benign-flag guard. Greenblatt et al. App. G (an
    excess-false-positive test with a switch to trusted) and LASR's inverse honeypots are such guards. The result
    is not a necessity theorem for incrimination: finite horizons, permanent switching and other stopping rules
    avoid it.

Novelty (honest). The per-attempt stopping ratio and the replace-vs-audit distinction are prior art: Shlegeris,
"Win/continue/lose scenarios and execute/replace/audit protocols", Redwood blog, Nov 2024; LASR's u/(c+u). What is
claimed is the adaptive-generator Lean bound, its budget-sensitive finite form, the composition with the honeypot
test, and the no-go for every honeypot law. -/

/-- P(catastrophe in the remaining `n` rounds | `u` audits used, history `h`), audit-then-defer -/
noncomputable def catD {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α : ℝ) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else catD Bad M φ π r η α b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 1 - r else catD Bad M φ π r η α b n (u + 1) (h ++ [(x, z, false)]))
                    else (1 - η) * ((if Bad x then 1 - α else 1) *
                      catD Bad M φ π r η α b n u (h ++ [(x, z, false)]))))

/-- P(survive the honeypot test, then uncaught catastrophe), audit-then-defer -/
noncomputable def protocolCatD {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ)
    (r η α : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * surv (push M PH) (φ ω) κ nh 0 * catD Bad M (φ ω) (π ω) r η α b N 0 []

/-- stopping hazard of an exhausted-budget flag on an attack -/
def theta (η α : ℝ) : ℝ := η + (1 - η) * α

/-- always-attack value of `n` exhausted-budget attempts with pass probability `A` -/
def retry (A θ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => A + (1 - A) * (1 - θ) * retry A θ n

/-- the finite state bound: decide at once while audits remain, or burn them and retry -/
noncomputable def finiteCap (r A θ : ℝ) (b n u : ℕ) : ℝ :=
  if n = 0 then 0
  else if u < b then max (1 - r + r * A) (retry A θ (n - (b - u)))
  else retry A θ n

/-- the no-go colluder's generator: submit the benign `false` until `b` audits are used, then the attack -/
def burnThenAttack (b : ℕ) : Hist Bool Bool → Bool → ℝ :=
  fun h x => if (h.filter (fun e => e.2.2 = false)).length < b then (if x = false then 1 else 0)
             else (if x = true then 1 else 0)

def Claim : Prop :=
  -- (a) halting recovery and probability bounds
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r α : ℝ) (b n u : ℕ) (h : Hist X Z),
      catD Bad M φ π r 1 α b n u h = cat Bad M φ π r b n u h) ∧
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r α : ℝ) (b N : ℕ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      protocolCatD Bad M PH κ nh r 1 α b N ρ φ π = protocolCat Bad M PH κ nh r b N ρ φ π) ∧
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α : ℝ) (b : ℕ),
      IsKernel M → IsRule φ → (∀ h, IsDist (π h)) → 0 ≤ r → r ≤ 1 → 0 ≤ η → η ≤ 1 → 0 ≤ α → α ≤ 1 →
      ∀ n u h, 0 ≤ catD Bad M φ π r η α b n u h ∧ catD Bad M φ π r η α b n u h ≤ 1) ∧
  -- (b) finite state bound
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α A : ℝ) (b : ℕ),
      IsKernel M → IsRule φ → (∀ h, IsDist (π h)) → 0 ≤ r → r ≤ 1 → 0 ≤ η → η ≤ 1 → 0 ≤ α → α ≤ 1 →
      0 ≤ A → A ≤ 1 → (∀ x, Bad x → E (M x) φ ≤ A) →
      ∀ n u h, catD Bad M φ π r η α b n u h ≤ finiteCap r A (theta η α) b n u) ∧
  -- (c) attainment at an exhausted budget, closed form, ratio
  (∀ (X Z : Type) [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (r η α A : ℝ) (b n u : ℕ) (h : Hist X Z) (x : X),
      IsKernel M → Bad x → b ≤ u →
      catD Bad M (fun _ => A) (fun _ x' => if x' = x then 1 else 0) r η α b n u h =
        retry A (theta η α) n) ∧
  (∀ (A θ : ℝ) (n : ℕ), (θ + A * (1 - θ)) * retry A θ n = A * (1 - ((1 - A) * (1 - θ)) ^ n)) ∧
  (∀ (A θ : ℝ) (n : ℕ), 0 ≤ A → A ≤ 1 → 0 ≤ θ → θ ≤ 1 → 0 < θ + A * (1 - θ) →
      retry A θ n ≤ A / (θ + A * (1 - θ))) ∧
  -- (d) protocol certificate and its coarse corollary (hard slack, domination)
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r η α L U : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      0 ≤ r → r ≤ 1 → 0 ≤ η → η ≤ 1 → 0 ≤ α → α ≤ 1 → 0 ≤ L →
      (∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          survH t (hardKill ns) nh 0 * finiteCap r (min 1 (L * t)) (theta η α) b N 0 ≤ U) →
      protocolCatD Bad M PH (hardKill ns) nh r η α b N ρ φ π ≤ U) ∧
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r η α L : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      0 ≤ r → r ≤ 1 → 0 ≤ η → η ≤ 1 → 0 ≤ α → α ≤ 1 → 0 ≤ L → 0 < theta η α →
      (∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) →
      protocolCatD Bad M PH (hardKill ns) nh r η α b N ρ φ π ≤
        max (if 0 < b then (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) else 0)
            (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)) / theta η α)) ∧
  -- (e) no-go without a stopping hazard, every honeypot law, every horizon
  (∀ (PH : Bool → ℝ) (nh ns b N : ℕ) (r t : ℝ), IsDist PH → 0 ≤ t → t ≤ 1 →
      protocolCatD (X := Bool) (Z := Bool) (Ω := Unit) (fun x => x = true)
          (fun x z => if z = x then 1 else 0) PH (hardKill ns) nh r 0 0 b N (fun _ => 1)
          (fun _ z => if z = true then t else 0) (fun _ => burnThenAttack b)
        = binCDF nh ns (PH true * t) * (1 - (1 - t) ^ (N - b)) ∧
      (1 - t) ^ nh * (1 - (1 - t) ^ (N - b)) ≤ binCDF nh ns (PH true * t) * (1 - (1 - t) ^ (N - b))) ∧
  -- (e') the lower bound along t_K = 1/√(K+1) tends to 1 as the number of retries K → ∞
  (∀ nh : ℕ, Filter.Tendsto
      (fun K : ℕ => (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ nh * (1 - (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ K))
      Filter.atTop (nhds 1))

/-- Non-vacuity.
- Retry suppression. One bad submission, identity view, A = 1/10, no audit budget, η = 0, r = 1, two rounds:
  with α = 1/2 the risk is 29/200; with α = 0 (no incrimination) it is 19/100.
- finiteCap is informative: at r = 1, A = 1/10, θ = 1/2, b = 1, n = 3, u = 0 it is max(1/10, retry 2) = 29/200.
- No-go: n_h = 2, n_s = 0, b = 1, N = 3, t = 1/2, point-mass honeypots: (1/4)(3/4) = 3/16. -/
def Witness : Prop :=
  catD (X := Unit) (Z := Unit) (fun _ => True) (fun _ _ => 1) (fun _ => 1/10) (fun _ _ => 1)
      1 0 (1/2) 0 2 0 [] = 29/200 ∧
  catD (X := Unit) (Z := Unit) (fun _ => True) (fun _ _ => 1) (fun _ => 1/10) (fun _ _ => 1)
      1 0 0 0 2 0 [] = 19/100 ∧
  theta 0 (1/2) = 1/2 ∧
  finiteCap 1 (1/10) (1/2) 1 3 0 = 29/200 ∧
  protocolCatD (X := Bool) (Z := Bool) (Ω := Unit) (fun x => x = true)
      (fun x z => if z = x then 1 else 0) (fun x => if x = true then 1 else 0) (hardKill 0) 2
      1 0 0 1 3 (fun _ => 1) (fun _ z => if z = true then 1/2 else 0) (fun _ => burnThenAttack 1)
    = 3/16

end PL_UMDEFERF1
