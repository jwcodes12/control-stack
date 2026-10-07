namespace PL_UMDEFERF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

/-! Control stack, collusion layer (campaign UMDEFER, v2.1: after the Reviewer A design review and the Reviewer A red team): audit, then defer
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

Contracts.
- α is a UNIFORM CONDITIONAL FLOOR, and this is a THEOREM here. The actual incrimination service `a h x z` may
  depend on the whole history and on the flagged submission and view (`catV`). If a h x z ≥ α on every
  REACHABLE, positive-probability exhausted-budget flag of a bad submission (`UniformFloor`, with reachability
  `Reach`), then catV ≤ catD, the constant-α model, so every upper bound below holds for the actual service.
  - Fresh, independent audit coins that select a fraction q of deferred items, each caught with recall r, give
    α = q·r. This requires the audit's catch probability to be independent across repeated audits of the same
    content; that is the most fragile part of the contract.
  - An AVERAGE rate does not give a floor. A single deployment-wide coin that audits all deferred items w.p. 1/2
    and none otherwise has "q = 1/2" and violates the bound (Reviewer A: 371/2000 > 2/11 at A = 1/10, three rounds).
- Resource. The deferred-item audits are an UNMETERED service: they are not charged to b. Their load is
  adversary-controlled, up to q(1 − η) per round over N rounds (honest flags included). Halting when a
  separate reserve runs out only lowers the risk (Reviewer B, numerics), so these bounds also cover that variant.
- Replacement. A submission has no effect before it executes; replacement removes the attack completely; the
  trusted replacement cannot itself cause the catastrophe; and shutdown on incrimination is immediate.
- Safety only. In this model halting (η = 1) dominates deferral. Deferral buys availability, which is not modelled
  here. The results price the safety cost of deferral; they do not recommend it.
- This is "audit-then-defer-after-exhaustion". It is not a general model of labs' defer-to-trusted routing
  (Greenblatt et al. defer by suspicion band), nor of Ctrl-Z resampling.

Claim.
(a) Halting recovery: η = 1 gives `cat` and `protocolCat`, for every service; and 0 ≤ catV ≤ 1.
(b) Finite state bound (constant model). Suppose every bad view law passes w.p. ≤ A. Then from any state,
    catD n u h ≤ finiteCap r A θ b n u, for every θ ∈ [0, 1], including θ = 0.
    - `retry A θ n` is the always-attack value of n exhausted-budget attempts.
    - An attack while audits remain decides at once (1 − r + rA).
    - Burning the b − u remaining audits takes b − u benign rounds, which leaves at most n − (b − u) retries.
    - The floor bridge carries this bound to the actual service.
(c) Attainment and closed form. A view-blind monitor (PASS w.p. A) with a fixed bad submission at an EXHAUSTED
    budget (u ≥ b) has catD = retry A θ n exactly, for the exact constant service. Before exhaustion,
    always-attack does not attain finiteCap (Witness: 1/10 < 29/200). The closed form is
    (θ + A(1 − θ))·retry A θ n = A(1 − ((1 − A)(1 − θ))^n). So, when the denominator is positive,
    retry ≤ A/(θ + A(1 − θ)) and retry → A/(θ + A(1 − θ)) as n → ∞ (sharp). This is the
    win/(win + safe-stop) ratio.
(d) Protocol certificate, hard slack, domination, for the ACTUAL service under the floor: if
    survH t (hardKill n_s) n_h 0 · finiteCap r (min 1 (L t)) θ b N 0 ≤ U for every t ∈ [0, 1], then every
    colluding pair has risk ≤ U.
    Coarse corollary for θ > 0, with H = L(n_s + 1)/(n_h + 1):
      risk ≤ max([0 < b]((1 − r) + rH), H/θ).
    - SUFFICIENT conditions for target risk ε: [0 < b]((1 − r) + rH) ≤ ε and θ ≥ H/ε. With b ≥ 1, no target
      below 1 − r is reachable.
    - Example: η = 0, r = 1, b = 0, L = 1, n_s = 5, n_h = 10⁴, ε = 10⁻³. The coarse condition asks q ≥ H/ε
      ≈ 0.6. The finite certificate shows θ ≈ 0.32 already suffices (Reviewer B, exact). r = 1 is the most
      favourable recall; smaller r needs larger q.
(e) No-go without a stopping hazard (η = α = 0), for every honeypot law on the two-point space and every
    horizon. Take Bool, the identity mediator, honeypot law PH and hard slack n_s.
    - The colluding monitor FLAGs the benign view and PASSes the attack view w.p. t. The generator submits the
      benign item until b audits are used, then attacks.
    - The risk is exactly binCDF n_h n_s (PH(true)·t) · (1 − (1 − t)^(N − b)) (natural subtraction).
    - This is ≥ (1 − t)^{n_h}·(1 − (1 − t)^(N − b)).
(e') Along t_K = 1/√(K+1), with K = N − b retries, that lower bound tends to 1 as K → ∞, for every fixed n_h
    (slowly). So over arbitrarily long deployments, honeypots alone give no guarantee.
    - At a fixed 0 < t ≤ 1 the value tends only to binCDF n_h n_s (PH(true)·t); at t = 0 it stays 0. The
      optimising t shrinks as the horizon grows.
    - Scope: this is the free-submission protocol WITHOUT a benign-flag guard. Greenblatt et al. App. G (an
      excess-false-positive test with a switch to trusted) and LASR's inverse honeypots are such guards. It is not a
      necessity theorem for incrimination: finite horizons, permanent switching and other stopping rules avoid it.

Novelty (honest). Prior art:
- the per-attempt stopping ratio and the replace-vs-audit distinction (Shlegeris, "Win/continue/lose scenarios
  and execute/replace/audit protocols", Redwood blog, Nov 2024: safety = P(caught)/(P(caught) + P(win)), which is
  A/(θ + A(1 − θ)) here);
- LASR's u/(c+u);
- Games for AI Control (2409.07985): Defer as a Blue action in trusted monitoring;
- Ctrl-Z (2504.10374): resampling-based incrimination.
What is claimed: the adaptive-generator Lean bound with a reachable conditional floor, its budget-sensitive
finite form, the composition with the honeypot test, and the no-go for every two-point honeypot law. -/

abbrev Service (X Z : Type) := Hist X Z → X → Z → ℝ

/-- Actual conditional safe-stop probability after deferral is a h x z.
It may depend on the entire live history and on the flagged submission/view. -/
noncomputable def catV {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (φ : Z → ℝ) (π : Hist X Z → X → ℝ)
    (r η : ℝ) (a : Service X Z) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else
         catV Bad M φ π r η a b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
         (if Bad x then 1 - r else
           catV Bad M φ π r η a b n (u + 1) (h ++ [(x, z, false)]))
         else (1 - η) * (if Bad x then 1 - a h x z else 1) *
           catV Bad M φ π r η a b n u (h ++ [(x, z, false)])))

/-- Constant-service model, and pessimistic envelope for a conditional floor α.
Equality/attainment statements refer to this exact constant service. -/
noncomputable def catD {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α : ℝ) (b : ℕ) :=
  catV Bad M φ π r η (fun _ _ _ => α) b

noncomputable def protocolCatV {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r η : ℝ)
    (a : Ω → Service X Z) (b N : ℕ) (ρ : Ω → ℝ)
    (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * surv (push M PH) (φ ω) κ nh 0 *
    catV Bad M (φ ω) (π ω) r η (a ω) b N 0 []

noncomputable def protocolCatD {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r η α : ℝ)
    (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ)
    (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  protocolCatV Bad M PH κ nh r η (fun _ _ _ _ => α) b N ρ φ π

def theta (η α : ℝ) : ℝ := η + (1 - η) * α

def retry (A θ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => A + (1 - A) * (1 - θ) * retry A θ n

noncomputable def finiteCap (r A θ : ℝ) (b n u : ℕ) : ℝ :=
  if n = 0 then 0
  else if u < b then
    max (1 - r + r * A) (retry A θ (n - (b - u)))
  else retry A θ n

def burnThenAttack (b : ℕ) : Hist Bool Bool → Bool → ℝ :=
  fun h x =>
    if (h.filter (fun e => e.2.2 = false)).length < b then
      (if x = false then 1 else 0)
    else (if x = true then 1 else 0)

def Core {X Z : Type} [Fintype X] [Fintype Z]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ)
    (r η : ℝ) : Prop :=
  IsKernel M ∧ IsRule φ ∧ (∀ h, IsDist (π h)) ∧
  0 ≤ r ∧ r ≤ 1 ∧ 0 ≤ η ∧ η ≤ 1

def IsService {X Z : Type} (a : Service X Z) : Prop :=
  ∀ h x z, 0 ≤ a h x z ∧ a h x z ≤ 1

/-- Positive-probability live states reachable within the remaining horizon.
Only benign audited flags continue while u < b. -/
inductive Reach {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (φ : Z → ℝ) (π : Hist X Z → X → ℝ)
    (η : ℝ) (a : Service X Z) (b n0 u0 : ℕ) (h0 : Hist X Z) :
    ℕ → ℕ → Hist X Z → Prop where
  | start : Reach Bad M φ π η a b n0 u0 h0 n0 u0 h0
  | pass {n u h x z} :
      Reach Bad M φ π η a b n0 u0 h0 (n + 1) u h →
      0 < π h x → 0 < M x z → ¬ Bad x → 0 < φ z →
      Reach Bad M φ π η a b n0 u0 h0 n u (h ++ [(x, z, true)])
  | audit {n u h x z} :
      Reach Bad M φ π η a b n0 u0 h0 (n + 1) u h →
      0 < π h x → 0 < M x z → ¬ Bad x → 0 < 1 - φ z → u < b →
      Reach Bad M φ π η a b n0 u0 h0 n (u + 1) (h ++ [(x, z, false)])
  | defer {n u h x z} :
      Reach Bad M φ π η a b n0 u0 h0 (n + 1) u h →
      0 < π h x → 0 < M x z → 0 < 1 - φ z → b ≤ u →
      0 < (1 - η) * (if Bad x then 1 - a h x z else 1) →
      Reach Bad M φ π η a b n0 u0 h0 n u (h ++ [(x, z, false)])

/-- The floor is required only on reachable, positive-probability deferred bad flags.
It is conditional on the colluder's seed when used in the protocol theorem. -/
def UniformFloor {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (φ : Z → ℝ) (π : Hist X Z → X → ℝ)
    (η : ℝ) (a : Service X Z) (b n u : ℕ) (h : Hist X Z)
    (α : ℝ) : Prop :=
  ∀ k v g x z, Reach Bad M φ π η a b n u h (k + 1) v g →
    b ≤ v → Bad x → 0 < π g x → 0 < M x z →
    0 < 1 - φ z → 0 < 1 - η → α ≤ a g x z

def PairCore {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (M : X → Z → ℝ) (PH : X → ℝ) (ρ : Ω → ℝ)
    (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ)
    (r η : ℝ) : Prop :=
  IsDist PH ∧ IsDist ρ ∧ ∀ ω, Core M (φ ω) (π ω) r η

def ProtocolFloor {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ)
    (η : ℝ) (a : Ω → Service X Z) (b N : ℕ) (α : ℝ) : Prop :=
  ∀ ω, IsService (a ω) ∧
    UniformFloor Bad M (φ ω) (π ω) η (a ω) b N 0 [] α

def Claim : Prop :=
  -- (a): halting recovery, including arbitrary conditional services.
  (∀ (X Z : Type) [Fintype X] [Fintype Z]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ)
      (a : Service X Z) (b n u : ℕ) (h : Hist X Z),
      catV Bad M φ π r 1 a b n u h = cat Bad M φ π r b n u h) ∧
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ)
      (a : Ω → Service X Z) (b N : ℕ) (ρ : Ω → ℝ)
      (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      protocolCatV Bad M PH κ nh r 1 a b N ρ φ π =
        protocolCat Bad M PH κ nh r b N ρ φ π) ∧
  (∀ (X Z : Type) [Fintype X] [Fintype Z]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η : ℝ)
      (a : Service X Z) (b : ℕ),
      Core M φ π r η → IsService a →
      ∀ n u h, 0 ≤ catV Bad M φ π r η a b n u h ∧
        catV Bad M φ π r η a b n u h ≤ 1) ∧
  -- (b): exact constant model's finite cap.
  (∀ (X Z : Type) [Fintype X] [Fintype Z]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α A : ℝ) (b : ℕ),
      Core M φ π r η → 0 ≤ α → α ≤ 1 → 0 ≤ A → A ≤ 1 →
      (∀ x, Bad x → E (M x) φ ≤ A) →
      ∀ n u h, catD Bad M φ π r η α b n u h ≤
        finiteCap r A (theta η α) b n u) ∧
  -- Missing bridge repaired: any conditional service satisfying the floor.
  (∀ (X Z : Type) [Fintype X] [Fintype Z]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α : ℝ)
      (a : Service X Z) (b n u : ℕ) (h : Hist X Z),
      Core M φ π r η → IsService a → 0 ≤ α → α ≤ 1 →
      UniformFloor Bad M φ π η a b n u h α →
      catV Bad M φ π r η a b n u h ≤ catD Bad M φ π r η α b n u h) ∧
  -- (c): always-attack attains retry only at an exhausted budget,
  -- for an exact constant service, not for every service with that floor.
  (∀ (X Z : Type) [Fintype X] [Fintype Z] [DecidableEq X]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (r η α A : ℝ) (b n u : ℕ) (h : Hist X Z) (x : X),
      IsKernel M → Bad x → b ≤ u →
      catD Bad M (fun _ => A) (fun _ x' => if x' = x then 1 else 0)
        r η α b n u h = retry A (theta η α) n) ∧
  (∀ (A θ : ℝ) (n : ℕ),
      (θ + A * (1 - θ)) * retry A θ n =
        A * (1 - ((1 - A) * (1 - θ)) ^ n)) ∧
  (∀ (A θ : ℝ) (n : ℕ), 0 ≤ A → A ≤ 1 → 0 ≤ θ → θ ≤ 1 →
      0 < θ + A * (1 - θ) →
      retry A θ n ≤ A / (θ + A * (1 - θ))) ∧
  (∀ (A θ : ℝ), 0 ≤ A → A ≤ 1 → 0 ≤ θ → θ ≤ 1 → 0 < θ + A * (1 - θ) →
      Filter.Tendsto (fun n : ℕ => retry A θ n) Filter.atTop (nhds (A / (θ + A * (1 - θ))))) ∧
  -- (d): certificate for actual services with the conditional floor.
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (PH : X → ℝ) (nh ns b N : ℕ) (r η α L U : ℝ)
      (a : Ω → Service X Z) (ρ : Ω → ℝ)
      (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      PairCore M PH ρ φ π r η → 0 ≤ α → α ≤ 1 → 0 ≤ L →
      ProtocolFloor Bad M φ π η a b N α →
      (∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        survH t (hardKill ns) nh 0 *
          finiteCap r (min 1 (L * t)) (theta η α) b N 0 ≤ U) →
      protocolCatV Bad M PH (hardKill ns) nh r η a b N ρ φ π ≤ U) ∧
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (PH : X → ℝ) (nh ns b N : ℕ) (r η α L : ℝ)
      (a : Ω → Service X Z) (ρ : Ω → ℝ)
      (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      PairCore M PH ρ φ π r η → 0 ≤ α → α ≤ 1 → 0 ≤ L →
      ProtocolFloor Bad M φ π η a b N α → 0 < theta η α →
      (∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) →
      protocolCatV Bad M PH (hardKill ns) nh r η a b N ρ φ π ≤
        max (if 0 < b then
          (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) else 0)
          (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)) / theta η α)) ∧
  -- (e): universal-honeypot-law no-go; r need not be constrained
  -- because every available audit in this strategy is on a benign item.
  (∀ (PH : Bool → ℝ) (nh ns b N : ℕ) (r t : ℝ),
      IsDist PH → 0 ≤ t → t ≤ 1 →
      protocolCatD (X := Bool) (Z := Bool) (Ω := Unit)
        (fun x => x = true) (fun x z => if z = x then 1 else 0)
        PH (hardKill ns) nh r 0 0 b N (fun _ => 1)
        (fun _ z => if z = true then t else 0) (fun _ => burnThenAttack b) =
          binCDF nh ns (PH true * t) * (1 - (1 - t) ^ (N - b)) ∧
      (1 - t) ^ nh * (1 - (1 - t) ^ (N - b)) ≤
        binCDF nh ns (PH true * t) * (1 - (1 - t) ^ (N - b))) ∧
  -- At fixed 0 < t ≤ 1, the no-go limit is binCDF nh ns (PH true * t).
  -- At t = 0 the risk stays zero. Always-attack is not claimed to attain
  -- finiteCap before exhaustion.
  -- (e'): n_h is fixed while the deployment horizon grows.
  (∀ nh : ℕ, Filter.Tendsto
    (fun K : ℕ => (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ nh *
      (1 - (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ K))
    Filter.atTop (nhds 1))

noncomputable def witnessM : Unit → Unit → ℝ := fun _ _ => 1
noncomputable def witnessPhi : Unit → ℝ := fun _ => 1/10
noncomputable def witnessPi : Hist Unit Unit → Unit → ℝ := fun _ _ => 1
noncomputable def witnessService : Service Unit Unit :=
  fun h _ _ => if h = [] then 3/4 else 1/2

/-- Explicitly witnesses the model assumptions, conditional floor and domination,
including a genuinely history-dependent service and a nontrivial certificate. -/
def Witness : Prop :=
  Core witnessM witnessPhi witnessPi 1 0 ∧
  IsDist (fun _ : Unit => (1 : ℝ)) ∧
  IsService witnessService ∧
  UniformFloor (fun _ : Unit => True) witnessM witnessPhi witnessPi
    0 witnessService 0 2 0 [] (1/2) ∧
  E (witnessM ()) witnessPhi = 1/10 ∧
  (∀ z : Unit, witnessM () z ≤ 1 *
    push witnessM (fun _ : Unit => (1 : ℝ)) z) ∧
  catV (fun _ : Unit => True) witnessM witnessPhi witnessPi
    1 0 witnessService 0 2 0 [] = 49/400 ∧
  catD (fun _ : Unit => True) witnessM witnessPhi witnessPi
    1 0 (1/2) 0 2 0 [] = 29/200 ∧
  catD (fun _ : Unit => True) witnessM witnessPhi witnessPi
    1 0 0 0 2 0 [] = 19/100 ∧
  finiteCap 1 (1/10) (1/2) 1 3 0 = 29/200 ∧
  catD (fun _ : Unit => True) witnessM witnessPhi witnessPi
    1 0 (1/2) 1 3 0 [] = 1/10 ∧
  (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    survH t (hardKill 0) 3 0 *
      finiteCap 1 (min 1 (1 * t)) (theta 0 (1/2)) 0 2 0 ≤ 1/2) ∧
  protocolCatV (X := Unit) (Z := Unit) (Ω := Unit) (fun _ => True)
    witnessM (fun _ => 1) (hardKill 0) 3 1 0
    (fun _ => witnessService) 0 2 (fun _ => 1)
    (fun _ => witnessPhi) (fun _ => witnessPi) = 35721/400000 ∧
  protocolCatD (X := Bool) (Z := Bool) (Ω := Unit) (fun x => x = true)
    (fun x z => if z = x then 1 else 0) (fun x => if x = true then 1 else 0)
    (hardKill 0) 2 1 0 0 1 3 (fun _ => 1)
    (fun _ z => if z = true then 1/2 else 0) (fun _ => burnThenAttack 1) = 3/16

end PL_UMDEFERF1
