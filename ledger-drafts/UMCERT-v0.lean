namespace PL_UMCERTF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 PL_UMSTRATF1

/-! Control stack, collusion layer (campaign UMCERT): certificate form of the halting-protocol bound
(PL_UMPROTF1) and of the stratified bound (PL_UMSTRATF1). Depends on PL_UMPROTF1 and PL_UMSTRATF1.

The counting bounds (1 − r) + r·L·(n_s+1)/(n_h+1) and (1 − r) + r·(s_c+1)/(m+1) come from the Markov-type
inequality h·binCDF(n, s, h) ≤ (s+1)/(n+1). They are loose: at m = 12, s_c = 1, r = 1 the counting bound is
2/13 ≈ 0.154, while the worst case is about 0.068. This campaign replaces the Markov step by a
one-dimensional certificate over the honeypot pass rate t ∈ [0, 1], and shows the certificate is EXACT.

Notation. `capB r b a` is the value of one attack that passes the monitor with probability `a`:
1 − r + r·a when an audit is available (b ≥ 1), and a when b = 0 (an unaffordable flag halts).

Claim.
(R) One-shot reduction (exact, every valid shutdown schedule κ, every budget b, horizon N ≥ 1). Every colluding
    pair (shared seed, stateless monitor, adaptive history-dependent generator) has risk ≤ U iff every ONE-SHOT pair
    does: a fixed bad submission x attacked in the first round, with a stateless rule ψ and no seed. The one-shot
    value is survH(E_{M·PH} ψ)·capB(E_{M x} ψ). So shared randomness, history dependence and waiting do not help
    the colluders in the halting protocol, and the worst case is a function of the trusted components
    (M, PH, κ, n_h, r, b) only.
(C) Envelope certificate. If g is an envelope of the trusted mediator (every bad view law passes a rule ψ with
    probability ≤ g(honeypot pass rate of ψ)) and survH(t)·capB(min 1 (g t)) ≤ U for every t ∈ [0, 1], then every
    colluding pair has risk ≤ U.
(E) The two trusted-side hypotheses of UMPROT T3 give envelopes: L-domination gives g t = L·t; a hockey-stick
    bound hs_η ≤ δ gives g t = e^η·t + δ (UMHS T2).
(G0) Survival is antitone in the pass rate, for every schedule κ with values in [0, 1].
(G) Grid certificates. For S antitone and F monotone, both nonnegative on [0, 1], a finite grid
    0 = t_0 ≤ t_1 ≤ … ≤ t_K = 1 with S(t_i)·F(t_{i+1}) ≤ U for every i certifies S(t)·F(t) ≤ U on [0, 1].
    With (G0) and (C) this turns a sup over t into finitely many rational inequalities.
(F) Honest-free floor (acceptance-sampling AOQL). For nonempty Bad and N ≥ 1, any certificate U for all colluding
    pairs satisfies survH(t)·capB(t) ≤ U for every t ∈ [0, 1], whatever the mediator and honeypot law
    (the view-blind pair; compare UMUSE (c')).
(X) Exactness at L = 1: if every bad view law is dominated by the mediated honeypot law with constant 1, then
    (every colluding pair has risk ≤ U) iff (survH(t)·capB(t) ≤ U for every t ∈ [0, 1]).
(S1) Stratified certificate. With a content-only mediator and class-aware hard slack, if
    binCDF(m, s_c, t)·capB(t) ≤ U for every t ∈ [0, 1], then every colluding pair has risk ≤ U. No coverage or
    domination constant is needed beyond content-only views and tested bad classes.
(S2) Stratified exactness. Under exact class decoding, b ≥ 1, N ≥ 1 and nonempty Bad, the certificate in (S1)
    is also necessary. So the stratified design's exact worst case is max_t binCDF(m, s_c, t)·(1 − r + r·t), the
    AOQL-type value of the per-class single-sampling plan, independent of the kernel K and of the number of classes.

Scope. Same model and assumptions as PL_UMPROTF1 / PL_UMSTRATF1 (A1–A11; constant audit recall r; halting on an
unaffordable flag; upfront test; absorbing shutdown on a catch). Nothing here concerns adaptive testers,
deferral or usefulness. The mathematics is classical (first-bad-decides plus a reduction to one-shot pairs, and a
monotone grid bound); the value is that numerical design tables become Lean-checked certificates. -/

/-- value of one attack that passes the monitor with probability `a` at audit budget `b` -/
def capB (r : ℝ) (b : ℕ) (a : ℝ) : ℝ := if 0 < b then 1 - r + r * a else a

/-- every consecutive pair `s, t` of the list satisfies `s ≤ t` and `S s * F t ≤ U` -/
def GridOK (S F : ℝ → ℝ) (U : ℝ) : List ℝ → Prop
  | s :: t :: rest => s ≤ t ∧ S s * F t ≤ U ∧ GridOK S F U (t :: rest)
  | _ => True

/-- a grid certificate: a list from 0 to 1 whose consecutive cells pass the check -/
def GridCert (S F : ℝ → ℝ) (U : ℝ) (ts : List ℝ) : Prop :=
  ts.head? = some 0 ∧ ts.getLast? = some 1 ∧ GridOK S F U ts

def Claim : Prop :=
  -- (R) one-shot reduction, exact
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ),
      IsKernel M → IsDist PH → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N → 0 ≤ U →
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ↔
       (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ →
          survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) ≤ U))) ∧
  -- (C) envelope certificate
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (g : ℝ → ℝ) (U : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 0 ≤ U →
      (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ g (E (push M PH) ψ)) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b (min 1 (g t)) ≤ U) →
      protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ∧
  -- (E) envelopes from L-domination and from a hockey-stick bound
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (L : ℝ) (x : X),
      (∀ z, M x z ≤ L * push M PH z) →
      ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ L * E (push M PH) ψ) ∧
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (η δ : ℝ) (x : X),
      hs η (M x) (push M PH) ≤ δ →
      ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ Real.exp η * E (push M PH) ψ + δ) ∧
  -- (G0) survival is antitone in the pass rate
  (∀ (κ : ℕ → ℝ) (n j : ℕ) (s t : ℝ), (∀ i, 0 ≤ κ i ∧ κ i ≤ 1) → 0 ≤ s → s ≤ t → t ≤ 1 →
      survH t κ n j ≤ survH s κ n j) ∧
  -- (G) grid certificates
  (∀ (S F : ℝ → ℝ) (U : ℝ) (ts : List ℝ),
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s) →
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t) →
      (∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t) →
      GridCert S F U ts → ∀ t, 0 ≤ t → t ≤ 1 → S t * F t ≤ U) ∧
  -- (F) honest-free floor
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ),
      IsKernel M → IsDist PH → 1 ≤ N → (∃ x, Bad x) →
      (∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b t ≤ U) ∧
  -- (X) exactness at L = 1
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ),
      IsKernel M → IsDist PH → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N →
      (∃ x, Bad x) → (∀ x, Bad x → ∀ z, M x z ≤ push M PH z) →
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ↔
       (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b t ≤ U))) ∧
  -- (S1) stratified certificate
  (∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 →
      (∀ x, Bad x → c x ∈ Es) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → binCDF m sc t * capB r b t ≤ U) →
      stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U) ∧
  -- (S2) stratified exactness under exact class decoding
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (g : Z → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ),
      IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → 0 ≤ r → r ≤ 1 → 1 ≤ b → 1 ≤ N →
      (∃ x, Bad x) → (∀ x, Bad x → c x ∈ Es) →
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U) ↔
       (∀ t : ℝ, 0 ≤ t → t ≤ 1 → binCDF m sc t * capB r b t ≤ U)))

/-- the 14-point grid used by the Witness -/
noncomputable def witnessGrid : List ℝ :=
  [0, 7/100, 9/100, 1/10, 11/100, 3/25, 13/100, 7/50, 3/20, 4/25, 9/50, 11/50, 33/100, 1]

/-- Non-vacuity and the certificate workflow, at m = n_h = 12, s_c = n_s = 1, r = 1, b = N = 1, X = Z = C = Bool,
Bad = {true}, identity view kernel (exact class decoding; for the halting protocol, honeypots are the point mass on
`true`, so L = 1).
- A 14-point grid certificates t·binCDF(12, 1, t) ≤ 3/40 on [0, 1]; at t = 1/8 the value is ≥ 17/250.
- So, at this instance, every colluding pair has risk ≤ 3/40 = 0.075, in the stratified design AND in the halting
  protocol, and an explicit pair has risk ≥ 17/250 = 0.068. The counting bound is 2/13 ≈ 0.154. -/
def Witness : Prop :=
  GridCert (fun t => binCDF 12 1 t) (fun t => capB 1 1 t) (3/40) witnessGrid ∧
  (17/250 : ℝ) ≤ binCDF 12 1 (1/8) * capB 1 1 (1/8) ∧
  (3/40 : ℝ) < (1 - 1) + 1 * (((1 : ℝ) + 1) / ((12 : ℝ) + 1)) ∧
  IsKernel witnessK ∧ (∀ e z : Bool, witnessK e z ≠ 0 → id z = e) ∧
  (∀ x : Bool, x = true → ∀ z, witnessK x z ≤ push witnessK (fun x => if x = true then 1 else 0) z) ∧
  (∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Bool → ℝ) (π : Ω → Hist Bool Bool → Bool → ℝ),
      IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      stratProtocolCat (fun x : Bool => x = true) witnessK id Finset.univ 12 1 1 1 1 ρ φ π ≤ 3/40 ∧
      protocolCat (fun x : Bool => x = true) witnessK (fun x => if x = true then 1 else 0)
        (hardKill 1) 12 1 1 1 ρ φ π ≤ 3/40) ∧
  (17/250 : ℝ) ≤ stratProtocolCat (fun x : Bool => x = true) witnessK id Finset.univ 12 1 1 1 1
      (fun _ : Unit => 1) (fun _ z => if z = true then 1/8 else 0) (fun _ _ x => if x = true then 1 else 0) ∧
  (17/250 : ℝ) ≤ protocolCat (fun x : Bool => x = true) witnessK (fun x => if x = true then 1 else 0)
      (hardKill 1) 12 1 1 1 (fun _ : Unit => 1) (fun _ _ => 1/8) (fun _ _ x => if x = true then 1 else 0)

end PL_UMCERTF1
