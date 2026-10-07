namespace PL_UMCERTF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 PL_UMSTRATF1

/-! Control stack, collusion layer (campaign UMCERT, v1 after the Reviewer A and Reviewer B design reviews): certificate
form of the halting-protocol bound (PL_UMPROTF1) and of the stratified bound (PL_UMSTRATF1). Depends on PL_UMPROTF1
and PL_UMSTRATF1.

The counting bounds (1 − r) + r·L·(n_s+1)/(n_h+1) and (1 − r) + r·(s_c+1)/(m+1) use the Markov-type inequality
h·binCDF(n, s, h) ≤ (s+1)/(n+1), which is loose: at m = 12, s_c = 1, r = 1 the counting bound is 2/13 ≈ 0.154 and the
worst case is about 0.0683. This campaign proves an exact reduction to one-shot pairs, sound one-dimensional upper
certificates over the honeypot pass rate t ∈ [0, 1], and finite grid certificates that check them with rational
arithmetic. The scalar certificate is also NECESSARY under the hypotheses of (X), (Xp) and (S2); for a general
mediator, or a general (e.g. hockey-stick) envelope, it is an upper bound only, and a grid adds further slack.

Notation. `capB r b a` is the value of one attack that passes the monitor with probability `a`: 1 − r + r·a when an
audit is available (b ≥ 1), and a when b = 0 (an unaffordable flag halts).

Claim.
(R) One-shot reduction (exact). For every valid shutdown schedule κ, every budget b and every horizon N ≥ 1: every
    colluding pair (shared finite seed, stateless monitor, history-dependent generator) has risk ≤ U iff every ONE-SHOT
    pair does: a fixed bad submission x attacked in the first round, with a stateless rule ψ and no seed. The one-shot
    value is survH(E_{M·PH} ψ)·capB(E_{M x} ψ). Scope: within this finite free-submission HALTING model, with a fixed
    stateless monitor rule, constant audit recall and absorbing outcomes, the generator's history dependence and
    finite shared-seed mixtures do not raise the worst case above an immediate fixed attack. The worst case depends
    only on (M, PH, κ, n_h, r, Bad) and on whether b = 0. It does NOT transfer to non-halting variants (there, burning
    the budget and then attacking can help) or to phase-aware monitors (FLAG every honeypot, PASS every attack: risk 1;
    excluded by the stateless-interface assumption A1).
(C) Envelope certificate (sound). If `env` bounds every bad view law's pass rate by a function of the honeypot pass
    rate (E_{M x} ψ ≤ env(E_{M·PH} ψ) for every rule ψ), and survH(t)·capB(min 1 (env t)) ≤ U for every t ∈ [0, 1],
    then every colluding pair has risk ≤ U.
(E) Envelopes from the two trusted-side hypotheses of UMPROT T3: L-domination gives env t = L·t; a hockey-stick bound
    hs_η ≤ δ gives env t = e^η·t + δ (UMHS T2).
(G0) Survival is antitone in the pass rate, for every schedule κ with values in [0, 1].
(G) Grid certificates. For S antitone and F monotone, both nonnegative on [0, 1], a list 0 = t_0 ≤ … ≤ t_K = 1 with
    S(t_i)·F(t_{i+1}) ≤ U for every i certifies S(t)·F(t) ≤ U on [0, 1].
(CG) End to end, halting protocol: for a monotone nonnegative envelope, a grid certificate for
    t ↦ survH(t), t ↦ capB(min 1 (env t)) bounds every colluding pair's risk.
(SG) End to end, stratified design: a grid certificate for t ↦ binCDF(m, s_c, t), t ↦ capB(t) bounds every
    colluding pair's risk.
(D) Refinement: the counting bounds of UMPROT T3 (hard slack, and soft slack κ ≡ 1/n_s) satisfy the certificate
    hypothesis at every t, for every b; so the best certificate is never worse than UMPROT T3.
(F) View-blind floor (a corollary of (R)(→); compare UMUSE (c')). For nonempty Bad and N ≥ 1, every universal
    certificate U satisfies survH(t)·capB(t) ≤ U for every t ∈ [0, 1], whatever the mediator and honeypot law. For hard
    slack with r = 1 or b = 0 this floor is max_t t·binCDF(n_h, n_s, t), the AOQL of the single-sampling plan
    (n_h, c = n_s) in the large-lot convention (Dodge–Romig); for r < 1, b ≥ 1 it is the audit-adjusted
    (1 − r)·OC(t) + r·AOQ(t).
(X) Exactness at perfect honeypots. The hypothesis M x z ≤ push M PH z (L = 1) forces M x = push M PH for every bad x.
    Then (every colluding pair has risk ≤ U) iff (survH(t)·capB(t) ≤ U for every t ∈ [0, 1]).
(Xp) Exactness for content-only mediators with exact class decoding and minimum bad-class honeypot mass p (attained by
    some bad class): (every colluding pair has risk ≤ U) iff (survH(t)·capB(min 1 (t/p)) ≤ U for every t ∈ [0, 1]).
    At uniform honeypots over k classes (p = 1/k) this is the exact worst case of the global-slack design.
(S1) Stratified certificate. With a content-only mediator and class-aware hard slack, if binCDF(m, s_c, t)·capB(t) ≤ U
    for every t ∈ [0, 1], then every colluding pair has risk ≤ U. Every bad class must be tested (c x ∈ Es); no
    quantitative class-mass constant is needed, because per-class honeypots of class e have view law exactly K e
    (in-class domination with constant 1 by construction; constructibility, A9).
(S2) Stratified exactness, every budget. Conditional on exact class decoding, complete bad-class coverage, nonempty Bad
    and N ≥ 1, the certificate of (S1) is also necessary. So the worst case depends on the per-class parameters
    (m, s_c, r, b) and not on the detailed decodable kernel or on which classes are tested; the total honeypot cost
    m·|Es| still grows with the number of tested classes. Without decoding the iff fails (two identical class laws:
    0.0452 < 0.0683).

Scope. Same model and assumptions as PL_UMPROTF1 / PL_UMSTRATF1 (A1–A11; constant audit recall r; halting on an
unaffordable flag; upfront test; absorbing shutdown on a catch). Nothing here concerns adaptive testers, deferral or
usefulness. Classical mathematics (first-bad-decides, a reduction to one-shot pairs, monotone grid bounds, acceptance
sampling); the value is that design tables become Lean-checked certificates. -/

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
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (env : ℝ → ℝ) (U : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 0 ≤ U →
      (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ env (E (push M PH) ψ)) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b (min 1 (env t)) ≤ U) →
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
  -- (CG) end to end: grid certificate, halting protocol, monotone nonnegative envelope
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (env : ℝ → ℝ) (U : ℝ)
      (ts : List ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 →
      (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ env (E (push M PH) ψ)) →
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → env s ≤ env t) → (∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ env t) →
      GridCert (fun t => survH t κ nh 0) (fun t => capB r b (min 1 (env t))) U ts →
      protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ∧
  -- (SG) end to end: grid certificate, stratified design
  (∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ) (ts : List ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 →
      (∀ x, Bad x → c x ∈ Es) →
      GridCert (fun t => binCDF m sc t) (fun t => capB r b t) U ts →
      stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U) ∧
  -- (D) refinement: the counting bounds of UMPROT T3 satisfy the certificate hypothesis
  (∀ (n s b : ℕ) (r L t : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ L → 0 ≤ t → t ≤ 1 →
      survH t (hardKill s) n 0 * capB r b (min 1 (L * t)) ≤
        (1 - r) + r * (L * (((s : ℝ) + 1) / ((n : ℝ) + 1)))) ∧
  (∀ (n ns b : ℕ) (r L t : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ L → 1 ≤ ns → 0 ≤ t → t ≤ 1 →
      survH t (softKill ns) n 0 * capB r b (min 1 (L * t)) ≤
        (1 - r) + r * (L * ((ns : ℝ) / ((n : ℝ) + 1)))) ∧
  -- (F) view-blind floor
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ),
      IsKernel M → IsDist PH → 1 ≤ N → (∃ x, Bad x) →
      (∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b t ≤ U) ∧
  -- (X) exactness at perfect honeypots (L = 1)
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ),
      IsKernel M → IsDist PH → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N →
      (∃ x, Bad x) → (∀ x, Bad x → ∀ z, M x z ≤ push M PH z) →
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ↔
       (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b t ≤ U))) ∧
  -- (Xp) exactness for decodable content-only mediators with minimum bad-class honeypot mass p
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (g : Z → C) (PH : X → ℝ) (p : ℝ)
      (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ),
      IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → IsDist PH → 0 < p →
      (∀ x, Bad x → p ≤ contentLaw c PH (c x)) → (∃ x, Bad x ∧ contentLaw c PH (c x) = p) →
      (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N →
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad (fun x => K (c x)) PH κ nh r b N ρ φ π ≤ U) ↔
       (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b (min 1 ((1 / p) * t)) ≤ U))) ∧
  -- (S1) stratified certificate
  (∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 →
      (∀ x, Bad x → c x ∈ Es) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → binCDF m sc t * capB r b t ≤ U) →
      stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U) ∧
  -- (S2) stratified exactness under exact class decoding, every budget
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (g : Z → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ),
      IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → 0 ≤ r → r ≤ 1 → 1 ≤ N →
      (∃ x, Bad x) → (∀ x, Bad x → c x ∈ Es) →
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U) ↔
       (∀ t : ℝ, 0 ≤ t → t ≤ 1 → binCDF m sc t * capB r b t ≤ U)))

/-- fixture (i): 24 points; certifies t·binCDF(12, 1, t) ≤ 7/100 -/
noncomputable def gridMain : List ℝ :=
  [0, 7/100, 87/1000, 97/1000, 13/125, 109/1000, 113/1000, 29/250, 119/1000, 61/500, 1/8, 16/125,
   131/1000, 67/500, 137/1000, 141/1000, 73/500, 19/125, 4/25, 43/250, 193/1000, 237/1000, 19/50, 1]

/-- fixture (ii): 23 points; certifies t·(1 − t/5)^100 ≤ 19/1000 (soft slack κ ≡ 1/5, n_h = 100) -/
noncomputable def gridSoft : List ℝ :=
  [0, 19/1000, 139/5000, 331/10000, 369/10000, 199/5000, 211/5000, 443/10000, 231/5000, 6/125, 249/5000,
   129/2500, 67/1250, 279/5000, 583/10000, 613/10000, 163/2500, 141/2000, 393/5000, 463/5000, 1231/10000,
   1149/5000, 1]

/-- fixture (iii): 14 points; certifies binCDF(30, 1, t)·(1/10 + (9/10)·min(1, 4t)) ≤ 17/100 -/
noncomputable def gridKink : List ℝ :=
  [0, 97/5000, 51/2000, 37/1250, 329/10000, 359/10000, 39/1000, 53/1250, 233/5000, 523/10000, 613/10000,
   393/5000, 317/2500, 1]

/-- the identity view kernel on Bool and the point mass on `true` -/
def idK (e z : Bool) : ℝ := if z = e then 1 else 0
def ptTrue (x : Bool) : ℝ := if x = true then 1 else 0

/-- Non-vacuity and the certificate workflow (computational facts only; the protocol consequences are corollaries
of (CG) and (SG)).
(i) m = n_h = 12, s_c = n_s = 1, r = 1, b = N = 1; X = Z = C = Bool, Bad = {true}, identity view kernel (exact class
    decoding; for the halting protocol honeypots are the point mass on `true`, so L = 1). A 24-point grid certifies
    7/100, below the counting bound 2/13 ≈ 0.154. Explicit pairs (view-blind for the halting protocol, decoded-class
    for the stratified design, both at t = 1/8) have risk ≥ 6833/100000. So the worst case of both designs lies in
    [0.06833, 0.07].
(ii) Soft slack κ ≡ 1/5, n_h = 100, L = r = 1: a 23-point grid certifies 19/1000, against the counting bound
    5/101 ≈ 0.0495; at t = 1/20 the curve is ≥ 18/1000.
(iii) Hard slack n_h = 30, n_s = 1, L = 4, r = 9/10, b = 1 (the min 1 (L·t) kink and imperfect recall): a 14-point
    grid certifies 17/100, against the counting bound 1/10 + (9/10)·4·2/31 ≈ 0.332; at t = 7/200 the curve is ≥ 16/100. -/
def Witness : Prop :=
  GridCert (fun t => binCDF 12 1 t) (fun t => capB 1 1 t) (7/100) gridMain ∧
  (6833/100000 : ℝ) ≤ binCDF 12 1 (1/8) * capB 1 1 (1/8) ∧
  (7/100 : ℝ) < (1 - 1) + 1 * (((1 : ℝ) + 1) / ((12 : ℝ) + 1)) ∧
  IsKernel idK ∧ (∀ e z : Bool, idK e z ≠ 0 → id z = e) ∧ IsDist ptTrue ∧
  (∀ x : Bool, x = true → ∀ z, idK x z ≤ push idK ptTrue z) ∧
  (6833/100000 : ℝ) ≤ stratProtocolCat (fun x : Bool => x = true) idK id Finset.univ 12 1 1 1 1
      (fun _ : Unit => 1) (fun _ z => if z = true then 1/8 else 0) (fun _ _ x => if x = true then 1 else 0) ∧
  (6833/100000 : ℝ) ≤ protocolCat (fun x : Bool => x = true) idK ptTrue (hardKill 1) 12 1 1 1
      (fun _ : Unit => 1) (fun _ _ => 1/8) (fun _ _ x => if x = true then 1 else 0) ∧
  GridCert (fun t => survH t (softKill 5) 100 0) (fun t => capB 1 1 (min 1 (1 * t))) (19/1000) gridSoft ∧
  (18/1000 : ℝ) ≤ survH (1/20) (softKill 5) 100 0 * capB 1 1 (min 1 (1 * (1/20))) ∧
  (19/1000 : ℝ) < (1 - 1) + 1 * (1 * ((5 : ℝ) / ((100 : ℝ) + 1))) ∧
  GridCert (fun t => survH t (hardKill 1) 30 0) (fun t => capB (9/10) 1 (min 1 (4 * t))) (17/100) gridKink ∧
  (16/100 : ℝ) ≤ survH (7/200) (hardKill 1) 30 0 * capB (9/10) 1 (min 1 (4 * (7/200))) ∧
  (17/100 : ℝ) < (1 - 9/10) + 9/10 * (4 * (((1 : ℝ) + 1) / ((30 : ℝ) + 1)))

end PL_UMCERTF1
