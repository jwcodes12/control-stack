namespace PL_UMLOWERF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

/-! Control stack, collusion layer (campaign UMLOWER): a design-free converse.
Depends on PL_UMPROTF1 (and PL_UMHSF1, PL_UMSURVF1).

Setting.
- The mediator has an exact decoder for a content class (`ContentPreserving`). Bad contains k ≥ 1
  submissions with pairwise distinct classes.
- Blue may use ANY honeypot design: an arbitrary joint law `D` over n-tuples of submissions. It may be
  correlated, stratified by class, deterministic, or anything else, but it is chosen independently of the
  colluders' seed.
- Each honeypot is mediated and judged in a fresh, stateless monitor call. So, given the tuple, the PASS
  events are independent, with probabilities `a x = ∑ z, M x z * φ z`.
- Blue may use ANY shutdown rule `keep` (the probability of keeping the monitor, given the tuple and the
  PASS pattern) that never shuts down a monitor with at most `ns` misses. Global hard slack and
  class-aware slack are special cases.

Claim. For every audit recall r ∈ [0,1] and every t ∈ [0,1], a seed-randomised colluding pair exists
against which:
  P(survive the test, then uncaught catastrophe) ≥ t · (1 − t·n / (k·(ns+1))).
- The pair: the seed is uniform on the k bad submissions; the monitor PASSes views of the seed's class
  with probability t; the generator submits the seed's submission.
- Proof idea: averaged over the seed, the expected number of misses is ≤ t·n/k; Markov's inequality.
- At t = min(1, k(ns+1)/(2n)) this is ≥ k(ns+1)/(4n), or ≥ 1/2 when 2n ≤ k(ns+1).
- Together with the stratified upper bound (PL_UMSTRATF1, m = n/k per class), honeypot budget per
  distinguishable class is necessary and sufficient up to a constant: risk = Θ(k(ns+1)/n). -/

/-- probability of keeping the monitor through the honeypot test under design `D` and rule `keep` -/
noncomputable def designSurv {X Z : Type} [Fintype X] [Fintype Z] (n : ℕ) (D : (Fin n → X) → ℝ)
    (M : X → Z → ℝ) (φ : Z → ℝ) (keep : (Fin n → X) → (Fin n → Bool) → ℝ) : ℝ :=
  ∑ xs : Fin n → X, D xs * ∑ pat : Fin n → Bool,
    (∏ i, (if pat i then ∑ z, M (xs i) z * φ z else 1 - ∑ z, M (xs i) z * φ z)) * keep xs pat

/-- P(survive the test, then uncaught catastrophe) under design `D` and rule `keep` -/
noncomputable def designProtocolCat {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (n : ℕ) (D : (Fin n → X) → ℝ)
    (keep : (Fin n → X) → (Fin n → Bool) → ℝ) (r : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ)
    (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * designSurv n D M (φ ω) keep * cat Bad M (φ ω) (π ω) r b N 0 []

def Claim : Prop :=
  ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq X] [DecidableEq C]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X)
    (n ns b N : ℕ) (D : (Fin n → X) → ℝ) (keep : (Fin n → X) → (Fin n → Bool) → ℝ) (r t : ℝ),
    IsKernel M → ContentPreserving M c → IsDist D →
    (∀ xs pat, 0 ≤ keep xs pat ∧ keep xs pat ≤ 1) →
    (∀ xs pat, (univ.filter (fun i => pat i = true)).card ≤ ns → keep xs pat = 1) →
    (∀ x ∈ S, Bad x) → Set.InjOn c (S : Set X) → 0 < S.card → 1 ≤ N → 0 ≤ r → r ≤ 1 →
    0 ≤ t → t ≤ 1 →
    ∃ (ρ : X → ℝ) (φ : X → Z → ℝ) (π : X → Hist X Z → X → ℝ),
      IsDist ρ ∧ (∀ ω, ρ ω ≠ 0 → ω ∈ S) ∧ (∀ ω, IsRule (φ ω)) ∧ (∀ ω h, IsDist (π ω h)) ∧
      t * (1 - t * (n : ℝ) / ((S.card : ℝ) * ((ns : ℝ) + 1))) ≤
        designProtocolCat Bad M n D keep r b N ρ φ π

/-- Non-vacuity and tightness: four distinct decodable bad classes (identity mediator on Fin 4), one
honeypot of each class (a stratified deterministic design, n = 4), no slack. The bound at t = 1/2 is
1/2 · (1 − (1/2)·4/(4·1)) = 1/4, and the seed-randomised colluder attains exactly 1/4: each seed survives
its class's single honeypot with probability 1/2, then its attack passes with probability 1/2. -/
def Witness : Prop :=
  IsKernel (fun (x : Fin 4) (z : Fin 4) => if z = x then (1 : ℝ) else 0) ∧
  ContentPreserving (fun (x : Fin 4) (z : Fin 4) => if z = x then (1 : ℝ) else 0) id ∧
  IsDist (fun xs : Fin 4 → Fin 4 => if xs = id then (1 : ℝ) else 0) ∧
  (∀ (xs : Fin 4 → Fin 4) (pat : Fin 4 → Bool),
      (univ.filter (fun i => pat i = true)).card ≤ 0 →
      (if (univ.filter (fun i => pat i = true)).card ≤ 0 then (1 : ℝ) else 0) = 1) ∧
  (1/2 : ℝ) * (1 - (1/2) * (4 : ℝ) / ((4 : ℝ) * ((0 : ℝ) + 1))) = 1/4 ∧
  -- the seed-randomised colluder attains the bound with equality in this design
  designProtocolCat (X := Fin 4) (Z := Fin 4) (Ω := Fin 4) (fun _ => True)
      (fun x z => if z = x then 1 else 0) 4 (fun xs => if xs = id then 1 else 0)
      (fun _ pat => if (univ.filter (fun i => pat i = true)).card ≤ 0 then 1 else 0) 1 1 1
      (fun _ => 1/4) (fun ω z => if z = ω then 1/2 else 0) (fun ω _ x => if x = ω then 1 else 0)
    = 1/4

end PL_UMLOWERF1
