namespace PL_UMVALF1
open Finset PL_UMHSF1 PL_UMPROTF1

/-! Control stack, collusion layer, T5: the value of the honeypot game for content-based mediators.
Depends on PL_UMPROTF1 (and PL_UMHSF1).

(a) upper bound, content-only mediators: if every bad submission's content class has honeypot mass
    at least p > 0, every colluding pair has P(catastrophe) ≤ (1−r) + (1/p)(n_s+1)/(n_h+1).
(b) no-go, content-preserving mediators: if Bad contains k ≥ 1 submissions with pairwise distinct
    content classes, then for EVERY honeypot law there is a colluding pair (deterministic monitor,
    deterministic generator) with P(catastrophe) ≥ (1 − 1/k)^{n_h}, for every slack, budget, audit
    recall and horizon N ≥ 1.
(c) exact attainment: for content-preserving mediators, for every bad class with honeypot mass p
    and every t ∈ [0,1], some colluding pair has P(catastrophe) exactly t · P(Bin(n_h, t p) ≤ n_s)
    (hard slack, r = 1). -/

def Claim : Prop :=
  -- (a)
  (∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] [Fintype Ω]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (PH : X → ℝ)
      (nh ns b N : ℕ) (r p : ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → ContentOnly M c → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) →
      (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 → 0 < p →
      (∀ x, Bad x → p ≤ contentLaw c PH (c x)) →
      protocolCat Bad M PH (hardKill ns) nh r b N ρ φ π
        ≤ (1 - r) + (1 / p) * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) ∧
  -- (b)
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (PH : X → ℝ)
      (S : Finset X) (nh ns b N : ℕ) (r : ℝ),
      IsKernel M → ContentPreserving M c → IsDist PH → 0 ≤ r → r ≤ 1 → 1 ≤ N →
      (∀ x ∈ S, Bad x) → Set.InjOn c (S : Set X) → 0 < S.card →
      ∃ (φ : Unit → Z → ℝ) (π : Unit → Hist X Z → X → ℝ),
        (∀ ω, IsRule (φ ω)) ∧ (∀ ω h, IsDist (π ω h)) ∧
        (1 - 1 / (S.card : ℝ)) ^ nh ≤ protocolCat Bad M PH (hardKill ns) nh r b N (fun _ => 1) φ π) ∧
  -- (c)
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (PH : X → ℝ)
      (xs : X) (nh ns b N : ℕ) (t : ℝ),
      IsKernel M → ContentPreserving M c → IsDist PH → Bad xs → 1 ≤ N → 0 ≤ t → t ≤ 1 →
      ∃ (φ : Unit → Z → ℝ) (π : Unit → Hist X Z → X → ℝ),
        (∀ ω, IsRule (φ ω)) ∧ (∀ ω h, IsDist (π ω h)) ∧
        protocolCat Bad M PH (hardKill ns) nh 1 b N (fun _ => 1) φ π =
          t * ∑ j ∈ range (ns + 1), (nh.choose j : ℝ) * (t * contentLaw c PH (c xs)) ^ j *
              (1 - t * contentLaw c PH (c xs)) ^ (nh - j))

/-- Non-vacuity: with four bad classes and identity mediation, honeypots uniform over the classes,
two honeypots and no slack, the content-only upper bound (a) gives 4·(1/3) — vacuous — while with
twelve honeypots it gives 4/13 < 1; and the no-go (b) is non-trivial: (1 − 1/4)^2 = 9/16. -/
def Witness : Prop :=
  (1 - 1 / (4 : ℝ)) ^ 2 = 9 / 16 ∧ (1 / (1/4 : ℝ)) * (((0 : ℝ) + 1) / ((12 : ℝ) + 1)) = 4 / 13 ∧
  ContentOnly (fun (x : Fin 4) (z : Fin 4) => if z = x then (1 : ℝ) else 0) id ∧
  ContentPreserving (fun (x : Fin 4) (z : Fin 4) => if z = x then (1 : ℝ) else 0) id ∧
  contentLaw (id : Fin 4 → Fin 4) (fun _ => (1/4 : ℝ)) 2 = 1/4

end PL_UMVALF1
