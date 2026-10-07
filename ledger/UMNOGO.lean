namespace PL_UMNOGOF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

/-! Control stack, collusion layer (DESIGN.md v1 §3, campaign UMNOGO): the coverage no-go.
Depends on PL_UMPROTF1 (and PL_UMHSF1, PL_UMSURVF1).

Setting: free-submission model (the generator may choose the task); iid honeypots; global slack.
(b) No-go: let the mediator be content-preserving (a decoder recovers the content class from every
    possible view), and let Bad contain k ≥ 1 submissions with pairwise distinct classes.  Then for every
    honeypot law there is a colluding pair (deterministic monitor, deterministic generator) with
    P(uncaught catastrophe) ≥ (1 − 1/k)^{n_h}, for every slack, budget, audit recall and horizon
    N ≥ 1.  With many decodable classes (k ≫ n_h), no iid honeypot law helps.
(c) Exact attainment: for a bad submission whose class has honeypot mass p and every t ∈ [0,1], some
    colluding pair achieves exactly t · P(Bin(n_h, t·p) ≤ n_s) (hard slack, r = 1). -/

def Claim : Prop :=
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (PH : X → ℝ)
      (S : Finset X) (nh ns b N : ℕ) (r : ℝ),
      IsKernel M → ContentPreserving M c → IsDist PH → 0 ≤ r → r ≤ 1 → 1 ≤ N →
      (∀ x ∈ S, Bad x) → Set.InjOn c (S : Set X) → 0 < S.card →
      ∃ (φ : Unit → Z → ℝ) (π : Unit → Hist X Z → X → ℝ),
        (∀ ω, IsRule (φ ω)) ∧ (∀ ω h, IsDist (π ω h)) ∧
        (1 - 1 / (S.card : ℝ)) ^ nh ≤
          protocolCat Bad M PH (hardKill ns) nh r b N (fun _ => 1) φ π) ∧
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (PH : X → ℝ)
      (xs : X) (nh ns b N : ℕ) (t : ℝ),
      IsKernel M → ContentPreserving M c → IsDist PH → Bad xs → 1 ≤ N → 0 ≤ t → t ≤ 1 →
      ∃ (φ : Unit → Z → ℝ) (π : Unit → Hist X Z → X → ℝ),
        (∀ ω, IsRule (φ ω)) ∧ (∀ ω h, IsDist (π ω h)) ∧
        protocolCat Bad M PH (hardKill ns) nh 1 b N (fun _ => 1) φ π =
          t * binCDF nh ns (t * contentLaw c PH (c xs)))

/-- Non-vacuity: four distinct decodable bad classes (identity mediator on Fin 4), uniform honeypots,
two honeypots: the no-go value (1 − 1/4)^2 = 9/16 is far from 0; the identity mediator satisfies the
hypotheses; each class has honeypot mass 1/4. -/
def Witness : Prop :=
  (1 - 1 / (4 : ℝ)) ^ 2 = 9 / 16 ∧
  IsKernel (fun (x : Fin 4) (z : Fin 4) => if z = x then (1 : ℝ) else 0) ∧
  ContentPreserving (fun (x : Fin 4) (z : Fin 4) => if z = x then (1 : ℝ) else 0) id ∧
  IsDist (fun _ : Fin 4 => (1/4 : ℝ)) ∧
  contentLaw (id : Fin 4 → Fin 4) (fun _ => (1/4 : ℝ)) 2 = 1/4

end PL_UMNOGOF1
