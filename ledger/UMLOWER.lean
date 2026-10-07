-- Replacement statement file; the supplied dependency namespaces are in scope.
namespace PL_UMLOWERF1
open Finset PL_UMHSF1 PL_UMPROTF1

noncomputable def designSurv {X Z : Type} [Fintype X] [Fintype Z]
    (n : ℕ) (D : (Fin n → X) → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ)
    (keep : (Fin n → X) → (Fin n → Bool) → ℝ) : ℝ :=
  ∑ xs : Fin n → X, D xs * ∑ pat : Fin n → Bool,
    (∏ i, (if pat i then ∑ z, M (xs i) z * φ z
      else 1 - ∑ z, M (xs i) z * φ z)) * keep xs pat

noncomputable def designProtocolCat {X Z Ω : Type}
    [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (n : ℕ) (D : (Fin n → X) → ℝ)
    (keep : (Fin n → X) → (Fin n → Bool) → ℝ)
    (r : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ)
    (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * designSurv n D M (φ ω) keep *
    cat Bad M (φ ω) (π ω) r b N 0 []

def Setup {X Z C : Type} [Fintype Z] [DecidableEq X]
    (Bad : X → Prop) (M : X → Z → ℝ) (c : X → C) (S : Finset X) : Prop :=
  IsKernel M ∧ ContentPreserving M c ∧
    (∀ x ∈ S, Bad x) ∧ Set.InjOn c (S : Set X) ∧ 0 < S.card

def TestSetup {X : Type} [Fintype X] (n ns : ℕ)
    (D : (Fin n → X) → ℝ)
    (keep : (Fin n → X) → (Fin n → Bool) → ℝ) : Prop :=
  IsDist D ∧ (∀ xs pat, 0 ≤ keep xs pat ∧ keep xs pat ≤ 1) ∧
    (∀ xs pat, (univ.filter (fun i => pat i = true)).card ≤ ns →
      keep xs pat = 1)

noncomputable def seedLaw {X : Type} [DecidableEq X] (S : Finset X) : X → ℝ :=
  fun ω => if ω ∈ S then 1 / (S.card : ℝ) else 0

def classRule {X Z C : Type} [DecidableEq C]
    (c : X → C) (g : Z → C) (t : ℝ) : X → Z → ℝ :=
  fun ω z => if g z = c ω then t else 0

def seedPolicy {X Z : Type} [DecidableEq X] : X → Hist X Z → X → ℝ :=
  fun ω _ x => if x = ω then 1 else 0

/- The decoder is fixed before the design, shutdown rule, recall, budget and t.
The seed law is uniform on S, the monitor passes precisely the seed's class
with probability t, and the generator always submits the seed's bad submission.
For n > 0, optimizing t gives at least min(1/2, |S|(ns+1)/(4n)).
For n = 0, t = 1 gives risk 1. No unconditional matching upper bound is asserted:
it requires the hypotheses of the separate upper theorem, saturation at 1,
and treatment of audit failures. -/
def Claim : Prop :=
  ∀ (X Z C : Type) [Fintype X] [Fintype Z]
    [DecidableEq X] [DecidableEq C]
    (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (c : X → C) (S : Finset X),
    Setup Bad M c S →
    ∃ g : Z → C, (∀ x z, M x z ≠ 0 → g z = c x) ∧
      ∀ (n ns : ℕ) (D : (Fin n → X) → ℝ)
        (keep : (Fin n → X) → (Fin n → Bool) → ℝ),
        TestSetup n ns D keep →
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          IsDist (seedLaw S) ∧
          (∀ ω, seedLaw S ω ≠ 0 → ω ∈ S) ∧
          (∀ ω, IsRule (classRule c g t ω)) ∧
          (∀ (ω : X) (h : Hist X Z), IsDist (seedPolicy ω h)) ∧
          ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N →
            t * (1 - t * (n : ℝ) /
              ((S.card : ℝ) * ((ns : ℝ) + 1))) ≤
              designProtocolCat Bad M n D keep r b N
                (seedLaw S) (classRule c g t) (seedPolicy (Z := Z))

def witnessM (x z : Fin 4) : ℝ := if z = x then 1 else 0
def witnessD (xs : Fin 4 → Fin 4) : ℝ := if xs = id then 1 else 0
def witnessKeep (_xs : Fin 4 → Fin 4) (pat : Fin 4 → Bool) : ℝ :=
  if (univ.filter (fun i => pat i = true)).card ≤ 0 then 1 else 0

def Witness : Prop :=
  Setup (fun _ : Fin 4 => True) witnessM id (univ : Finset (Fin 4)) ∧
  TestSetup 4 0 witnessD witnessKeep ∧
  (∀ x z : Fin 4, witnessM x z ≠ 0 → id z = id x) ∧
  IsDist (seedLaw (univ : Finset (Fin 4))) ∧
  (∀ ω : Fin 4, seedLaw (univ : Finset (Fin 4)) ω ≠ 0 →
    ω ∈ (univ : Finset (Fin 4))) ∧
  (∀ ω : Fin 4, IsRule (classRule id id (1/2) ω)) ∧
  (∀ (ω : Fin 4) (h : Hist (Fin 4) (Fin 4)),
    IsDist (seedPolicy ω h)) ∧
  (0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 ∧
    0 ≤ (1/2 : ℝ) ∧ (1/2 : ℝ) ≤ 1 ∧ (1 : ℕ) ≤ 1) ∧
  (1/2 : ℝ) * (1 - (1/2) * (4 : ℝ) /
    ((4 : ℝ) * ((0 : ℝ) + 1))) = 1/4 ∧
  designProtocolCat (fun _ : Fin 4 => True) witnessM 4 witnessD witnessKeep
    1 1 1 (seedLaw (univ : Finset (Fin 4))) (classRule id id (1/2))
    (seedPolicy (X := Fin 4) (Z := Fin 4)) = 1/4

end PL_UMLOWERF1
