namespace PL_UMSTRATF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

/-- Conditional on the shared seed, the per-class tests use independent samples and PASS coins. -/
def stratSurv {Z C : Type} [Fintype Z] (K : C → Z → ℝ) (Es : Finset C)
    (φ : Z → ℝ) (m sc : ℕ) : ℝ :=
  ∏ e ∈ Es, surv (K e) φ (hardKill sc) m 0

noncomputable def stratProtocolCat {X Z C Ω : Type}
    [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ)
    (c : X → C) (Es : Finset C) (m sc : ℕ) (r : ℝ) (b N : ℕ)
    (ρ : Ω → ℝ) (φ : Ω → Z → ℝ)
    (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * stratSurv K Es (φ ω) m sc *
    cat Bad (fun x => K (c x)) (φ ω) (π ω) r b N 0 []

/-- The counting upper bound and the explicit attainable curve.
The second conjunct does not assert tightness of the first conjunct. -/
def Claim : Prop :=
  (∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω]
      (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (Es : Finset C)
      (m sc b N : ℕ) (r : ℝ) (ρ : Ω → ℝ)
      (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) →
      (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 →
      (∀ x, Bad x → c x ∈ Es) →
      stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤
        (1 - r) + r * (((sc : ℝ) + 1) / ((m : ℝ) + 1))) ∧
  (∀ (X Z C : Type) [Fintype X] [Fintype Z]
      [DecidableEq C] [DecidableEq X]
      (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (g : Z → C)
      (Es : Finset C) (m sc b N : ℕ) (r t : ℝ) (x : X),
      IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) →
      Bad x → c x ∈ Es → 1 ≤ N → 1 ≤ b → 0 ≤ t → t ≤ 1 →
      stratProtocolCat Bad K c Es m sc r b N
          (fun _ : Unit => 1)
          (fun _ z => if g z = c x then t else 0)
          (fun _ _ x' => if x' = x then 1 else 0) =
        binCDF m sc t * (1 - r + r * t))

def witnessK (e z : Bool) : ℝ := if z = e then 1 else 0

noncomputable def witnessPhi : Unit → Bool → ℝ :=
  fun _ z => if z = true then 1 / 6 else 0

def witnessPi : Unit → Hist Bool Bool → Bool → ℝ :=
  fun _ _ x => if x = true then 1 else 0

/-- Two tested classes, a nonempty catastrophe set, exact decoding,
a valid colluding pair, and positive catastrophe probability below the bound.
All hypotheses of both Claim conjuncts are represented at this instance. -/
def Witness : Prop :=
  IsKernel witnessK ∧
  (∀ e z : Bool, witnessK e z ≠ 0 → id z = e) ∧
  IsDist (fun _ : Unit => (1 : ℝ)) ∧
  (∀ ω : Unit, IsRule (witnessPhi ω)) ∧
  (∀ (ω : Unit) (h : Hist Bool Bool), IsDist (witnessPi ω h)) ∧
  (∀ x : Bool, x = true → id x ∈ (Finset.univ : Finset Bool)) ∧
  (∃ x : Bool, x = true) ∧
  (true = true) ∧
  (id true ∈ (Finset.univ : Finset Bool)) ∧
  (Finset.univ : Finset Bool).card = 2 ∧
  (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 ∧
  (0 : ℝ) ≤ 1 / 6 ∧ (1 / 6 : ℝ) ≤ 1 ∧
  (1 : ℕ) ≤ 1 ∧
  (∀ z : Bool,
    witnessPhi () z = if id z = id true then (1 / 6 : ℝ) else 0) ∧
  (∀ (ω : Unit) (h : Hist Bool Bool) (x : Bool),
    witnessPi ω h x = if x = true then (1 : ℝ) else 0) ∧
  stratProtocolCat (fun x : Bool => x = true)
      witnessK id (Finset.univ : Finset Bool) 12 1 1 1 1
      (fun _ : Unit => 1) witnessPhi witnessPi =
    binCDF 12 1 (1 / 6) * (1 - 1 + 1 * (1 / 6 : ℝ)) ∧
  (1 - (1 : ℝ)) + 1 * (((1 : ℝ) + 1) / ((12 : ℝ) + 1)) = 2 / 13 ∧
  0 < stratProtocolCat (fun x : Bool => x = true)
      witnessK id (Finset.univ : Finset Bool) 12 1 1 1 1
      (fun _ : Unit => 1) witnessPhi witnessPi ∧
  stratProtocolCat (fun x : Bool => x = true)
      witnessK id (Finset.univ : Finset Bool) 12 1 1 1 1
      (fun _ : Unit => 1) witnessPhi witnessPi < (2 / 13 : ℝ)

end PL_UMSTRATF1
