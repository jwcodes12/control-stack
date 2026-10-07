-- Replacement statement file; the supplied reviewed dependencies are in scope.
namespace PL_UMNOGOF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

/-- A fixed submission at every history, with no strategy randomness. -/
noncomputable def submit {X Z : Type} (xs : X) :
    Unit → Hist X Z → X → ℝ := by
  classical
  exact fun _ _ x => if x = xs then 1 else 0

def DeterministicRule {Z : Type} (φ : Unit → Z → ℝ) : Prop :=
  ∀ ω z, φ ω z = 0 ∨ φ ω z = 1

def classMonitor {Z C : Type} [DecidableEq C] (g : Z → C) (e : C) (t : ℝ) :
    Unit → Z → ℝ := fun _ z => if g z = e then t else 0

def Claim : Prop :=
  -- One deterministic pair works for every valid shutdown schedule and setting.
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (c : X → C) (PH : X → ℝ) (S : Finset X),
      IsKernel M → ContentPreserving M c → IsDist PH →
      (∀ x ∈ S, Bad x) → Set.InjOn c (S : Set X) → 0 < S.card →
      ∃ (φ : Unit → Z → ℝ) (π : Unit → Hist X Z → X → ℝ),
        (∀ ω, IsRule (φ ω)) ∧
        (∀ ω h, IsDist (π ω h)) ∧
        DeterministicRule φ ∧
        (∃ xs ∈ S, π = submit (Z := Z) xs) ∧
        (∀ (nh : ℕ) (κ : ℕ → ℝ) (r : ℝ) (b N : ℕ),
          (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N →
          (1 - 1 / (S.card : ℝ)) ^ nh ≤
            protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) φ π)) ∧
  -- For each t, a rule and the fixed bad generator attain the formula uniformly.
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
      (c : X → C) (PH : X → ℝ) (xs : X) (t : ℝ),
      IsKernel M → ContentPreserving M c → IsDist PH →
      Bad xs → 0 ≤ t → t ≤ 1 →
      ∃ (φ : Unit → Z → ℝ) (π : Unit → Hist X Z → X → ℝ),
        (∀ ω, IsRule (φ ω)) ∧
        (∀ ω h, IsDist (π ω h)) ∧
        π = submit (Z := Z) xs ∧
        (∀ nh ns b N : ℕ, 1 ≤ N →
          protocolCat Bad M PH (hardKill ns) nh 1 b N
              (fun _ : Unit => 1) φ π =
            t * binCDF nh ns (t * contentLaw c PH (c xs))))

def witnessM (x z : Fin 4) : ℝ := if z = x then 1 else 0
noncomputable def witnessPH (_ : Fin 4) : ℝ := 1 / 4
def witnessBad (_ : Fin 4) : Prop := True
instance : DecidablePred witnessBad := fun _ => isTrue True.intro
def witnessS : Finset (Fin 4) := Finset.univ

/-- All hypotheses, strategy validity, and two actual protocol values. -/
def Witness : Prop :=
  IsKernel witnessM ∧
  ContentPreserving witnessM (id : Fin 4 → Fin 4) ∧
  IsDist witnessPH ∧
  (∀ x ∈ witnessS, witnessBad x) ∧
  Set.InjOn (id : Fin 4 → Fin 4) (witnessS : Set (Fin 4)) ∧
  witnessS.card = 4 ∧ 0 < witnessS.card ∧
  witnessBad (2 : Fin 4) ∧
  (∀ j, 0 ≤ hardKill 0 j ∧ hardKill 0 j ≤ 1) ∧
  0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 ∧ 1 ≤ (1 : ℕ) ∧
  0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) ≤ 1 ∧
  contentLaw (id : Fin 4 → Fin 4) witnessPH 2 = 1 / 4 ∧
  (∀ ω, IsRule (classMonitor (id : Fin 4 → Fin 4) 2 1 ω)) ∧
  DeterministicRule (classMonitor (id : Fin 4 → Fin 4) 2 1) ∧
  (∀ ω, IsRule (classMonitor (id : Fin 4 → Fin 4) 2 (1 / 2) ω)) ∧
  (∀ ω h, IsDist (submit (Z := Fin 4) (2 : Fin 4) ω h)) ∧
  (1 - 1 / (witnessS.card : ℝ)) ^ 2 = 9 / 16 ∧
  protocolCat witnessBad witnessM witnessPH (hardKill 0) 2 1 1 1
      (fun _ : Unit => 1) (classMonitor (id : Fin 4 → Fin 4) 2 1)
      (submit (Z := Fin 4) (2 : Fin 4)) = 9 / 16 ∧
  protocolCat witnessBad witnessM witnessPH (hardKill 0) 2 1 1 1
      (fun _ : Unit => 1) (classMonitor (id : Fin 4 → Fin 4) 2 (1 / 2))
      (submit (Z := Fin 4) (2 : Fin 4)) = 49 / 128 ∧
  (1 / 2 : ℝ) * binCDF 2 0 ((1 / 2) * contentLaw (id : Fin 4 → Fin 4) witnessPH 2)
      = 49 / 128

end PL_UMNOGOF1
