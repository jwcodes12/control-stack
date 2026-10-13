namespace PL_bg5n1_5
open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
open scoped BigOperators

def Back_sc21_adaptive : Prop :=
  ∀ (N B k : ℕ) (σ : List (AOut Unit) → Bool → ℝ),
    B ≤ N → (∀ g, IsDist (σ g)) →
    (∑ S ∈ randomSchedules N B,
      (Nat.choose N B : ℝ)⁻¹ *
        val (hiddenK (N := N) σ S) (survInd k S) N []) ≤
      (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)

def HBack (N B k : ℕ) (σ : List (AOut Unit) → Bool → ℝ) : Prop :=
  (B ≤ N) ∧
  (∀ g, IsDist (σ g))
def HOrig (N B k : ℕ) (σ : List (AOut Unit) → Bool → ℝ) : Prop :=
  (B ≤ N) ∧
  (∀ g, IsDist (σ g))
noncomputable def BackAt (N B k : ℕ) (σ : List (AOut Unit) → Bool → ℝ) : Prop :=
  (∑ S ∈ randomSchedules N B, (Nat.choose N B : ℝ)⁻¹ * val (hiddenK (N := N) σ S) (survInd k S) N []) ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
noncomputable def OrigAt (N B k : ℕ) (σ : List (AOut Unit) → Bool → ℝ) : Prop :=
  (∑ S : Finset (Fin N), (if S ∈ randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (hiddenK (N := N) σ S) (survInd k S) N []) ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)

noncomputable def wSigma (_ : List (AOut Unit)) (_ : Bool) : ℝ := 1/2
def Witness : Prop := HBack 2 1 1 wSigma ∧ wSigma [] true > 0 ∧ wSigma [] false > 0

def Claim : Prop :=
  (Back_sc21_adaptive ↔ ∀ (N B k : ℕ) (σ : List (AOut Unit) → Bool → ℝ), HBack N B k σ → BackAt N B k σ) ∧
  (∀ (N B k : ℕ) (σ : List (AOut Unit) → Bool → ℝ), HBack N B k σ ↔ HOrig N B k σ) ∧
  (∀ (N B k : ℕ) (σ : List (AOut Unit) → Bool → ℝ), HBack N B k σ → (BackAt N B k σ ↔ OrigAt N B k σ))
end PL_bg5n1_5
