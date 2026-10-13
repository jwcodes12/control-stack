namespace PL_bg5n1_6
open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
open scoped BigOperators

def Back_sc21_adaptive_content : Prop :=
  ∀ (N B k : ℕ) (Y : Type) [Fintype Y]
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ),
    B ≤ N →
    (∀ g, IsDist (σ g)) →
    (∀ S ∈ randomSchedules N B, ∀ h yo, 0 ≤ K S h yo) →
    (∀ S ∈ randomSchedules N B, ∀ h,
      (∑ y, ∑ o, K S h (y, o)) ≤ 1) →
    (∀ S ∈ randomSchedules N B, ∀ h a,
      (∑ y, ∑ f : Bool, K S h (y, (a, (), f))) ≤
        σ (h.map Prod.snd) a) →
    (∑ S ∈ randomSchedules N B,
      (Nat.choose N B : ℝ)⁻¹ * val (K S) (successInd k S) N []) ≤
      (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)

def HBack (N B k : ℕ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) : Prop :=
  (B ≤ N) ∧
  (∀ g, IsDist (σ g)) ∧
  (∀ S ∈ randomSchedules N B, ∀ h yo, 0 ≤ K S h yo) ∧
  (∀ S ∈ randomSchedules N B, ∀ h, (∑ y, ∑ o, K S h (y, o)) ≤ 1) ∧
  (∀ S ∈ randomSchedules N B, ∀ h a, (∑ y, ∑ f : Bool, K S h (y, (a, (), f))) ≤ σ (h.map Prod.snd) a)
def HOrig (N B k : ℕ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) : Prop :=
  (B ≤ N) ∧
  (∀ g, IsDist (σ g)) ∧
  (∀ S ∈ randomSchedules N B, ∀ h yo, 0 ≤ K S h yo) ∧
  (∀ S ∈ randomSchedules N B, ∀ h, (∑ z, K S h z) ≤ 1) ∧
  (∀ S ∈ randomSchedules N B, ∀ h a, (∑ y, ∑ f : Bool, K S h (y, (a, (), f))) ≤ σ (h.map Prod.snd) a)
noncomputable def BackAt (N B k : ℕ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) : Prop :=
  (∑ S ∈ randomSchedules N B, (Nat.choose N B : ℝ)⁻¹ * val (K S) (successInd k S) N []) ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
noncomputable def OrigAt (N B k : ℕ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) : Prop :=
  (∑ S : Finset (Fin N), pU N B S * val (K S) (successInd k S) N []) ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)

noncomputable def wSigma (_ : List (AOut Unit)) (_ : Bool) : ℝ := 1/2
noncomputable def wKernel (_ : Finset (Fin 2)) (_ : List (Unit × AOut Unit)) (z : Unit × AOut Unit) : ℝ := if z.2.2.2 = false then 1/2 else 0
def Witness : Prop := HBack 2 1 1 Unit wKernel wSigma ∧ wKernel {0} [] ((), (true, (), false)) > 0

def Claim : Prop :=
  (Back_sc21_adaptive_content ↔ ∀ (N B k : ℕ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ), HBack N B k Y K σ → BackAt N B k Y K σ) ∧
  (∀ (N B k : ℕ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ), HBack N B k Y K σ ↔ HOrig N B k Y K σ) ∧
  (∀ (N B k : ℕ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ), HBack N B k Y K σ → (BackAt N B k Y K σ ↔ OrigAt N B k Y K σ))
end PL_bg5n1_6
