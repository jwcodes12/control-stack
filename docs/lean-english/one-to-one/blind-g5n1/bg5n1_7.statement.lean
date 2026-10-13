namespace PL_bg5n1_7
open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
open scoped BigOperators

def Back_sc21_adaptive_recall : Prop :=
  ∀ (N B k : ℕ) (r : ℝ) (Y : Type) [Fintype Y]
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ),
    B ≤ N → 0 ≤ r → r ≤ 1 →
    (∀ g, IsDist (σ g)) →
    (∀ S ∈ randomSchedules N B, ∀ h yo, 0 ≤ K S h yo) →
    (∀ S ∈ randomSchedules N B, ∀ h,
      (∑ y, ∑ o, K S h (y, o)) ≤ 1) →
    (∀ S ∈ randomSchedules N B, ∀ h a,
      (∑ y, ∑ f : Bool, K S h (y, (a, (), f))) ≤
        σ (h.map Prod.snd) a) →
    (∀ S ∈ randomSchedules N B, ∀ h a,
      (∑ y, K S h (y, (a, (), false))) ≤
        σ (h.map Prod.snd) a *
          (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) →
    (∑ S ∈ randomSchedules N B,
      (Nat.choose N B : ℝ)⁻¹ * val (K S) (recallSucc (N := N) k) N []) ≤
      hypMiss N B k r

def HBack (N B k : ℕ) (r : ℝ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) : Prop :=
  (B ≤ N) ∧
  (0 ≤ r) ∧
  (r ≤ 1) ∧
  (∀ g, IsDist (σ g)) ∧
  (∀ S ∈ randomSchedules N B, ∀ h yo, 0 ≤ K S h yo) ∧
  (∀ S ∈ randomSchedules N B, ∀ h, (∑ y, ∑ o, K S h (y, o)) ≤ 1) ∧
  (∀ S ∈ randomSchedules N B, ∀ h a, (∑ y, ∑ f : Bool, K S h (y, (a, (), f))) ≤ σ (h.map Prod.snd) a) ∧
  (∀ S ∈ randomSchedules N B, ∀ h a, (∑ y, K S h (y, (a, (), false))) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1))
def HOrig (N B k : ℕ) (r : ℝ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) : Prop :=
  (B ≤ N) ∧
  (0 ≤ r) ∧
  (r ≤ 1) ∧
  (∀ g, IsDist (σ g)) ∧
  (∀ S ∈ randomSchedules N B, ∀ h yo, 0 ≤ K S h yo) ∧
  (∀ S ∈ randomSchedules N B, ∀ h, (∑ z, K S h z) ≤ 1) ∧
  (∀ S ∈ randomSchedules N B, ∀ h a, (∑ y, K S h (y, (a, (), false))) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1))
noncomputable def BackAt (N B k : ℕ) (r : ℝ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) : Prop :=
  (∑ S ∈ randomSchedules N B, (Nat.choose N B : ℝ)⁻¹ * val (K S) (recallSucc (N := N) k) N []) ≤ hypMiss N B k r
noncomputable def OrigAt (N B k : ℕ) (r : ℝ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) : Prop :=
  (∑ S : Finset (Fin N), pU N B S * val (K S) (recallSucc (N := N) k) N []) ≤ hypMiss N B k r

noncomputable def wSigma (_ : List (AOut Unit)) (_ : Bool) : ℝ := 1/2
noncomputable def wKernel (_ : Finset (Fin 2)) (_ : List (Unit × AOut Unit)) (_ : Unit × AOut Unit) : ℝ := 1/4
noncomputable def cSigma (_ : List (AOut Unit)) (a : Bool) : ℝ := if a = false then 1 else 0
noncomputable def cKernel (_ : Finset (Fin 2)) (_ : List (Unit × AOut Unit)) (z : Unit × AOut Unit) : ℝ := if z.2.1 = true ∧ z.2.2.2 = true then 1 else 0
def StrictScope : Prop := HOrig 2 1 1 (1/2) Unit cKernel cSigma ∧ ¬ HBack 2 1 1 (1/2) Unit cKernel cSigma
def Witness : Prop := HBack 2 1 1 (1/2) Unit wKernel wSigma ∧ wKernel {0} [] ((), (true, (), false)) > 0

def Claim : Prop :=
  (Back_sc21_adaptive_recall ↔ ∀ (N B k : ℕ) (r : ℝ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ), HBack N B k r Y K σ → BackAt N B k r Y K σ) ∧
  (∀ (N B k : ℕ) (r : ℝ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ), HBack N B k r Y K σ → HOrig N B k r Y K σ) ∧
  (∀ (N B k : ℕ) (r : ℝ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ), HBack N B k r Y K σ → (BackAt N B k r Y K σ ↔ OrigAt N B k r Y K σ)) ∧
  (∀ (N B k : ℕ) (r : ℝ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ), (HOrig N B k r Y K σ → OrigAt N B k r Y K σ) → (HBack N B k r Y K σ → BackAt N B k r Y K σ)) ∧
  StrictScope
end PL_bg5n1_7
