open scoped BigOperators
open ControlStack Finset
open ControlStack.Covert ControlStack.Leakage
open ControlStack.SC07Exfil
namespace PL_bg1n2_10

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

def FrozenBack : Prop :=
  ∀ (N B S q : ℕ) (r : ℝ) (Y : Type) [Fintype Y]
      (sigma : List (AOut Unit) → Bool → ℝ)
      (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ),
    B ≤ N →
    0 ≤ r → r ≤ 1 →
    (∀ g a, 0 ≤ sigma g a) →
    (∀ g, (∑ a, sigma g a) ≤ 1) →
    (∀ sched ∈ ControlStack.AuditBudget.randomSchedules N B,
      ∀ h z, 0 ≤ K sched h z) →
    (∀ sched ∈ ControlStack.AuditBudget.randomSchedules N B,
      ∀ h, (∑ y, ∑ o, K sched h (y, o)) ≤ 1) →
    (∀ sched ∈ ControlStack.AuditBudget.randomSchedules N B,
      ∀ h a,
        (∑ y, K sched h (y, (a, (), false))) ≤
          sigma (h.map Prod.snd) a *
            (if memN sched (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) →
    (∑ sched : Finset (Fin N), ControlStack.ReservedAudit.pU N B sched *
      val (K sched) (ControlStack.ReservedRecall.recallSucc (N := N) (ceilDiv S q)) N []) ≤
      ControlStack.ReservedRecall.hypMiss N B (ceilDiv S q) r


noncomputable def delta {A : Type} [Fintype A] [DecidableEq A] (a : A) : A → ℝ :=
  fun x => if x = a then 1 else 0

noncomputable def sigmaSub : List (AOut Unit) → Bool → ℝ := fun _ _ => 1 / 4
noncomputable def sigmaNorm : List (AOut Unit) → Bool → ℝ := fun _ _ => 1 / 2
noncomputable def testK (sigma : List (AOut Unit) → Bool → ℝ) :
    Finset (Fin 2) → List (Unit × AOut Unit) → Unit × AOut Unit → ℝ :=
  fun sched h z => if z.2.2.2 = false then
    sigma (h.map Prod.snd) z.2.1 *
      (if memN sched (h.map Prod.snd).length ∧ z.2.1 = true then 1 / 2 else 1)
    else 0

def BackHyp (N B S q : ℕ) (r : ℝ) (Y : Type) [Fintype Y]
    (sigma : List (AOut Unit) → Bool → ℝ)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) : Prop :=
  B ≤ N ∧ 0 ≤ r ∧ r ≤ 1 ∧
    (∀ g a, 0 ≤ sigma g a) ∧ (∀ g, (∑ a, sigma g a) ≤ 1) ∧
    (∀ sched ∈ ControlStack.AuditBudget.randomSchedules N B, ∀ h z, 0 ≤ K sched h z) ∧
    (∀ sched ∈ ControlStack.AuditBudget.randomSchedules N B, ∀ h, (∑ y, ∑ o, K sched h (y, o)) ≤ 1) ∧
    (∀ sched ∈ ControlStack.AuditBudget.randomSchedules N B, ∀ h a,
      (∑ y, K sched h (y, (a, (), false))) ≤ sigma (h.map Prod.snd) a *
      (if memN sched (h.map Prod.snd).length ∧ a = true then 1 - r else 1))

def OrigHyp (N B S q : ℕ) (r : ℝ) (Y : Type) [Fintype Y]
    (sigma : List (AOut Unit) → Bool → ℝ)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) : Prop :=
  B ≤ N ∧ 0 ≤ r ∧ r ≤ 1 ∧
    (∀ g, IsDist (sigma g)) ∧
    (∀ sched ∈ ControlStack.AuditBudget.randomSchedules N B, ∀ h z, 0 ≤ K sched h z) ∧
    (∀ sched ∈ ControlStack.AuditBudget.randomSchedules N B, ∀ h, (∑ z, K sched h z) ≤ 1) ∧
    (∀ sched ∈ ControlStack.AuditBudget.randomSchedules N B, ∀ h a,
      (∑ y, K sched h (y, (a, (), false))) ≤ sigma (h.map Prod.snd) a *
      (if memN sched (h.map Prod.snd).length ∧ a = true then 1 - r else 1))

def BackConclusion (N B S q : ℕ) (r : ℝ) (Y : Type) [Fintype Y]
    (sigma : List (AOut Unit) → Bool → ℝ)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) : Prop :=
  (∑ sched : Finset (Fin N), ControlStack.ReservedAudit.pU N B sched *
    val (K sched) (ControlStack.ReservedRecall.recallSucc (N := N) (ceilDiv S q)) N []) ≤
    ControlStack.ReservedRecall.hypMiss N B (ceilDiv S q) r

def OrigConclusion (N B S q : ℕ) (r : ℝ) (Y : Type) [Fintype Y]
    (sigma : List (AOut Unit) → Bool → ℝ)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) : Prop :=
  (∑ sched : Finset (Fin N), ControlStack.ReservedAudit.pU N B sched *
    val (K sched) (ControlStack.ReservedRecall.recallSucc (N := N) (ceilDiv S q)) N []) ≤
    ControlStack.ReservedRecall.hypMiss N B (ceilDiv S q) r

def BackAt (N B S q : ℕ) (r : ℝ) (Y : Type) [Fintype Y]
    (sigma : List (AOut Unit) → Bool → ℝ)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) : Prop := BackHyp N B S q r Y sigma K → BackConclusion N B S q r Y sigma K

def OrigAt (N B S q : ℕ) (r : ℝ) (Y : Type) [Fintype Y]
    (sigma : List (AOut Unit) → Bool → ℝ)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) : Prop := OrigHyp N B S q r Y sigma K → OrigConclusion N B S q r Y sigma K

def PointwiseClaim : Prop :=
  ∀ (N B S q : ℕ) (r : ℝ) (Y : Type) [Fintype Y]
    (sigma : List (AOut Unit) → Bool → ℝ)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ), (OrigHyp N B S q r Y sigma K → BackHyp N B S q r Y sigma K) ∧ (BackAt N B S q r Y sigma K → OrigAt N B S q r Y sigma K) ∧ (BackConclusion N B S q r Y sigma K ↔ OrigConclusion N B S q r Y sigma K)

def Witness : Prop :=
  BackHyp 2 1 1 1 (1 / 2) Unit sigmaSub (testK sigmaSub) ∧
    ¬ OrigHyp 2 1 1 1 (1 / 2) Unit sigmaSub (testK sigmaSub) ∧
    0 < sigmaSub [] true ∧ (∑ a, sigmaSub [] a) = 1 / 2 ∧
    OrigHyp 2 1 1 1 (1 / 2) Unit sigmaNorm (testK sigmaNorm)

def Original : Prop :=
  ∀  {N : ℕ} {Y : Type} [Fintype Y] (S q B : ℕ) (hB : B ≤ N) (r : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1)
    (K : Finset (Fin N) → List (Y × Leakage.AOut Unit) → Y × Leakage.AOut Unit → ℝ)
    (σ : List (Leakage.AOut Unit) → Bool → ℝ) (hσ : ∀ g, Covert.IsDist (σ g))
    (hK0 : ∀ T, T ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K T h z)
    (hK1 : ∀ T, T ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K T h z ≤ 1)
    (hrec : ∀ T, T ∈ AuditBudget.randomSchedules N B → ∀ h (a : Bool),
      ∑ y, K T h (y, (a, (), false)) ≤
        σ (h.map Prod.snd) a * (if Leakage.memN T (h.map Prod.snd).length ∧ a = true then 1 - r else 1)),
    ∑ T : Finset (Fin N), ReservedAudit.pU N B T * Leakage.val (K T) (ReservedRecall.recallSucc (N := N) (ceilDiv S q)) N []
      ≤ ReservedRecall.hypMiss N B (ceilDiv S q) r

def BackSchema : Prop := ∀ (N B S q : ℕ) (r : ℝ) (Y : Type) [Fintype Y]
    (sigma : List (AOut Unit) → Bool → ℝ)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ), BackAt N B S q r Y sigma K

def OrigSchema : Prop := ∀ (N B S q : ℕ) (r : ℝ) (Y : Type) [Fintype Y]
    (sigma : List (AOut Unit) → Bool → ℝ)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ), OrigAt N B S q r Y sigma K

def Claim : Prop :=
  (FrozenBack ↔ BackSchema) ∧ (Original ↔ OrigSchema) ∧ PointwiseClaim ∧ (FrozenBack → Original)

end PL_bg1n2_10
