open scoped BigOperators
open ControlStack Finset
open ControlStack.Covert ControlStack.Leakage
open ControlStack.SC07Exfil
namespace PL_bg1n2_9

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

def FrozenBack : Prop :=
  ∀ (P : Type) [Fintype P] (S q : ℕ) (pr : ℝ)
      (plans : P → List ℕ) (w : P → ℝ) (c : ℕ → ℝ),
    0 < q →
    0 ≤ pr → pr ≤ 1 →
    (∀ i, pr ≤ c i) →
    (∀ i, c i ≤ 1) →
    ControlStack.Covert.IsDist w →
    (∑ p, if S ≤ (capped q (plans p)).sum
      then w p * survive c (capped q (plans p)) 0 else 0) ≤
      (1 - pr) ^ ceilDiv S q


noncomputable def delta {A : Type} [Fintype A] [DecidableEq A] (a : A) : A → ℝ :=
  fun x => if x = a then 1 else 0


def BackHyp (P : Type) [Fintype P] (S q : ℕ) (pr : ℝ)
    (plans : P → List ℕ) (w : P → ℝ) (c : ℕ → ℝ) : Prop :=
  0 < q ∧ 0 ≤ pr ∧ pr ≤ 1 ∧ (∀ i, pr ≤ c i) ∧ (∀ i, c i ≤ 1) ∧ IsDist w

def OrigHyp (P : Type) [Fintype P] (S q : ℕ) (pr : ℝ)
    (plans : P → List ℕ) (w : P → ℝ) (c : ℕ → ℝ) : Prop :=
  0 < q ∧ 0 ≤ pr ∧ pr ≤ 1 ∧ (∀ i, pr ≤ c i ∧ c i ≤ 1) ∧ (∀ p, 0 ≤ w p) ∧ (∑ p, w p) = 1

def BackConclusion (P : Type) [Fintype P] (S q : ℕ) (pr : ℝ)
    (plans : P → List ℕ) (w : P → ℝ) (c : ℕ → ℝ) : Prop :=
  (∑ p, if S ≤ (capped q (plans p)).sum
    then w p * survive c (capped q (plans p)) 0 else 0) ≤ (1 - pr) ^ ceilDiv S q

def OrigConclusion (P : Type) [Fintype P] (S q : ℕ) (pr : ℝ)
    (plans : P → List ℕ) (w : P → ℝ) (c : ℕ → ℝ) : Prop :=
  (∑ p, w p * (if S ≤ (capped q (plans p)).sum
    then survive c (capped q (plans p)) 0 else 0)) ≤ (1 - pr) ^ ceilDiv S q

def BackAt (P : Type) [Fintype P] (S q : ℕ) (pr : ℝ)
    (plans : P → List ℕ) (w : P → ℝ) (c : ℕ → ℝ) : Prop := BackHyp P S q pr plans w c → BackConclusion P S q pr plans w c

def OrigAt (P : Type) [Fintype P] (S q : ℕ) (pr : ℝ)
    (plans : P → List ℕ) (w : P → ℝ) (c : ℕ → ℝ) : Prop := OrigHyp P S q pr plans w c → OrigConclusion P S q pr plans w c

def ComponentwiseClaim : Prop :=
  ∀ (P : Type) [Fintype P] (S q : ℕ) (pr : ℝ)
    (plans : P → List ℕ) (w : P → ℝ) (c : ℕ → ℝ), (BackHyp P S q pr plans w c ↔ OrigHyp P S q pr plans w c) ∧ (BackConclusion P S q pr plans w c ↔ OrigConclusion P S q pr plans w c)

def Witness : Prop :=
  BackHyp Bool 3 2 (1 / 2) (fun _ => [2, 0, 1]) (fun _ => 1 / 2) (fun _ => 1 / 2) ∧
    (capped 2 [2, 0, 1]).sum = 3 ∧ survive (fun _ => (1 / 2 : ℝ)) (capped 2 [2, 0, 1]) 0 = 1 / 4

def Original : Prop :=
  ∀  {Ω : Type} [Fintype Ω] (S q : ℕ) (hq : 0 < q) (c : ℕ → ℝ) (pr : ℝ)
    (hc : ∀ i, pr ≤ c i ∧ c i ≤ 1) (hpr0 : 0 ≤ pr) (hpr : pr ≤ 1)
    (w : Ω → ℝ) (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1) (plan : Ω → List ℕ),
    ∑ ω, w ω * (if S ≤ (capped q (plan ω)).sum then survive c (capped q (plan ω)) 0 else 0)
      ≤ (1 - pr) ^ ceilDiv S q

def BackSchema : Prop := ∀ (P : Type) [Fintype P] (S q : ℕ) (pr : ℝ)
    (plans : P → List ℕ) (w : P → ℝ) (c : ℕ → ℝ), BackAt P S q pr plans w c

def OrigSchema : Prop := ∀ (P : Type) [Fintype P] (S q : ℕ) (pr : ℝ)
    (plans : P → List ℕ) (w : P → ℝ) (c : ℕ → ℝ), OrigAt P S q pr plans w c

def PointwiseClaim : Prop :=
  ComponentwiseClaim ∧ ∀ (P : Type) [Fintype P] (S q : ℕ) (pr : ℝ)
    (plans : P → List ℕ) (w : P → ℝ) (c : ℕ → ℝ), BackAt P S q pr plans w c ↔ OrigAt P S q pr plans w c

def Claim : Prop :=
  (FrozenBack ↔ BackSchema) ∧ (Original ↔ OrigSchema) ∧ PointwiseClaim

end PL_bg1n2_9
