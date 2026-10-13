open scoped BigOperators
open ControlStack Finset
open ControlStack.Covert ControlStack.Leakage
open ControlStack.SC07Exfil
namespace PL_bg1n2_8

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

def FrozenBack : Prop :=
  ∀ (S q : ℕ) (b : List ℕ),
    0 < q →
    (∀ x ∈ b, x ≤ q) →
    S ≤ b.sum →
    ceilDiv S q ≤ traffic b


noncomputable def delta {A : Type} [Fintype A] [DecidableEq A] (a : A) : A → ℝ :=
  fun x => if x = a then 1 else 0


def BackHyp (S q : ℕ) (b : List ℕ) : Prop :=
  0 < q ∧ (∀ x ∈ b, x ≤ q) ∧ S ≤ b.sum

def OrigHyp (S q : ℕ) (b : List ℕ) : Prop :=
  0 < q ∧ (∀ x ∈ b, x ≤ q) ∧ S ≤ b.sum

def BackConclusion (S q : ℕ) (b : List ℕ) : Prop :=
  ceilDiv S q ≤ traffic b

def OrigConclusion (S q : ℕ) (b : List ℕ) : Prop :=
  ceilDiv S q ≤ traffic b

def BackAt (S q : ℕ) (b : List ℕ) : Prop := BackHyp S q b → BackConclusion S q b

def OrigAt (S q : ℕ) (b : List ℕ) : Prop := OrigHyp S q b → OrigConclusion S q b

def ComponentwiseClaim : Prop :=
  ∀ (S q : ℕ) (b : List ℕ), (BackHyp S q b ↔ OrigHyp S q b) ∧ (BackConclusion S q b ↔ OrigConclusion S q b)

def Witness : Prop :=
  BackHyp 3 2 [2, 0, 1] ∧ ceilDiv 3 2 = 2 ∧ traffic [2, 0, 1] = 2

def Original : Prop :=
  ∀  (S q : ℕ) (hq : 0 < q) (b : List ℕ) (hb : ∀ x ∈ b, x ≤ q) (hS : S ≤ b.sum),
    ceilDiv S q ≤ traffic b

def BackSchema : Prop := ∀ (S q : ℕ) (b : List ℕ), BackAt S q b

def OrigSchema : Prop := ∀ (S q : ℕ) (b : List ℕ), OrigAt S q b

def PointwiseClaim : Prop :=
  ComponentwiseClaim ∧ ∀ (S q : ℕ) (b : List ℕ), BackAt S q b ↔ OrigAt S q b

def Claim : Prop :=
  (FrozenBack ↔ BackSchema) ∧ (Original ↔ OrigSchema) ∧ PointwiseClaim

end PL_bg1n2_8
