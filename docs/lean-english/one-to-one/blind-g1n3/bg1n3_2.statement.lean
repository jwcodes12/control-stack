namespace PL_bg1n3_2
open ControlStack.SC07Exfil

def FrozenBack : Prop :=
  ∀ q : ℕ, 0 < q →
    let b : List ℕ := [0, q, 0, q]
    let c : ℕ → ℝ := fun i => if i = 0 ∨ i = 2 then 1 else 0
    b.sum = 2 * q ∧ survive c b 0 = 1

def BackAt (q : ℕ) : Prop :=
  let b : List ℕ := [0, q, 0, q]
  let c : ℕ → ℝ := fun i => if i = 0 ∨ i = 2 then 1 else 0
  b.sum = 2 * q ∧ survive c b 0 = 1

def OriginalAt (q : ℕ) : Prop :=
  let c : ℕ → ℝ := fun i => if i = 0 ∨ i = 2 then 1 else 0
  (capped q [0, q, 0, q]).sum = 2 * q ∧ survive c (capped q [0, q, 0, q]) 0 = 1

def Claim : Prop :=
  (FrozenBack ↔ ∀ q : ℕ, 0 < q → BackAt q) ∧
  (∀ q : ℕ, 0 < q → (BackAt q ↔ OriginalAt q))

def Witness : Prop :=
  0 < (1 : ℕ) ∧ ([0, 1, 0, 1] : List ℕ).sum = 2 ∧ survive (fun i => if i = 0 ∨ i = 2 then 1 else 0) [0, 1, 0, 1] 0 = 1

end PL_bg1n3_2
