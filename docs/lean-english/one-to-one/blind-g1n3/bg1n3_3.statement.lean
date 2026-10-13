namespace PL_bg1n3_3
open ControlStack.SC07Exfil

def FrozenBack : Prop :=
  ceilDiv 800000000000 8000000000 = 100 ∧
    ∀ (b : List ℕ) (c : ℕ → ℝ),
      800000000000 ≤ (capped 8000000000 b).sum →
      (∀ i : ℕ, (5 / 100 : ℝ) ≤ c i ∧ c i ≤ 1) →
      survive c (capped 8000000000 b) 0 ≤ (6 / 1000 : ℝ)

def BackAt (b : List ℕ) (c : ℕ → ℝ) : Prop :=
  ceilDiv 800000000000 8000000000 = 100 ∧ survive c (capped 8000000000 b) 0 ≤ (6 / 1000 : ℝ)

def OriginalAt (b : List ℕ) (c : ℕ → ℝ) : Prop :=
  ceilDiv 800000000000 8000000000 = 100 ∧ survive c (capped 8000000000 b) 0 ≤ (0.006 : ℝ)

def Claim : Prop :=
  (FrozenBack ↔ ∀ (b : List ℕ) (c : ℕ → ℝ), 800000000000 ≤ (capped 8000000000 b).sum → (∀ i, (5 / 100 : ℝ) ≤ c i ∧ c i ≤ 1) → BackAt b c) ∧
  (∀ (b : List ℕ) (c : ℕ → ℝ), 800000000000 ≤ (capped 8000000000 b).sum → (∀ i, (5 / 100 : ℝ) ≤ c i ∧ c i ≤ 1) → (BackAt b c ↔ OriginalAt b c))

def Witness : Prop :=
  0 < (8000000000 : ℕ) ∧ (∀ i : ℕ, (5 / 100 : ℝ) ≤ (fun _ : ℕ => (1 : ℝ)) i ∧ (fun _ : ℕ => (1 : ℝ)) i ≤ 1) ∧ (capped 8000000000 (List.replicate 100 8000000000)).sum = 800000000000

end PL_bg1n3_3
