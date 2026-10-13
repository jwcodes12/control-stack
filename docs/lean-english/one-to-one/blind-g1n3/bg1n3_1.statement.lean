namespace PL_bg1n3_1
open ControlStack.SC07Exfil

def FrozenBack : Prop :=
  ∀ (q : ℕ) (pr : ℝ) (c : ℕ → ℝ) (b : List ℕ),
    0 < pr →
    (∀ i : ℕ, pr ≤ c i ∧ c i ≤ 1) →
    expLeak c (capped q b) 0 ≤ (q : ℝ) / pr

def BackAt (q : ℕ) (pr : ℝ) (c : ℕ → ℝ) (b : List ℕ) : Prop :=
  expLeak c (capped q b) 0 ≤ (q : ℝ) / pr

def OriginalAt (q : ℕ) (pr : ℝ) (c : ℕ → ℝ) (b : List ℕ) : Prop :=
  expLeak c (capped q b) 0 ≤ q / pr

def Claim : Prop :=
  (FrozenBack ↔ ∀ (q : ℕ) (pr : ℝ) (c : ℕ → ℝ) (b : List ℕ), 0 < pr → (∀ i, pr ≤ c i ∧ c i ≤ 1) → BackAt q pr c b) ∧
  (∀ (q : ℕ) (pr : ℝ) (c : ℕ → ℝ) (b : List ℕ), 0 < pr → (∀ i, pr ≤ c i ∧ c i ≤ 1) → (BackAt q pr c b ↔ OriginalAt q pr c b))

def Witness : Prop :=
  (0 < (1 / 2 : ℝ)) ∧ (∀ i : ℕ, (1 / 2 : ℝ) ≤ (fun _ : ℕ => (1 / 2 : ℝ)) i ∧ (fun _ : ℕ => (1 / 2 : ℝ)) i ≤ 1) ∧ (capped 8 [8, 8]).sum = 16 ∧ expLeak (fun _ => (1 / 2 : ℝ)) (capped 8 [8, 8]) 0 = 12

end PL_bg1n3_1
