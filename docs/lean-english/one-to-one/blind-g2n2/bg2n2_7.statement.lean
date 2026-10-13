namespace PL_bg2n2_7

open ControlStack ControlStack.SC14

def FrozenBack : Prop :=
∀ (E : Env) (exp : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal o) → Good E (run E full (init exp) ops)

def BackAt (E : Env) (exp : ℕ) (ops : List Op) : Prop := Good E (run E full (init exp) ops)
def OrigAt (E : Env) (exp : ℕ) (ops : List Op) : Prop := Good E (run E full (init exp) ops)
def Claim : Prop := ∀ (E : Env) (exp : ℕ) (ops : List Op),
  (∀ o ∈ ops, legal o) → (BackAt E exp ops ↔ OrigAt E exp ops)
def Witness : Prop := ∃ ops : List Op,
  (∀ o ∈ ops, legal o) ∧
  (run E0 full (init 100) ops).usage = [((2, 2, 2), 0, 100), ((3, 3, 3), 1, 100)] ∧
  usedTotal (run E0 full (init 100) ops) = (5, 5, 5)

end PL_bg2n2_7
