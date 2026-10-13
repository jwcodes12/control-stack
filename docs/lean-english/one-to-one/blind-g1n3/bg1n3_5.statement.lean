namespace PL_bg1n3_5
open ControlStack.SC07Liveness

def FrozenBack : Prop :=
  ∀ (E : Env) (ops : List Op) (S : ℕ),
    0 < E.q →
    S ≤ total (run E full init ops) →
    ControlStack.SC07Exfil.ceilDiv S E.q ≤
      (run E full init ops).window + 1

def BackAt (E : Env) (ops : List Op) (S : ℕ) : Prop :=
  ControlStack.SC07Exfil.ceilDiv S E.q ≤ (run E full init ops).window + 1

def OriginalAt (E : Env) (ops : List Op) (S : ℕ) : Prop :=
  ControlStack.SC07Exfil.ceilDiv S E.q ≤ (run E full init ops).window + 1

def Claim : Prop :=
  (FrozenBack ↔ ∀ (E : Env) (ops : List Op) (S : ℕ), 0 < E.q → S ≤ total (run E full init ops) → BackAt E ops S) ∧
  (∀ (E : Env) (ops : List Op) (S : ℕ), 0 < E.q → S ≤ total (run E full init ops) → (BackAt E ops S ↔ OriginalAt E ops S))

def Witness : Prop :=
  0 < E0.q ∧ total (run E0 full init [.send 10 8, .tick, .send 10 8]) = 16 ∧ (run E0 full init [.send 10 8, .tick, .send 10 8]).window + 1 = 2 ∧ ControlStack.SC07Exfil.ceilDiv 16 E0.q = 2

end PL_bg1n3_5
