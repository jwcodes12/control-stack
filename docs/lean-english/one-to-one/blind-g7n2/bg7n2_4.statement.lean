namespace PL_bg7n2_4
open ControlStack
open ControlStack.SC28

def BackFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op),
    s.halted = true →
    (run admins G full s ops).usage = s.usage


def BackResult (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op) : Prop :=
  (run admins G full s ops).usage = s.usage
def OrigResult (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op) : Prop :=
  (run admins G full s ops).usage = s.usage

def OrigFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op) (hh : s.halted = true),
    (run admins G full s ops).usage = s.usage

def BackSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op),
    s.halted = true →
    BackResult admins G s ops

def OrigSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op) (hh : s.halted = true),
    OrigResult admins G s ops


def Claim : Prop :=
  (BackFull ↔ BackSchema) ∧ (OrigFull ↔ OrigSchema) ∧
  ∀ (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op),
    s.halted = true → (BackResult admins G s ops ↔ OrigResult admins G s ops)

def Witness : Prop :=
  let s := run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0, .work 1 2 2, .halt 9]
  s.halted = true ∧ usedT s = 2 ∧
    (run [9] 10 full s [.rollback 0, .work 1 3 3]).usage = s.usage ∧
    (run [9] 10 full s [.rollback 0]).ledger ≠ s.ledger
end PL_bg7n2_4
