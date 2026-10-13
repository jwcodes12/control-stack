namespace PL_bg7n2_1
open ControlStack
open ControlStack.SC28

def BackFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal o) →
    Good G (run admins G full init ops)


def BackResult (admins : List ℕ) (G : ℕ) (ops : List Op) : Prop :=
  Good G (run admins G full init ops)
def OrigResult (admins : List ℕ) (G : ℕ) (ops : List Op) : Prop :=
  Good G (run admins G full init ops)

def OrigFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal o),
    Good G (run admins G full init ops)

def BackSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal o) →
    BackResult admins G ops

def OrigSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal o),
    OrigResult admins G ops


def Claim : Prop :=
  (BackFull ↔ BackSchema) ∧ (OrigFull ↔ OrigSchema) ∧
  ∀ (admins : List ℕ) (G : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal o) → (BackResult admins G ops ↔ OrigResult admins G ops)

def Witness : Prop :=
  let ops : List Op := [.issue 9 0 10, .assignTo 9 1 0, .work 1 2 2]
  (∀ o ∈ ops, legal o) ∧ (run [9] 10 full init ops).usage = [(1, 0, 2)] ∧
    usedT (run [9] 10 full init ops) = 2
end PL_bg7n2_1
