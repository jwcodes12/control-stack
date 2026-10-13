namespace PL_bg7n2_2
open ControlStack
open ControlStack.SC28

def BackFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (C : Checks) (s : St)
    (lid : ℕ) (ops : List Op),
    lid ∈ s.revoked →
    usedL (run admins G C s ops) lid = usedL s lid


def BackResult (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (lid : ℕ) (ops : List Op) : Prop :=
  usedL (run admins G C s ops) lid = usedL s lid
def OrigResult (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (lid : ℕ) (ops : List Op) : Prop :=
  usedL (run admins G C s ops) lid = usedL s lid

def OrigFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (ops : List Op) (lid : ℕ)
    (hr : lid ∈ s.revoked),
    usedL (run admins G C s ops) lid = usedL s lid

def BackSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (C : Checks) (s : St)
    (lid : ℕ) (ops : List Op),
    lid ∈ s.revoked →
    BackResult admins G C s lid ops

def OrigSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (ops : List Op) (lid : ℕ)
    (hr : lid ∈ s.revoked),
    OrigResult admins G C s lid ops


def Claim : Prop :=
  (BackFull ↔ BackSchema) ∧ (OrigFull ↔ OrigSchema) ∧
  ∀ (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (lid : ℕ) (ops : List Op),
    lid ∈ s.revoked → (BackResult admins G C s lid ops ↔ OrigResult admins G C s lid ops)

def Witness : Prop :=
  let s := run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0, .work 1 2 2, .revoke 9 0]
  0 ∈ s.revoked ∧ usedL s 0 = 2 ∧ usedL (run [9] 10 full s [.rollback 0, .work 1 3 3]) 0 = 2
end PL_bg7n2_2
