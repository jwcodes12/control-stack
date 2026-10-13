namespace PL_bg7n2_3
open ControlStack
open ControlStack.SC28

def BackFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St)
    (caller parent child newLid lid : ℕ),
    s.halted = false →
    leaseOf s parent = some lid →
    leaseOf s child = none →
    leaseOf (step admins G full s (.fork caller parent child newLid)) child =
      some lid


def BackFresh (s : St) (child : ℕ) : Prop := leaseOf s child = none
def OrigFresh (s : St) (child : ℕ) : Prop := child ∉ s.assign.map Prod.fst
def BackResult (admins : List ℕ) (G : ℕ) (s : St) (c p ch nl lid : ℕ) : Prop :=
  leaseOf (step admins G full s (.fork c p ch nl)) ch = some lid
def OrigResult (admins : List ℕ) (G : ℕ) (s : St) (c p ch nl lid : ℕ) : Prop :=
  leaseOf (step admins G full s (.fork c p ch nl)) ch = some lid

def OrigFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St) (c p ch nl lid : ℕ) (hh : s.halted = false)
    (hp : leaseOf s p = some lid) (hfresh : ch ∉ s.assign.map Prod.fst),
    leaseOf (step admins G full s (.fork c p ch nl)) ch = some lid

def BackSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St)
    (caller parent child newLid lid : ℕ),
    s.halted = false →
    leaseOf s parent = some lid →
    leaseOf s child = none →
    BackResult admins G s caller parent child newLid lid

def OrigSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St) (c p ch nl lid : ℕ) (hh : s.halted = false)
    (hp : leaseOf s p = some lid) (hfresh : ch ∉ s.assign.map Prod.fst),
    OrigResult admins G s c p ch nl lid


def Claim : Prop :=
  (BackFull ↔ BackSchema) ∧ (OrigFull ↔ OrigSchema) ∧
  (∀ (s : St) (child : ℕ), BackFresh s child ↔ OrigFresh s child) ∧
  (∀ (admins : List ℕ) (G : ℕ) (s : St) (c p ch nl lid : ℕ),
    s.halted = false → leaseOf s p = some lid → BackFresh s ch →
    (BackResult admins G s c p ch nl lid ↔ OrigResult admins G s c p ch nl lid))

def Witness : Prop :=
  let s := run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0]
  s.halted = false ∧ leaseOf s 1 = some 0 ∧ leaseOf s 2 = none ∧
    2 ∉ s.assign.map Prod.fst ∧ leaseOf (step [9] 10 full s (.fork 77 1 2 99)) 2 = some 0
end PL_bg7n2_3
