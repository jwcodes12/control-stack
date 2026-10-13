namespace PL_bg7n2_13
open ControlStack
open ControlStack.SC28Refinement

def BackFull : Prop :=
  ∀ (G : ℕ) (ops : List COp),
    (∀ o ∈ ops, isUnplaced o = false) →
    let s := runC G cinit ops
    s.outside = [] ∧ realTotal s ≤ G


def BackResult (G : ℕ) (ops : List COp) : Prop :=
  let s := runC G cinit ops
  s.outside = [] ∧ realTotal s ≤ G
def OrigResult (G : ℕ) (ops : List COp) : Prop :=
  (runC G cinit ops).outside = [] ∧ realTotal (runC G cinit ops) ≤ G

def OrigFull : Prop :=
  ∀ (G : ℕ) (ops : List COp) (hu : ∀ o ∈ ops, isUnplaced o = false),
    (runC G cinit ops).outside = [] ∧ realTotal (runC G cinit ops) ≤ G

def BackSchema : Prop :=
  ∀ (G : ℕ) (ops : List COp),
    (∀ o ∈ ops, isUnplaced o = false) →
    BackResult G ops

def OrigSchema : Prop :=
  ∀ (G : ℕ) (ops : List COp) (hu : ∀ o ∈ ops, isUnplaced o = false),
    OrigResult G ops


def Claim : Prop :=
  (BackFull ↔ BackSchema) ∧ (OrigFull ↔ OrigSchema) ∧
  ∀ (G : ℕ) (ops : List COp), (∀ o ∈ ops, isUnplaced o = false) →
    (BackResult G ops ↔ OrigResult G ops)

def Witness : Prop :=
  let ops : List COp := [.createLease 0 10, .launch 1 0, .fork 1 2, .consume 1 2, .consume 2 3]
  (∀ o ∈ ops, isUnplaced o = false) ∧
    (runC 10 cinit ops).outside = [] ∧ realTotal (runC 10 cinit ops) = 5
end PL_bg7n2_13
