namespace PL_bg7n2_12
open ControlStack
open ControlStack.SC28Refinement

def BackFull : Prop :=
  ∀ (G lid : ℕ) (first second : List COp),
    lid ∈ (runC G cinit first).revoked →
    counter (runC G (runC G cinit first) second) lid =
      counter (runC G cinit first) lid


def BackResult (G lid : ℕ) (first second : List COp) : Prop :=
  counter (runC G (runC G cinit first) second) lid = counter (runC G cinit first) lid
def OrigResult (G lid : ℕ) (first second : List COp) : Prop :=
  counter (runC G cinit (first ++ second)) lid = counter (runC G cinit first) lid

def OrigFull : Prop :=
  ∀ (G : ℕ) (pre post : List COp) (lid : ℕ) (hr : lid ∈ (runC G cinit pre).revoked),
    counter (runC G cinit (pre ++ post)) lid = counter (runC G cinit pre) lid

def BackSchema : Prop :=
  ∀ (G lid : ℕ) (first second : List COp),
    lid ∈ (runC G cinit first).revoked →
    BackResult G lid first second

def OrigSchema : Prop :=
  ∀ (G : ℕ) (pre post : List COp) (lid : ℕ) (hr : lid ∈ (runC G cinit pre).revoked),
    OrigResult G lid pre post


def Claim : Prop :=
  (BackFull ↔ BackSchema) ∧ (OrigFull ↔ OrigSchema) ∧
  ∀ (G lid : ℕ) (first second : List COp),
    lid ∈ (runC G cinit first).revoked → (BackResult G lid first second ↔ OrigResult G lid first second)

def Witness : Prop :=
  let first : List COp := [.createLease 0 10, .launch 1 0, .consume 1 2, .revoke 0]
  let s := runC 10 cinit first
  0 ∈ s.revoked ∧ counter s 0 = 2 ∧
    counter (runC 10 s [.fork 1 2, .consume 1 3, .launch 3 0, .consume 3 3]) 0 = 2
end PL_bg7n2_12
