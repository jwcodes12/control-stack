namespace PL_bg7n2_11
open ControlStack
open ControlStack.SC28Refinement

def BackFull : Prop :=
  ∀ (G : ℕ) (ops : List COp),
    let s := runC G cinit ops
    runCounter s ≤ G ∧
      (∀ lid, counter s lid ≤ (limitOf s lid).getD 0) ∧
      s.acct.length ≤ G


def BackResult (G : ℕ) (s : CSt) : Prop :=
  runCounter s ≤ G ∧ (∀ lid, counter s lid ≤ (limitOf s lid).getD 0) ∧ s.acct.length ≤ G
def OrigResult (G : ℕ) (s : CSt) : Prop := SC28.Good G (α s)

def OrigFull : Prop :=
  ∀ (G : ℕ) (ops : List COp),
    SC28.Good G (α (runC G cinit ops))

def BackSchema : Prop :=
  ∀ (G : ℕ) (ops : List COp),
    BackResult G (runC G cinit ops)

def OrigSchema : Prop :=
  ∀ (G : ℕ) (ops : List COp),
    OrigResult G (runC G cinit ops)


def Claim : Prop :=
  (BackFull ↔ BackSchema) ∧ (OrigFull ↔ OrigSchema) ∧
  ∀ (G : ℕ) (s : CSt), BackResult G s ↔ OrigResult G s

def Witness : Prop :=
  let t := runC 10 cinit [.createLease 0 10, .launch 1 0, .consume 1 2]
  t.acct = [(1, 0, 2)] ∧ runCounter t = 2 ∧ t.outside = []
end PL_bg7n2_11
