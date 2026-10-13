namespace PL_bg6n3_2
open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness ControlStack.SC26Liveness.Concrete ControlStack.SC26LossyLiveness ControlStack.SC26LossyHalt

def Back_crash_tolerant_progress : Prop :=
  ∀ (R : Roles) (cap k : ℕ) (ops₀ pre mid post : List COp),
    (∀ o ∈ ops₀, legalC R o) →
    let start := runC R cap true cinit ops₀
    (∃ d ∈ start.delivery, d.id = k) →
    (∀ o ∈ pre ++ mid ++ post, legalC R o) →
    (runC R cap true start pre).halted = false →
    let final := runC R cap true start
      (pre ++ [.recover] ++ mid ++ [.bankProcess k] ++ post)
    (final.bank.map Prod.fst).count k = 1


def BackAt (R : Roles) (cap k : ℕ) (ops₀ pre mid post : List COp) : Prop :=
  let start := runC R cap true cinit ops₀
  let final := runC R cap true start (pre ++ [.recover] ++ mid ++ [.bankProcess k] ++ post)
  (final.bank.map Prod.fst).count k = 1

def OrigAt (R : Roles) (cap k : ℕ) (ops0 pre mid post : List COp) : Prop :=
  k ∈ (runC R cap true (runC R cap true cinit ops0) (pre ++ .recover :: mid ++ .bankProcess k :: post)).bank.map Prod.fst ∧
  ((runC R cap true (runC R cap true cinit ops0) (pre ++ .recover :: mid ++ .bankProcess k :: post)).bank.map Prod.fst).count k = 1

def Pointwise : Prop :=
  ∀ (R : Roles) (cap k : ℕ) (ops₀ pre mid post : List COp) (d : DRow),
    (∀ o ∈ ops₀, legalC R o) → d ∈ (runC R cap true cinit ops₀).delivery → d.id = k →
    (∀ o ∈ pre ++ mid ++ post, legalC R o) →
    (runC R cap true (runC R cap true cinit ops₀) pre).halted = false →
    (BackAt R cap k ops₀ pre mid post ↔ OrigAt R cap k ops₀ pre mid post)

def setup : List COp := [.request 1 wTx, .approve 2 0 wTx, .execute 1 0, .deliver 0]
def Witness : Prop :=
  let s := runC R0 10 true cinit setup
  (∀ o ∈ setup, legalC R0 o) ∧ ⟨0, wTx, false⟩ ∈ s.delivery ∧
  (∀ o ∈ ([.crash] ++ [.crash] ++ [.crash] : List COp), legalC R0 o) ∧
  (runC R0 10 true s [.crash]).halted = false ∧
  ((runC R0 10 true s [.crash, .recover, .crash, .bankProcess 0, .crash]).bank.map Prod.fst).count 0 = 1

def OriginalSignature : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops0 : List COp) (hops0 : ∀ o ∈ ops0, legalC R o)
    (k : ℕ) (d : DRow) (hd : d ∈ (runC R cap true cinit ops0).delivery) (hk : d.id = k)
    (pre mid post : List COp) (hleg : ∀ o ∈ pre ++ mid ++ post, legalC R o)
    (hh : (runC R cap true (runC R cap true cinit ops0) pre).halted = false),
    k ∈ (runC R cap true (runC R cap true cinit ops0) (pre ++ .recover :: mid ++ .bankProcess k :: post)).bank.map
        Prod.fst ∧
      ((runC R cap true (runC R cap true cinit ops0) (pre ++ .recover :: mid ++ .bankProcess k :: post)).bank.map
        Prod.fst).count k = 1

def BackShape : Prop := Back_crash_tolerant_progress ↔

  ∀ (R : Roles) (cap k : ℕ) (ops₀ pre mid post : List COp),
    (∀ o ∈ ops₀, legalC R o) →
    let start := runC R cap true cinit ops₀
    (∃ d ∈ start.delivery, d.id = k) →
    (∀ o ∈ pre ++ mid ++ post, legalC R o) →
    (runC R cap true start pre).halted = false →
    BackAt R cap k ops₀ pre mid post

def OriginalShape : Prop := OriginalSignature ↔
  ∀ (R : Roles) (cap : ℕ) (ops0 : List COp) (hops0 : ∀ o ∈ ops0, legalC R o)
    (k : ℕ) (d : DRow) (hd : d ∈ (runC R cap true cinit ops0).delivery) (hk : d.id = k)
    (pre mid post : List COp) (hleg : ∀ o ∈ pre ++ mid ++ post, legalC R o)
    (hh : (runC R cap true (runC R cap true cinit ops0) pre).halted = false), OrigAt R cap k ops0 pre mid post

def Claim : Prop := Pointwise ∧ BackShape ∧ OriginalShape

end PL_bg6n3_2
