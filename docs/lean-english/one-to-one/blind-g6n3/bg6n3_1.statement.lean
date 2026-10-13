namespace PL_bg6n3_1
open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness ControlStack.SC26Liveness.Concrete ControlStack.SC26LossyLiveness ControlStack.SC26LossyHalt

def Back_progress_interleaved : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req)
    (pre mid₁ mid₂ post : List Op),
    Inv R cap s →
    reqOf s k = some r →
    Approved R s k r →
    (∀ o ∈ pre ++ mid₁ ++ mid₂ ++ post, legal R o) →
    let beforeExecute := run R cap full s pre
    let final := run R cap full s
      (pre ++ [.execute r.requester k] ++ mid₁ ++ [.deliver k] ++
        mid₂ ++ [.arrive k] ++ post)
    final.halted = true ∨
      (k, r.tx) ∈ final.bank ∨
      (k ∉ beforeExecute.reserved ∧ cap < beforeExecute.spent + r.tx.amount)


def BackAt (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req)
    (pre mid₁ mid₂ post : List Op) : Prop :=
  let beforeExecute := run R cap full s pre
  let final := run R cap full s
    (pre ++ [.execute r.requester k] ++ mid₁ ++ [.deliver k] ++ mid₂ ++ [.arrive k] ++ post)
  final.halted = true ∨ (k, r.tx) ∈ final.bank ∨
    (k ∉ beforeExecute.reserved ∧ cap < beforeExecute.spent + r.tx.amount)

def OrigAt (R : Roles) (cap : ℕ) (s : St) (c k : ℕ) (r : Req)
    (a0 a1 a2 a3 : List Op) : Prop :=
  let t := run R cap full s (a0 ++ .execute c k :: a1 ++ .deliver k :: a2 ++ .arrive k :: a3)
  t.halted = true ∨ (k, r.tx) ∈ t.bank ∨
    (k ∉ (run R cap full s a0).reserved ∧ cap < (run R cap full s a0).spent + r.tx.amount)

def Pointwise : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : St) (c k : ℕ) (r : Req) (pre mid₁ mid₂ post : List Op),
    Inv R cap s → reqOf s k = some r → Approved R s k r →
    (∀ o ∈ pre ++ mid₁ ++ mid₂ ++ post, legal R o) →
    (BackAt R cap s k r pre mid₁ mid₂ post ↔ OrigAt R cap s c k r pre mid₁ mid₂ post)

def setup : List Op := [.request 1 wTx, .approve 2 0 wTx]
def Witness : Prop :=
  let s := run R0 10 full init setup
  Inv R0 10 s ∧ reqOf s 0 = some ⟨0, 1, wTx⟩ ∧
    Approved R0 s 0 ⟨0, 1, wTx⟩ ∧ (∀ o ∈ setup, legal R0 o) ∧
    (∀ o ∈ ([] : List Op), legal R0 o) ∧
    (0, wTx) ∈ (run R0 10 full s [.execute 88 0, .deliver 0, .arrive 0]).bank

def OriginalSignature : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : St) (h : Inv R cap s) (c k : ℕ) (r : Req)
    (hr : reqOf s k = some r) (happ : Approved R s k r) (a0 a1 a2 a3 : List Op)
    (hleg : ∀ o ∈ a0 ++ a1 ++ a2 ++ a3, legal R o),
    let t := run R cap full s (a0 ++ .execute c k :: a1 ++ .deliver k :: a2 ++ .arrive k :: a3)
    t.halted = true ∨ (k, r.tx) ∈ t.bank ∨
      (k ∉ (run R cap full s a0).reserved ∧ cap < (run R cap full s a0).spent + r.tx.amount)

def BackShape : Prop := Back_progress_interleaved ↔

  ∀ (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req)
    (pre mid₁ mid₂ post : List Op),
    Inv R cap s →
    reqOf s k = some r →
    Approved R s k r →
    (∀ o ∈ pre ++ mid₁ ++ mid₂ ++ post, legal R o) →
    BackAt R cap s k r pre mid₁ mid₂ post

def OriginalShape : Prop := OriginalSignature ↔
  ∀ (R : Roles) (cap : ℕ) (s : St) (h : Inv R cap s) (c k : ℕ) (r : Req)
    (hr : reqOf s k = some r) (happ : Approved R s k r) (a0 a1 a2 a3 : List Op)
    (hleg : ∀ o ∈ a0 ++ a1 ++ a2 ++ a3, legal R o), OrigAt R cap s c k r a0 a1 a2 a3

def Claim : Prop := Pointwise ∧ BackShape ∧ OriginalShape

end PL_bg6n3_1
