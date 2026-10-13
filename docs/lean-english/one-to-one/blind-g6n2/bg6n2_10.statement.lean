namespace PL_bg6n2_10
open ControlStack.SC26
open ControlStack.SC26Liveness

open ControlStack.SC26

def Back : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req) (caller : ℕ),
    Inv R cap s →
    s.halted = false →
    reqOf s k = some r →
    Approved R s k r →
    k ∉ s.reserved →
    s.spent + r.tx.amount ≤ cap →
    (k, r.tx) ∈
      (run R cap full s
        [Op.execute caller k, Op.deliver k, Op.arrive k]).bank


def BackAt (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req) (caller : ℕ) : Prop :=
  (k, r.tx) ∈ (run R cap full s [Op.execute caller k, Op.deliver k, Op.arrive k]).bank
def OrigAt (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req) (caller : ℕ) : Prop :=
  (k, r.tx) ∈ (run R cap full s [Op.execute caller k, Op.deliver k, Op.arrive k]).bank
def BackEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req) (caller : ℕ), Inv R cap s → s.halted = false → reqOf s k = some r → Approved R s k r → k ∉ s.reserved → s.spent + r.tx.amount ≤ cap →
    BackAt R cap s k r caller
def OrigEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req) (caller : ℕ), Inv R cap s → s.halted = false → reqOf s k = some r → Approved R s k r → k ∉ s.reserved → s.spent + r.tx.amount ≤ cap →
    OrigAt R cap s k r caller
def Claim : Prop := (Back ↔ BackEnvelope) ∧ (∀ (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req) (caller : ℕ), BackAt R cap s k r caller ↔ OrigAt R cap s k r caller)
def ready : St := ⟨1, [⟨0, 1, tx1⟩], [(0, 2, tx1)], [], 0, false, [], []⟩
def Witness : Prop := Inv R0 20 ready ∧ ready.halted = false ∧ reqOf ready 0 = some ⟨0, 1, tx1⟩ ∧
  Approved R0 ready 0 ⟨0, 1, tx1⟩ ∧ 0 ∉ ready.reserved ∧ ready.spent + tx1.amount ≤ 20 ∧
  (0, tx1) ∈ (run R0 20 full ready [.execute 1 0, .deliver 0, .arrive 0]).bank
end PL_bg6n2_10
