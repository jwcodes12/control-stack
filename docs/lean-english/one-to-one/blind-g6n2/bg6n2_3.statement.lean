namespace PL_bg6n2_3
open ControlStack.SC26

def Back : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops : List Op),
    (run R cap full init ops).reserved.Nodup


def BackAt (s : St) : Prop := s.reserved.Nodup
def OrigAt (s : St) : Prop := s.reserved.Nodup
def BackEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (ops : List Op),
    BackAt (run R cap full init ops)
def OrigEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (ops : List Op),
    OrigAt (run R cap full init ops)
def Claim : Prop := (Back ↔ BackEnvelope) ∧ (∀ (s : St), BackAt s ↔ OrigAt s)
def honestOps : List Op := [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .arrive 0]
def Witness : Prop := (run R0 20 full init honestOps).reserved = [0] ∧
  (run R0 20 full init honestOps).spent = 10 ∧
  (run R0 20 full init honestOps).bank = [(0, tx1)]
end PL_bg6n2_3
