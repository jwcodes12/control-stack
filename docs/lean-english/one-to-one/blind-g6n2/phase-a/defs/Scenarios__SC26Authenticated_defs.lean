-- EXCERPT of ControlStack/Scenarios/SC26Authenticated.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC26Authenticated

open ControlStack.Gate ControlStack.Authenticated ControlStack.SC26

/-- the SC-26 gate as a raw `Gate.System` (all operations, deployed checks) -/
def raw (R : Roles) (cap : ℕ) : System St Op (ℕ × Tx) := ⟨step R cap full, St.bank⟩

/-- the identity each operation claims; `deliver` and `arrive` claim none -/
def claim : Op → Option ℕ
  | .request c _ => some c
  | .approve c _ _ => some c
  | .execute c _ => some c
  | .bankCall c _ _ => some c
  | .halt c => some c
  | .deliver _ => none
  | .arrive _ => none

/-- the forged-approval trace: every operation is issued by agent 1; the `approve` claims approver 2 -/
def forged : List (ℕ × Op) :=
  [(1, .request 1 tx1), (1, .approve 2 0 tx1), (1, .execute 1 0), (1, .deliver 0), (1, .arrive 0)]

end ControlStack.SC26Authenticated

