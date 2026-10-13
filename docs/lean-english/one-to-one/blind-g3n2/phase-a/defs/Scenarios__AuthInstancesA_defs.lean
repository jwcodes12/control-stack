-- EXCERPT of ControlStack/Scenarios/AuthInstancesA.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.AuthInstances

open ControlStack.Gate ControlStack.Authenticated ControlStack.AuthenticatedLog



section SC16
open ControlStack.SC16

def claim16 : SC16.Op → Option ℕ
  | .stage c _ => some c
  | .writeSlot c _ _ => some c
  | .review c _ => some c
  | .approve c _ _ _ _ => some c
  | .deploy c _ _ _ => some c
  | .halt c => some c

/-- agent 1 issues everything, forging the review (as reviewer 2) and the approval (as approver 3) -/
def forged16 : List (ℕ × SC16.Op) := [(1, .stage 1 7), (1, .review 2 7), (1, .approve 3 0 7 5 0), (1, .deploy 1 0 5 7)]

end SC16



section SC25
open ControlStack.SC25

def claim25 : SC25.Op → Option ℕ
  | .submit c _ _ _ => some c
  | .amend c _ _ => some c
  | .audit c _ _ => some c
  | .approve c _ => some c
  | .halt c => some c
  | .timeout _ => none
  | .check _ => none
  | .fire _ => none
  | .crash => none

/-- agent 1 submits a reversible operation and forges the auditor's PASS (as auditor 2) -/
def forged25 : List (ℕ × SC25.Op) := [(1, .submit 1 0 7 false), (1, .audit 2 0 true), (1, .check 0), (1, .fire 0)]

end SC25



section SC28
open ControlStack.SC28

def claim28 : SC28.Op → Option ℕ
  | .issue c _ _ => some c
  | .assignTo c _ _ => some c
  | .fork c _ _ _ => some c
  | .revoke c _ => some c
  | .work w _ _ => some w
  | .restart => none
  | .rollback _ => none
  | .halt c => some c

/-- agent 1 forges the admin's lease issue and assignment (as admin 9), then works -/
def forged28 : List (ℕ × SC28.Op) := [(1, .issue 9 0 100), (1, .assignTo 9 1 0), (1, .work 1 5 5)]

end SC28



section SC17
open ControlStack.SC17

def claim17 : SC17.Op → Option ℕ
  | .propose c _ _ => some c
  | .amend c _ _ => some c
  | .approve c _ => some c
  | .halt c => some c
  | .oob _ => none
  | .reconcile => none
  | .apply _ => none

/-- author 1 proposes and forges the reviewer's approval (as reviewer 2) -/
def forged17 : List (ℕ × SC17.Op) := [(1, .propose 1 0 dA), (1, .approve 2 0), (1, .apply 0)]

end SC17



section SC19
open ControlStack.SC19

def claim19 : SC19.Op → Option ℕ
  | .verify c _ => some c
  | .prepare c _ _ => some c
  | .approve c _ => some c
  | .halt c => some c
  | .write _ _ => none
  | .snapshot _ => none
  | .commit _ _ => none

/-- author 1 issues everything, forging the restore verification (as verifier 3) and the approval (as approver 2) -/
def forged19 : List (ℕ × SC19.Op) :=
  [(1, .write 7 5), (1, .snapshot 7), (1, .verify 3 0), (1, .prepare 1 0 7), (1, .approve 2 0), (1, .commit 0 0)]

end SC19

end ControlStack.AuthInstances

