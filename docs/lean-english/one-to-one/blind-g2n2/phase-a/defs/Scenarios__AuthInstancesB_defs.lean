-- EXCERPT of ControlStack/Scenarios/AuthInstancesB.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.AuthInstances

open ControlStack.Gate ControlStack.Authenticated ControlStack.AuthenticatedLog



section SC15
open ControlStack.SC15

def claim15 : SC15.Op → Option ℕ
  | .propose a _ _ _ _ => some a
  | .amend a _ _ _ => some a
  | .review r _ _ => some r
  | .halt a => some a
  | .runCI _ => none
  | .merge _ => none

/-- author 1 proposes and forges the review (as reviewer 2) -/
def forged15 : List (ℕ × SC15.Op) :=
  [(1, .propose 1 0 7 [5] [5]), (1, .review 2 0 false), (1, .runCI 0), (1, .merge 0)]

end SC15



section SC20
open ControlStack.SC20

def claim20 : SC20.Op → Option ℕ
  | .agentWrite c _ _ => some c
  | .promote c _ => some c
  | .freeze c _ => some c
  | .halt c => some c
  | .ingest _ _ _ => none
  | .edit _ _ => none
  | .train => none

/-- agent 1 writes an example and forges the promotion (as reviewer 2) and the freeze (as admin 9) -/
def forged20 : List (ℕ × SC20.Op) := [(1, .agentWrite 1 1 66), (1, .promote 2 1), (1, .freeze 9 [1]), (1, .train)]

end SC20



section SC23
open ControlStack.SC23

def claim23 : SC23.Op → Option ℕ
  | .confirm c _ _ _ => some c
  | .halt c => some c
  | .userInput _ _ => none
  | .toolResult _ _ => none
  | .derive _ _ _ => none
  | .act _ _ _ => none

/-- an injected principal 7 delivers a tool result and forges the user's confirmation (as user 1) -/
def forged23 : List (ℕ × SC23.Op) := [(7, .toolResult 0 66), (7, .confirm 1 7 5 [66]), (7, .act 5 [0] 7)]

end SC23



section SC12
open ControlStack.SC12

def claim12 : SC12.Op → Option ℕ
  | .start c _ => some c
  | .endSession c _ => some c
  | .halt c => some c
  | .spawn _ _ _ _ => none
  | .bypass _ _ _ => none
  | .fire _ => none

/-- agent 1 forges an admin session start (as admin 9) -/
def forged12 : List (ℕ × SC12.Op) := [(1, .start 9 5), (1, .spawn 5 6 true 0)]

end SC12



section SC18
open ControlStack.SC18

def claim18 : SC18.Op → Option ℕ
  | .setSink c _ => some c
  | .halt c => some c
  | .request _ => none
  | .logWrite _ => none
  | .release _ => none
  | .sinkDown => none
  | .sinkRestore => none
  | .tick => none

/-- agent 1 forges the admin's sink change (as admin 9) to an untrusted sink 66 -/
def forged18 : List (ℕ × SC18.Op) := [(1, .setSink 9 66)]

end SC18

end ControlStack.AuthInstances

