namespace PL_bg5n1_1
open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
open scoped BigOperators

def Back_sc21_safe : Prop :=
  ∀ (E : Env) (ops : List Op),
    ∀ p ∈ (run E full init ops).published, PubOk E p

def HBack (E : Env) (ops : List Op) : Prop :=
  True
def HOrig (E : Env) (ops : List Op) : Prop :=
  True
noncomputable def BackAt (E : Env) (ops : List Op) : Prop :=
  ∀ p ∈ (run E full init ops).published, PubOk E p
noncomputable def OrigAt (E : Env) (ops : List Op) : Prop :=
  ∀ p ∈ (run E full init ops).published, PubOk E p

def wEnv : Env := ⟨[0, 1], fun _ => 0, 7, [9]⟩
def wOps : List Op := [.report 0 0 7, .report 1 9 7, .reexec 0, .publish]
def Witness : Prop := (run wEnv full init wOps).published = [([(1,9,7),(0,0,7)], [0])]

def Claim : Prop :=
  (Back_sc21_safe ↔ ∀ (E : Env) (ops : List Op), HBack E ops → BackAt E ops) ∧
  (∀ (E : Env) (ops : List Op), HBack E ops ↔ HOrig E ops) ∧
  (∀ (E : Env) (ops : List Op), HBack E ops → (BackAt E ops ↔ OrigAt E ops))
end PL_bg5n1_1
