namespace PL_bg5n2_3
open ControlStack.SC23Isolation
def Back_sc23_isolated_safe : Prop :=
  ∀ (E : Env) (ops : List Op),
    let s := run E full init ops
    ∀ x ∈ s.executed, ActOk E s x

def Claim : Prop :=
  (Back_sc23_isolated_safe = (∀ (E : Env) (ops : List Op),
    ∀ x ∈ (run E full init ops).executed, ActOk E (run E full init ops) x)) ∧
  (∀ (E : Env) (ops : List Op) (x : Act), x ∈ (run E full init ops).executed →
    (ActOk E (run E full init ops) x ↔
     (x.tool ∈ E.sensitive → x.tainted = true →
       ∃ n, x.conf = some n ∧ ∃ cf ∈ (run E full init ops).confs,
         cf.n = n ∧ cf.tool = x.tool ∧ cf.vals = x.vals ∧ cf.by_ ∈ E.users)))
def BasicWitness : Prop :=
  (run E0 full init [.toolResult 66, .confirm 1 7 5 [66], .act 5 [0] 7]).executed = [⟨5,[66],true,some 7⟩]

def LimitWitness : Prop :=
  (run E0 full init [.toolResult 66,.confirm 1 7 5 [66],.act 5 [0] 7,.act 5 [0] 7]).executed =
    [⟨5,[66],true,some 7⟩,⟨5,[66],true,some 7⟩]
def Witness : Prop := BasicWitness ∧ LimitWitness
end PL_bg5n2_3
