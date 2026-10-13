namespace PL_bg6n1_5

open ControlStack.SC25Content ControlStack.SC25

def FrozenBack : Prop :=
  let ops : List Op :=
    [.submit 1 0 7 false, .audit 2 0 true, .amend 1 0 50, .check 0, .fire 0]
  let sg := grun R0 (fun _ => 0) cls0 ops
  (∃ e ∈ sg.1.executed, e.content = 50) ∧
    sg.2 = [(0, 7, true, 2)]

def Ops : List Op := [.submit 1 0 7 false, .audit 2 0 true, .amend 1 0 50, .check 0, .fire 0]
def Back (es : List Exec) (g : List ARec) : Prop :=
  (∃ e ∈ es, e.content = 50) ∧ g = [(0, 7, true, 2)]
def Orig (es : List Exec) (g : List ARec) : Prop :=
  es.map Exec.content = [50] ∧ g = [(0, 7, true, 2)]

def Claim : Prop :=
  (FrozenBack = (Back (grun R0 (fun _ => 0) cls0 Ops).1.executed (grun R0 (fun _ => 0) cls0 Ops).2)) ∧
  (∀ (es : List Exec) (g : List ARec), es.length = 1 → (Back es g ↔ Orig es g)) ∧
  ((run R0 (fun _ => 0) cls0 full init Ops).executed.length = 1) ∧
  (Back (grun R0 (fun _ => 0) cls0 Ops).1.executed (grun R0 (fun _ => 0) cls0 Ops).2 ↔ Orig (run R0 (fun _ => 0) cls0 full init Ops).executed (grun R0 (fun _ => 0) cls0 Ops).2)

def Witness : Prop :=
  (run R0 (fun _ => 0) cls0 full init Ops).executed.map Exec.content = [50] ∧
    (grun R0 (fun _ => 0) cls0 Ops).2 = [(0, 7, true, 2)] ∧
    ¬ (∃ x ∈ (grun R0 (fun _ => 0) cls0 Ops).2, x.2.1 = 50)

end PL_bg6n1_5
