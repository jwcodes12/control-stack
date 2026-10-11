namespace PL_g0_02
open ControlStack ControlStack.Deployment
def Back (d : IR) (e : Edge) : Prop := e.source = d.receiver ∨ e.source = d.broker
def Orig (d : IR) (e : Edge) : Prop := e.source = d.receiver
def Claim : Prop := (∀ d e, Orig d e → Back d e) ∧ (∃ d e, Back d e ∧ ¬ Orig d e)
def Witness : Prop := Accepted clean
end PL_g0_02
