namespace PL_g0_02_contextual
open ControlStack.Deployment
def Back (d : IR) (e : Edge) : Prop := e.source = d.receiver ∨ e.source = d.broker
def Orig (d : IR) (e : Edge) : Prop := e.source = d.receiver
def Claim : Prop := ∀ (d : IR) (e : Edge), Accepted d → e ∈ d.edges → e.authority = true → e.target = d.sink → (Back d e ↔ Orig d e)
def Witness : Prop := Accepted clean
end PL_g0_02_contextual
