namespace PL_g0_04
open ControlStack ControlStack.Deployment
def Back (d : IR) (actual : List Edge) (e : Edge) : Prop := e.source = d.receiver
def Orig (d : IR) (actual : List Edge) (e : Edge) : Prop := e.source = d.receiver
def Claim : Prop := ∀ (d : IR) (actual : List Edge) (e : Edge), (Back d actual e ↔ Orig d actual e)
def Witness : Prop := Accepted clean
end PL_g0_04
