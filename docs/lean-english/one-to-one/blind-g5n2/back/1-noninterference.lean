import ControlStack.Scenarios.SC23Isolation

namespace ControlStack.SC23Isolation

-- Environmental isolation and authentic user input are external interpretations
-- of this model; the proposition compares precisely the four fields of Rel.
def Back_noninterference : Prop :=
  ∀ (E : Env) (ops ops' : List Op),
    List.Forall₂ SameExceptContent ops ops' →
      Rel (run E full init ops) (run E full init ops')

end ControlStack.SC23Isolation
