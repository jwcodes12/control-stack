import ControlStack.Deployment.Contracts

namespace ControlStack.Deployment

def Back_runtime_exclusive : Prop :=
  ∀ (d : IR) (actual : List Edge),
    Accepted d → Faithful d actual →
    ∀ e ∈ actual, e.authority = true → e.target = d.sink →
      e.source = d.receiver

end ControlStack.Deployment
