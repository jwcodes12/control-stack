import ControlStack.Deployment.R2Contracts

namespace ControlStack.Deployment

def Back_indexed_receipts_sound : Prop :=
  ∀ (R : ControlStack.TrustedBroker.Roles) (table : IndexedBrokerTable R)
    (start : Nat) (rs : List (ControlStack.CheckedTrace.Receipt Nat Nat)),
    ControlStack.CheckedTrace.verified table.step start rs = true →
      ControlStack.TrustedBroker.Trace R (table.interpret start)
        (table.interpret (ControlStack.CheckedTrace.recordedEnd start rs))

end ControlStack.Deployment
