import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_17
open ControlStack ControlStack.Deployment
def Back (R : TrustedBroker.Roles) (table : IndexedBrokerTable R) (rs : List (CheckedTrace.Receipt Nat Nat)) (start : Nat) : Prop := TrustedBroker.Trace R (table.interpret start) (table.interpret (CheckedTrace.recordedEnd start rs))
def Orig (R : TrustedBroker.Roles) (table : IndexedBrokerTable R) (rs : List (CheckedTrace.Receipt Nat Nat)) (start : Nat) : Prop := TrustedBroker.Trace R (table.interpret start) (table.interpret (CheckedTrace.recordedEnd start rs))
def Claim : Prop := ∀ (R : TrustedBroker.Roles) (table : IndexedBrokerTable R) (rs : List (CheckedTrace.Receipt Nat Nat)) (start : Nat), (Back R table rs start ↔ Orig R table rs start)
def Witness : Prop := Accepted clean
end PL_g0_17

namespace ReviewProof_g0_17
open PL_g0_17
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro R table rs start
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : TrustedBroker.Roles) (table : IndexedBrokerTable R) (rs : List (CheckedTrace.Receipt Nat Nat)) (start : Nat) (verified : CheckedTrace.verified table.step start rs = true) : Orig R table rs start := indexed_receipts_sound R table rs start verified

end ReviewProof_g0_17
#print axioms ReviewProof_g0_17.claim
#print axioms ReviewProof_g0_17.witness
