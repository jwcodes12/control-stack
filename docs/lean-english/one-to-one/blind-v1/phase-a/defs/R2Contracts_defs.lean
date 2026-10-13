-- EXCERPT: definitions only; theorems and the redacted declarations are removed. Not compilable on its own.
namespace ControlStack.Deployment
inductive AvoidedPath (d : IR) (start : Nat) : Nat → Prop
  | refl : AvoidedPath d start start
  | step (e : Edge) (member : e ∈ d.edges)
      (broker : e.target ≠ d.broker) (receiver : e.target ≠ d.receiver)
      (prior : AvoidedPath d start e.source) : AvoidedPath d start e.target

def sinkOnly : IR := {clean with edges := [⟨3,4,true,false,true⟩]}
def noBrokerDB : IR := {clean with edges := [⟨3,4,true,false,true⟩,⟨3,5,true,false,true⟩]}
def noReceiverDB : IR := {clean with edges := [⟨3,4,true,false,true⟩,⟨2,5,true,false,true⟩]}
end ControlStack.Deployment


namespace ControlStack.Deployment
open ControlStack

/-- Actual sink records are indexed in admission order, not wall-clock publication
order. This unproved correspondence allows admitted-but-unpublished records.
Caller binding and model transactions are separate from authority extraction. -/
structure BrokerProtocolRefinement (d : IR) (R : TrustedBroker.Roles) (cap : Nat)
    (t : TrustedBroker.State) (sinkNonces : List Nat) : Prop where
  transactions : TrustedBroker.Trace R (TrustedBroker.initial cap) t
  callerBinding : ∀ uid, R.agent uid → ∃ a ∈ d.nodes, a.agent = true ∧ uid = a.uid
  publication : List.Sublist sinkNonces.reverse t.consumed

end ControlStack.Deployment

namespace ControlStack.Deployment
open ControlStack
/-- Finite state identifiers refer to complete instantiated broker states.
Every executable table transition has a kernel-checked TrustedBroker step.
Identifiers avoid inventing decidable equality for arbitrary function states. -/
structure IndexedBrokerTable (R : TrustedBroker.Roles) where
  interpret : Nat → TrustedBroker.State
  step : Nat → Nat → Nat
  checked : ∀ s op, TrustedBroker.Step R (interpret s) (interpret (step s op))

end ControlStack.Deployment
