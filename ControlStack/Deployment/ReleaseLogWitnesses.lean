import ControlStack.Deployment.ReleaseLog
import ControlStack.Deployment.Witnesses

/-!
Positive and negative *model* witnesses for the release event log. They reuse
the guarded broker trace of `Witnesses` (stage, review, lease, approval, one
release). No live container, receiver or file bytes are involved, and the log
records the broker's committed transaction, not publication.
-/
namespace ControlStack.Deployment.ReleaseLogWitnesses
open ControlStack
open ControlStack.Deployment
open ControlStack.Deployment.ReleaseLog

/-- The one event the witness trace logs. -/
def event : ReleaseEvent := eventOf Witnesses.request Witnesses.approval 23703

/-- The guarded trace of `Witnesses`, with its ghost log. -/
theorem logged_trace :
    LTrace Witnesses.R (LoggedState.initial 1) { broker := Witnesses.s5, log := [event] } := by
  refine LTrace.cons (b := { broker := Witnesses.s1, log := [] })
    (LStep.plain (LoggedState.initial 1) Witnesses.s1 Witnesses.staged rfl) ?_
  refine LTrace.cons (b := { broker := Witnesses.s2, log := [] })
    (LStep.plain { broker := Witnesses.s1, log := [] } Witnesses.s2 Witnesses.reviewed rfl) ?_
  refine LTrace.cons (b := { broker := Witnesses.s3, log := [] })
    (LStep.plain { broker := Witnesses.s2, log := [] } Witnesses.s3 Witnesses.issued rfl) ?_
  refine LTrace.cons (b := { broker := Witnesses.s4, log := [] })
    (LStep.plain { broker := Witnesses.s3, log := [] } Witnesses.s4 Witnesses.approved rfl) ?_
  exact LTrace.cons
    (LStep.release { broker := Witnesses.s4, log := [] } 0 Witnesses.request
      Witnesses.approval Witnesses.lease 23703 Witnesses.release_allowed (by decide))
    (LTrace.nil _)

/-- The logged event carries the approved digest and destination, the signer,
the release-time reviewer and the cost. -/
theorem event_fields :
    event.nonce = 7 ∧ event.digest = 23 ∧ event.destination = 1 ∧
    event.agent = 23701 ∧ event.lease = 9 ∧ event.signer = 23704 ∧
    event.reviewer = 23703 ∧ event.cost = 1 := by decide

theorem witness_log_sound :
    LogSound { broker := Witnesses.s5, log := [event] } :=
  ltrace_logSound Witnesses.R (logSound_initial 1) logged_trace

/-- Negative: the replay of the released nonce is refused, so no second event
can be logged for it. -/
theorem replay_emits_no_event :
    ¬ TrustedBroker.Allowed Witnesses.R Witnesses.s5 0 Witnesses.request
        Witnesses.approval Witnesses.lease :=
  Witnesses.replay_refuted

/-- Negative: a tampered artifact (`intact` false) is refused by the guard, so
no release step, and hence no event, exists for it. -/
theorem tampered_emits_no_event :
    ¬ TrustedBroker.Allowed Witnesses.R Witnesses.tampered 0 Witnesses.request
        Witnesses.approval Witnesses.lease :=
  Witnesses.tampered_payload_refutes

/-- Limit, not a success: the broker admitted a release (one event) while the
sink publication list is empty. A logged release is therefore *not* evidence of
publication, and there is no publish receipt in the model. -/
theorem admitted_not_published :
    Nonempty (BrokerProtocolRefinement clean Witnesses.R 1 Witnesses.s5 []) ∧
    Witnesses.s5.releases = 1 := by
  refine ⟨⟨{ Witnesses.refined with publication := List.nil_sublist _ }⟩, by decide⟩

end ControlStack.Deployment.ReleaseLogWitnesses

#print axioms ControlStack.Deployment.ReleaseLogWitnesses.logged_trace
#print axioms ControlStack.Deployment.ReleaseLogWitnesses.event_fields
#print axioms ControlStack.Deployment.ReleaseLogWitnesses.witness_log_sound
#print axioms ControlStack.Deployment.ReleaseLogWitnesses.replay_emits_no_event
#print axioms ControlStack.Deployment.ReleaseLogWitnesses.tampered_emits_no_event
#print axioms ControlStack.Deployment.ReleaseLogWitnesses.admitted_not_published
