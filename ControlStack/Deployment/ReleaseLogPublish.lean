import ControlStack.Deployment.ReleaseLogWitnesses

/-!
Publication side of the release event log (model only). `ReleaseLog` logs the
broker's committed release; here an abstract *receipt* records that the receiver
published the artifact for an admitted event, with the digest and destination it
actually observed. Added to cover the design doc's acceptance cases:
admitted-but-unpublished (crash between admission and publication), receiver
retry, HALT in flight, and a false-extraction countermodel.

Premises, stated in the constructors and not proved: the receiver publishes
the *approved* digest and destination (`publish`: faithful extraction), the log
and the receipts are durable across a crash (`crash` is the identity), and
publication is atomic with its receipt. There is no byte-level, filesystem or
SQLite statement here, and no rollback or log-custody guarantee.
-/
namespace ControlStack.Deployment.ReleaseLogPublish
open ControlStack
open ControlStack.TrustedBroker
open ControlStack.Deployment.ReleaseLog

/-- What the receiver observed when it published. -/
structure Receipt where
  nonce : Nat
  digest : Nat
  destination : Nat
deriving DecidableEq

/-- The receipt of a faithful publication of `e`. -/
def Receipt.ofEvent (e : ReleaseEvent) : Receipt := ⟨e.nonce, e.digest, e.destination⟩

structure PState where
  logged : LoggedState
  receipts : List Receipt

def PState.initial (cap : Nat) : PState :=
  { logged := LoggedState.initial cap, receipts := [] }

inductive PStep (roles : Roles) : PState → PState → Prop
  /-- a logged broker step (including `release`, which appends an event) -/
  | broker (p : PState) (ls : LoggedState) (h : LStep roles p.logged ls) :
      PStep roles p { logged := ls, receipts := p.receipts }
  /-- the receiver publishes an admitted event, once: no receipt for this nonce yet.
  The receipt carries the approved digest and destination (faithful extraction). -/
  | publish (p : PState) (e : ReleaseEvent) (admitted : e ∈ p.logged.log)
      (fresh : ∀ r ∈ p.receipts, r.nonce ≠ e.nonce) :
      PStep roles p { logged := p.logged, receipts := Receipt.ofEvent e :: p.receipts }
  /-- crash and restart: log and receipts are durable (a premise) -/
  | crash (p : PState) : PStep roles p p

inductive PTrace (roles : Roles) : PState → PState → Prop
  | nil (p) : PTrace roles p p
  | cons {a b c} : PStep roles a b → PTrace roles b c → PTrace roles a c

/-- Every receipt is for an admitted event and carries that event's digest and
destination; at most one receipt per nonce. -/
def PInv (p : PState) : Prop :=
  (∀ r ∈ p.receipts, ∃ e ∈ p.logged.log,
    e.nonce = r.nonce ∧ e.digest = r.digest ∧ e.destination = r.destination) ∧
  (p.receipts.map (·.nonce)).Nodup

theorem pInv_initial (cap : Nat) : PInv (PState.initial cap) := by
  simp [PInv, PState.initial]

theorem pInv_step (roles : Roles) {p q : PState} (h : PInv p) (st : PStep roles p q) :
    PInv q := by
  obtain ⟨match_, nodup⟩ := h
  cases st with
  | broker ls hl =>
      refine ⟨fun r hr => ?_, nodup⟩
      obtain ⟨e, he, rest⟩ := match_ r hr
      obtain ⟨pre, hpre⟩ := lstep_log_extends roles hl
      exact ⟨e, by rw [hpre]; exact List.mem_append_right _ he, rest⟩
  | publish e admitted fresh =>
      refine ⟨fun r hr => ?_, ?_⟩
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨e, admitted, rfl, rfl, rfl⟩
        · exact match_ r hr
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, nodup⟩
        obtain ⟨r, hr, hn⟩ := List.mem_map.mp hmem
        exact fresh r hr hn
  | crash => exact ⟨match_, nodup⟩

theorem ptrace_pInv (roles : Roles) {p q : PState} (h : PInv p) (t : PTrace roles p q) :
    PInv q := by
  induction t with
  | nil => exact h
  | cons st _ ih => exact ih (pInv_step roles h st)

/-- Published is a subset of admitted, with event-time digest and destination. -/
theorem receipt_matches_event (roles : Roles) (cap : Nat) {q : PState}
    (t : PTrace roles (PState.initial cap) q) :
    ∀ r ∈ q.receipts, ∃ e ∈ q.logged.log,
      e.nonce = r.nonce ∧ e.digest = r.digest ∧ e.destination = r.destination :=
  (ptrace_pInv roles (pInv_initial cap) t).1

/-- Retry and replay: along any trace from the initial state there is at most one
receipt per nonce, so a retried publication cannot produce a second one. -/
theorem receipts_nodup (roles : Roles) (cap : Nat) {q : PState}
    (t : PTrace roles (PState.initial cap) q) : (q.receipts.map (·.nonce)).Nodup :=
  (ptrace_pInv roles (pInv_initial cap) t).2

/-- Published is no more than admitted. -/
theorem published_le_admitted (roles : Roles) (cap : Nat) {q : PState}
    (t : PTrace roles (PState.initial cap) q) :
    q.receipts.length ≤ q.logged.log.length := by
  have inv := ptrace_pInv roles (pInv_initial cap) t
  have sub : (q.receipts.map (·.nonce)) ⊆ (q.logged.log.map (·.nonce)) := by
    intro n hn
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hn
    obtain ⟨e, he, hnonce, _⟩ := inv.1 r hr
    exact List.mem_map.mpr ⟨e, he, hnonce⟩
  have := (inv.2.subperm sub).length_le
  simpa using this

/-- A logged trace lifts to a publication trace with the receipts unchanged. -/
theorem ltrace_ptrace (roles : Roles) {a b : LoggedState} (rs : List Receipt)
    (h : LTrace roles a b) :
    PTrace roles { logged := a, receipts := rs } { logged := b, receipts := rs } := by
  induction h with
  | nil => exact PTrace.nil _
  | cons st _ ih => exact PTrace.cons (PStep.broker _ _ st) ih

/-- Countermodel for the faithful-extraction premise: a receiver that records an
observed digest of its own choosing (any admitted nonce, any bytes) breaks the
invariant. This is why `publish` states the approved digest as a premise. -/
inductive PStepWeak (roles : Roles) : PState → PState → Prop
  | strong {p q} (h : PStep roles p q) : PStepWeak roles p q
  | publishAny (p : PState) (r : Receipt) (admitted : ∃ e ∈ p.logged.log, e.nonce = r.nonce) :
      PStepWeak roles p { logged := p.logged, receipts := r :: p.receipts }

end ControlStack.Deployment.ReleaseLogPublish

namespace ControlStack.Deployment.ReleaseLogPublishWitnesses
open ControlStack
open ControlStack.Deployment
open ControlStack.Deployment.ReleaseLog
open ControlStack.Deployment.ReleaseLogPublish

abbrev R := Witnesses.R

/-- Admitted, nothing published yet: the state after a crash between admission and publication. -/
def admitted : PState :=
  { logged := { broker := Witnesses.s5, log := [ReleaseLogWitnesses.event] }, receipts := [] }

theorem admitted_reachable : PTrace R (PState.initial 1) admitted :=
  ltrace_ptrace R [] ReleaseLogWitnesses.logged_trace

theorem admitted_is_unpublished : admitted.logged.log ≠ [] ∧ admitted.receipts = [] :=
  ⟨by simp [admitted], rfl⟩

/-- Crash and restart keep the admitted event, and the receiver can then publish it. -/
def recovered : PState :=
  { logged := admitted.logged,
    receipts := [Receipt.ofEvent ReleaseLogWitnesses.event] }

theorem crash_then_publish : PStep R admitted admitted ∧ PStep R admitted recovered :=
  ⟨PStep.crash _, PStep.publish admitted ReleaseLogWitnesses.event (by simp [admitted])
    (by simp [admitted])⟩

theorem recovered_receipt :
    recovered.receipts = [⟨7, 23, 1⟩] := by decide

/-- Retry: with the receipt present, the publish premise (`fresh`) fails. -/
theorem retry_refused :
    ¬ (∀ r ∈ recovered.receipts, r.nonce ≠ ReleaseLogWitnesses.event.nonce) := by
  intro h
  exact h (Receipt.ofEvent ReleaseLogWitnesses.event) (by simp [recovered]) rfl

/-- HALT in flight: after a HALT step the admitted event can still be published
(delivery of already-admitted work), while no new event can be admitted. -/
def haltedAdmitted : PState :=
  { logged := { broker := { Witnesses.s5 with halted := true },
                log := [ReleaseLogWitnesses.event] }, receipts := [] }

theorem halt_in_flight :
    PStep R admitted haltedAdmitted ∧
    ∃ q, PStep R haltedAdmitted q ∧ q.receipts ≠ [] := by
  refine ⟨?_, ?_⟩
  · exact PStep.broker admitted haltedAdmitted.logged
      (LStep.plain admitted.logged _ (TrustedBroker.Step.halt Witnesses.s5 23700 rfl) rfl)
  · exact ⟨_, PStep.publish haltedAdmitted ReleaseLogWitnesses.event (by simp [haltedAdmitted])
      (by simp [haltedAdmitted]), by simp⟩

/-- False extraction: a receiver that records digest 99 for the admitted nonce 7
(approved digest 23) leaves the invariant. -/
def forged : PState :=
  { logged := admitted.logged, receipts := [⟨7, 99, 1⟩] }

theorem false_extraction_breaks_invariant :
    PInv admitted ∧ PStepWeak R admitted forged ∧ ¬ PInv forged := by
  refine ⟨?_, ?_, ?_⟩
  · simp [PInv, admitted]
  · exact PStepWeak.publishAny admitted ⟨7, 99, 1⟩ ⟨ReleaseLogWitnesses.event, by simp [admitted],
      by decide⟩
  · intro h
    obtain ⟨e, he, _, hd, _⟩ := h.1 ⟨7, 99, 1⟩ (by simp [forged])
    simp [forged, admitted] at he
    subst he
    revert hd
    decide

end ControlStack.Deployment.ReleaseLogPublishWitnesses

#print axioms ControlStack.Deployment.ReleaseLogPublish.pInv_step
#print axioms ControlStack.Deployment.ReleaseLogPublish.receipt_matches_event
#print axioms ControlStack.Deployment.ReleaseLogPublish.receipts_nodup
#print axioms ControlStack.Deployment.ReleaseLogPublish.published_le_admitted
#print axioms ControlStack.Deployment.ReleaseLogPublishWitnesses.admitted_reachable
#print axioms ControlStack.Deployment.ReleaseLogPublishWitnesses.crash_then_publish
#print axioms ControlStack.Deployment.ReleaseLogPublishWitnesses.retry_refused
#print axioms ControlStack.Deployment.ReleaseLogPublishWitnesses.halt_in_flight
#print axioms ControlStack.Deployment.ReleaseLogPublishWitnesses.false_extraction_breaks_invariant
