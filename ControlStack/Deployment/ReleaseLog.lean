import ControlStack.Deployment.Provenance

/-!
Model-only release event log: Option A of `docs/lean-english/RELEASE-LOG-DESIGN.md`.

A *logged* release is exactly one broker `release` step, i.e. the broker's
committed transaction that admitted the request. It is NOT "the receiver
received the bytes" and NOT "the bytes were durably published": no publish
receipt, crash between admission and publication, or rehash of live content is
modeled. The log is a ghost, append-only projection of broker steps. The
historical broker `State`/`Step` and every pinned theorem are untouched.
Nothing here is a statement about the Python/SQLite broker, extraction
faithfulness, or log custody; those remain premises.
-/
namespace ControlStack.Deployment.ReleaseLog
open ControlStack
open TrustedBroker

/-- What the broker admitted at the instant of one release. -/
structure ReleaseEvent where
  nonce : Nat
  digest : Nat
  destination : Nat
  agent : Nat
  lease : Nat
  signer : Nat
  reviewer : Nat
  cost : Nat

/-- Broker state plus the ghost log, newest event first. -/
structure LoggedState where
  broker : State
  log : List ReleaseEvent

def LoggedState.initial (cap : Nat) : LoggedState :=
  { broker := TrustedBroker.initial cap, log := [] }

/-- The event of a release: the *approved* digest and destination, the signer,
and the reviewer entry present at that instant. -/
def eventOf (r : Request) (a : Approval) (reviewer : Nat) : ReleaseEvent :=
  { nonce := r.nonce, digest := a.digest, destination := a.destination,
    agent := r.uid, lease := r.lease, signer := a.signer,
    reviewer := reviewer, cost := r.cost }

/-- A broker step with the log extended exactly by release steps. Non-release
steps keep the log (the side condition `t.releases = s.releases` holds for
every constructor of `Step` except `release`). -/
inductive LStep (roles : Roles) : LoggedState → LoggedState → Prop
  | plain (ls : LoggedState) (t : State) (step : Step roles ls.broker t)
      (same : t.releases = ls.broker.releases) :
      LStep roles ls { broker := t, log := ls.log }
  | release (ls : LoggedState) (now : Nat) (r : Request) (a : Approval)
      (l : Lease) (reviewer : Nat)
      (allowed : Allowed roles ls.broker now r a l)
      (review : ls.broker.reviews r.digest = some reviewer) :
      LStep roles ls
        { broker := committed ls.broker r a l,
          log := eventOf r a reviewer :: ls.log }

inductive LTrace (roles : Roles) : LoggedState → LoggedState → Prop
  | nil (ls) : LTrace roles ls ls
  | cons {a b c} : LStep roles a b → LTrace roles b c → LTrace roles a c

/-- Forward simulation: every logged step projects to an existing broker step. -/
theorem lstep_forget (roles : Roles) {ls ls' : LoggedState}
    (h : LStep roles ls ls') : Step roles ls.broker ls'.broker := by
  cases h with
  | plain t step _ => exact step
  | release now r a l reviewer allowed _ => exact Step.release _ now r a l allowed

theorem ltrace_forget (roles : Roles) {ls ls' : LoggedState}
    (h : LTrace roles ls ls') : Trace roles ls.broker ls'.broker := by
  induction h with
  | nil => exact Trace.nil _
  | cons step _ ih => exact Trace.cons (lstep_forget roles step) ih

/-- Non-release steps change neither the nonce history nor the spent total. -/
theorem step_nonrelease_fields (roles : Roles) (s t : State)
    (step : Step roles s t) (same : t.releases = s.releases) :
    t.consumed = s.consumed ∧ t.spent = s.spent := by
  cases step <;> simp_all [committed]

/-- The log is a faithful shadow of the broker counters and nonce history. -/
def LogSound (ls : LoggedState) : Prop :=
  ls.log.map (·.nonce) = ls.broker.consumed ∧
  (ls.log.map (·.cost)).sum = ls.broker.spent ∧
  ls.log.length = ls.broker.releases

theorem logSound_initial (cap : Nat) : LogSound (LoggedState.initial cap) := by
  simp [LogSound, LoggedState.initial, TrustedBroker.initial]

theorem logSound_step (roles : Roles) {ls ls' : LoggedState}
    (sound : LogSound ls) (h : LStep roles ls ls') : LogSound ls' := by
  obtain ⟨hn, hc, hl⟩ := sound
  cases h with
  | plain t step same =>
      obtain ⟨hcons, hspent⟩ := step_nonrelease_fields roles _ _ step same
      exact ⟨hn.trans hcons.symm, hc.trans hspent.symm, hl.trans same.symm⟩
  | release now r a l reviewer allowed review =>
      refine ⟨?_, ?_, ?_⟩
      · simp [eventOf, committed, hn]
      · simp [eventOf, committed, hc, Nat.add_comm]
      · simp [committed, hl]

theorem ltrace_logSound (roles : Roles) {ls ls' : LoggedState}
    (sound : LogSound ls) (h : LTrace roles ls ls') : LogSound ls' := by
  induction h with
  | nil => exact sound
  | cons step _ ih => exact ih (logSound_step roles sound step)

/-- Append-only: a later log extends the earlier one by new (newer) events. -/
theorem lstep_log_extends (roles : Roles) {ls ls' : LoggedState}
    (h : LStep roles ls ls') : ∃ pre, ls'.log = pre ++ ls.log := by
  cases h with
  | plain => exact ⟨[], rfl⟩
  | release now r a l reviewer => exact ⟨[eventOf r a reviewer], rfl⟩

theorem ltrace_log_extends (roles : Roles) {ls ls' : LoggedState}
    (h : LTrace roles ls ls') : ∃ pre, ls'.log = pre ++ ls.log := by
  induction h with
  | nil => exact ⟨[], rfl⟩
  | cons step _ ih =>
      obtain ⟨p1, h1⟩ := lstep_log_extends roles step
      obtain ⟨p2, h2⟩ := ih
      exact ⟨p2 ++ p1, by rw [h2, h1, List.append_assoc]⟩

/-- Event-time facts, available at the instant of release from the guard alone:
the logged digest/destination are the *approved* ones and equal the request's;
the signer is an approver; the agent is an agent; the cost is positive. -/
theorem release_event_matches (roles : Roles) (s : State) (now : Nat)
    (r : Request) (a : Approval) (l : Lease) (reviewer : Nat)
    (allowed : Allowed roles s now r a l) :
    (eventOf r a reviewer).nonce = r.nonce ∧
    (eventOf r a reviewer).digest = r.digest ∧
    (eventOf r a reviewer).destination = r.destination ∧
    (eventOf r a reviewer).lease = r.lease ∧
    s.approvals (eventOf r a reviewer).nonce = some a ∧
    roles.agent (eventOf r a reviewer).agent ∧
    roles.approver (eventOf r a reviewer).signer ∧
    0 < (eventOf r a reviewer).cost := by
  obtain ⟨_, agent, lookup, _, dig, dest, _, _, approver, _, _, _, _, _,
    positive, _⟩ := allowed
  exact ⟨rfl, dig, dest, rfl, lookup, agent, approver, positive⟩

/-- Every event in a log reached from the initial state satisfies the role and
cost facts, including the reviewer's role (from review provenance). -/
def LogAuthentic (roles : Roles) (ls : LoggedState) : Prop :=
  Provenance.ReviewProvenance roles ls.broker ∧
  ∀ e ∈ ls.log, roles.agent e.agent ∧ roles.approver e.signer ∧
    roles.reviewer e.reviewer ∧ 0 < e.cost

theorem logAuthentic_initial (roles : Roles) (cap : Nat) :
    LogAuthentic roles (LoggedState.initial cap) :=
  ⟨Provenance.initial_review roles cap, by simp [LoggedState.initial]⟩

theorem logAuthentic_step (roles : Roles) {ls ls' : LoggedState}
    (h : LogAuthentic roles ls) (step : LStep roles ls ls') :
    LogAuthentic roles ls' := by
  obtain ⟨reviews, events⟩ := h
  refine ⟨Provenance.review_step roles _ _ reviews (lstep_forget roles step), ?_⟩
  cases step with
  | plain t _ _ => exact events
  | release now r a l reviewer allowed review =>
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · obtain ⟨_, _, _, _, _, agent, approver, positive⟩ :=
          release_event_matches roles _ now r a l reviewer allowed
        exact ⟨agent, approver, (reviews _ _ review).1, positive⟩
      · exact events e he

theorem ltrace_logAuthentic (roles : Roles) {ls ls' : LoggedState}
    (h : LogAuthentic roles ls) (t : LTrace roles ls ls') :
    LogAuthentic roles ls' := by
  induction t with
  | nil => exact h
  | cons step _ ih => exact ih (logAuthentic_step roles h step)

/-- Conservative extension: every broker step has a logged counterpart, so the
log constrains nothing about what the broker can do. -/
theorem lift_step (roles : Roles) {s t : State} (step : Step roles s t)
    (log : List ReleaseEvent) :
    ∃ log', LStep roles { broker := s, log := log } { broker := t, log := log' } := by
  cases step with
  | release now r a l allowed =>
      obtain ⟨reviewer, review⟩ := allowed.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      exact ⟨_, LStep.release { broker := s, log := log } now r a l reviewer allowed review⟩
  | deny => exact ⟨log, LStep.plain _ _ (Step.deny _) rfl⟩
  | stage uid digest live role =>
      exact ⟨log, LStep.plain _ _ (Step.stage _ uid digest live role) rfl⟩
  | review uid digest live role ex =>
      exact ⟨log, LStep.plain _ _ (Step.review _ uid digest live role ex) rfl⟩
  | issue uid key l now live role agent fresh budget unused active future =>
      exact ⟨log, LStep.plain _ _ (Step.issue _ uid key l now live role agent fresh budget unused active future) rfl⟩
  | approve uid nonce a l now reviewer live role signer agent fresh unused review
      reviewRole distinct lease owner active leaseFuture future =>
      exact ⟨log, LStep.plain _ _ (Step.approve _ uid nonce a l now reviewer live role signer agent fresh unused review reviewRole distinct lease owner active leaseFuture future) rfl⟩
  | revoke uid key l live role lease =>
      exact ⟨log, LStep.plain _ _ (Step.revoke _ uid key l live role lease) rfl⟩
  | halt uid role => exact ⟨log, LStep.plain _ _ (Step.halt _ uid role) rfl⟩

theorem lift_trace (roles : Roles) {s t : State} (tr : Trace roles s t)
    (log : List ReleaseEvent) :
    ∃ log', LTrace roles { broker := s, log := log } { broker := t, log := log' } := by
  induction tr generalizing log with
  | nil => exact ⟨log, LTrace.nil _⟩
  | cons step _ ih =>
      obtain ⟨log1, h1⟩ := lift_step roles step log
      obtain ⟨log2, h2⟩ := ih log1
      exact ⟨log2, LTrace.cons h1 h2⟩

/-- A release is only admitted for a nonce not yet in the log, so no nonce is
ever logged twice (the log's nonce list equals the consumed-nonce history). -/
theorem release_nonce_new_in_log (roles : Roles) {ls : LoggedState}
    (sound : LogSound ls) (now : Nat) (r : Request) (a : Approval) (l : Lease)
    (allowed : Allowed roles ls.broker now r a l) :
    r.nonce ∉ ls.log.map (·.nonce) := by
  rw [sound.1]
  exact allowed.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- After a release, the same nonce can never be admitted again. -/
theorem no_duplicate_release_event (roles : Roles) (s : State)
    (r : Request) (a : Approval) (l : Lease)
    (now' : Nat) (r' : Request) (a' : Approval) (l' : Lease)
    (same : r'.nonce = r.nonce) :
    ¬ Allowed roles (committed s r a l) now' r' a' l' :=
  committed_nonce_unusable roles s r a l now' r' a' l' same

/-- After HALT no further event is ever logged. -/
theorem halted_no_new_events (roles : Roles) {ls ls' : LoggedState}
    (sound : LogSound ls) (halted : ls.broker.halted = true)
    (h : LStep roles ls ls') : ls'.log.length = ls.log.length := by
  obtain ⟨_, _, hl⟩ := sound
  have step := lstep_forget roles h
  obtain ⟨_, hrel⟩ := halted_absorbing roles _ _ halted step
  cases h with
  | plain t _ same => rfl
  | release now r a l reviewer allowed review =>
      simp [committed] at hrel

/-- Every published nonce of a `BrokerProtocolRefinement` has a release event,
with role and cost facts, in a logged shadow of the broker trace. -/
theorem deployment_release_events (d : IR) (R : Roles) (cap : Nat)
    (t : State) (sinkNonces : List Nat)
    (refinement : BrokerProtocolRefinement d R cap t sinkNonces) :
    ∃ log, LTrace R (LoggedState.initial cap) { broker := t, log := log } ∧
      LogSound { broker := t, log := log } ∧
      ∀ n ∈ sinkNonces, ∃ e ∈ log, e.nonce = n ∧ R.agent e.agent ∧
        R.approver e.signer ∧ R.reviewer e.reviewer ∧ 0 < e.cost := by
  obtain ⟨log, tr⟩ := lift_trace R refinement.transactions []
  have sound := ltrace_logSound R (logSound_initial cap) tr
  have auth := ltrace_logAuthentic R (logAuthentic_initial R cap) tr
  refine ⟨log, tr, sound, ?_⟩
  intro n hn
  have member : n ∈ t.consumed :=
    refinement.publication.subset (List.mem_reverse.mpr hn)
  have viaLog : n ∈ log.map (·.nonce) := by rw [sound.1]; exact member
  obtain ⟨e, he, eq⟩ := List.mem_map.mp viaLog
  exact ⟨e, he, eq, auth.2 e he⟩

#print axioms lstep_forget
#print axioms ltrace_forget
#print axioms logSound_step
#print axioms ltrace_logSound
#print axioms ltrace_log_extends
#print axioms release_event_matches
#print axioms ltrace_logAuthentic
#print axioms lift_trace
#print axioms release_nonce_new_in_log
#print axioms no_duplicate_release_event
#print axioms halted_no_new_events
#print axioms deployment_release_events
end ControlStack.Deployment.ReleaseLog
