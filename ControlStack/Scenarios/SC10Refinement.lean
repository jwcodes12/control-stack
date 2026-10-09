/-
SC-10 candidate concrete-event refinement (2026-10-09).

Source-pinned target: main at 37e118ecfb5c923d94edd15100fc867fd8ab32da,
scenarios/SC-10/harness/store.py and run_sc10.py.

This finite event machine distinguishes SO_PEERCRED pid-bearing write requests,
latest-policy reads, decisions, alternate evaluation requests, writable paths,
pinned builds, and HALT. It deliberately models only the successful, atomic
single-threaded store/event boundary. It is NOT yet a proof that the Python store
or the host kernel implement these events: socket framing, pid authentication,
process lifetime, filesystem recovery, replay, external enforcement effects,
scheduler interleavings, and alternate entry points are residual premises.

The proof transfers the existing SC10.sc10_safe claim through a forward simulation,
rather than restating the property of the concrete state as a hypothesis.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC10Policy

namespace ControlStack.SC10Refinement

structure Config where
  adminPids : List ℕ
  digest : ℕ → ℕ
  pinnedBinary : ℕ
  pinnedDigest : ℕ

/-- Concrete store state: separate policy append log, read-cache, alternate
files, decision receipts, build receipts, and HALT state. -/
structure CSt where
  policyLog : List (ℕ × ℕ)
  cached : Option ℕ
  alternativePolicy : ℕ
  pathBinary : ℕ
  decisionReceipts : List SC10.Dec
  buildReceipts : List ℕ
  stopped : Bool
deriving DecidableEq, Repr

/-- Requests at the store/tool boundary, NOT arbitrary bytes or syscalls. -/
inductive Event where
  | commit (peerPid value : ℕ)
  | readCache
  | enforce (request : ℕ)
  | editAlt (value : ℕ)
  | alternateEnforce (request : ℕ)
  | editPath (binary : ℕ)
  | build
  | stop (peerPid : ℕ)
deriving DecidableEq, Repr

def cinit : CSt := ⟨[], none, 0, 0, [], [], false⟩

def newest (s : CSt) : Option ℕ :=
  if s.policyLog = [] then none else some (s.policyLog.length - 1)

/-- Implemented reference transition. A fresh enforcement query uses the
store's latest version (no cache) and alternate evaluation is refused. -/
def stepC (K : Config) (s : CSt) : Event → CSt
  | .commit pid v =>
      if s.stopped then s
      else if pid ∈ K.adminPids then
        { s with policyLog := s.policyLog ++ [(v, pid)] }
      else s
  | .readCache =>
      if s.stopped then s else { s with cached := newest s }
  | .enforce req =>
      if s.stopped then s
      else match newest s with
        | none => s
        | some i =>
            match s.policyLog[i]? with
            | none => s
            | some vw =>
                { s with decisionReceipts :=
                    s.decisionReceipts ++ [⟨req, some i, vw.1, s.policyLog.length⟩] }
  | .editAlt v =>
      if s.stopped then s else { s with alternativePolicy := v }
  | .alternateEnforce _ => s
  | .editPath b =>
      if s.stopped then s else { s with pathBinary := b }
  | .build =>
      if s.stopped then s
      else { s with buildReceipts := s.buildReceipts ++ [K.pinnedBinary] }
  | .stop pid =>
      if pid ∈ K.adminPids then { s with stopped := true } else s

def runC (K : Config) (s : CSt) (events : List Event) : CSt :=
  events.foldl (stepC K) s

def envOf (K : Config) : SC10.Env :=
  ⟨K.adminPids, K.digest, K.pinnedBinary, K.pinnedDigest⟩

def alpha (s : CSt) : SC10.St :=
  ⟨s.policyLog, s.cached, s.alternativePolicy, s.pathBinary,
    s.decisionReceipts, s.buildReceipts, s.stopped⟩

def abstractEvent : Event → SC10.Op
  | .commit pid v => .writePolicy pid v
  | .readCache => .refresh
  | .enforce req => .decide req
  | .editAlt v => .writeAlt v
  | .alternateEnforce req => .altDecide req
  | .editPath b => .writePath b
  | .build => .build
  | .stop pid => .halt pid

/-- Local simulation: every concrete event is reflected by precisely its
corresponding SC10 abstract event, including declined writes and bypasses. -/
theorem simulation_step (K : Config) (s : CSt) (e : Event) :
    alpha (stepC K s e) =
      SC10.step (envOf K) SC10.full (alpha s) (abstractEvent e) := by
  cases s with
  | mk log cache alt path decisions builds stopped =>
    cases stopped <;> cases e <;>
      simp [stepC, alpha, envOf, abstractEvent, newest,
            SC10.step, SC10.full, SC10.latest] <;>
      (split_ifs <;> simp_all) <;>
      (cases hlookup : log[log.length - 1]? <;> simp_all [hlookup])

/-- Trace-level simulation is proved from per-event simulation. -/
theorem simulation_run (K : Config) (s : CSt) (events : List Event) :
    alpha (runC K s events) =
      SC10.run (envOf K) SC10.full (alpha s) (events.map abstractEvent) := by
  induction events generalizing s with
  | nil => rfl
  | cons e es ih =>
    change alpha (runC K (stepC K s e) es) =
      SC10.run (envOf K) SC10.full
        (SC10.step (envOf K) SC10.full (alpha s) (abstractEvent e))
        (es.map abstractEvent)
    rw [ih (stepC K s e), simulation_step K s e]

theorem alpha_init : alpha cinit = SC10.init := rfl

/-- Existing abstract safety transferred to every event sequence of the
new event machine. Digest equality is an EXPLICIT premise. -/
theorem concrete_safe (K : Config)
    (hpin : K.digest K.pinnedBinary = K.pinnedDigest) (events : List Event) :
    SC10.Good (envOf K) (alpha (runC K cinit events)) := by
  rw [simulation_run, alpha_init]
  exact SC10.sc10_safe (envOf K) hpin (events.map abstractEvent)

/-- All accepted policy writes have the authenticated admin pid in this
machine. Authentication of the actual SO_PEERCRED observation is NOT proved. -/
theorem concrete_admin_only (K : Config)
    (hpin : K.digest K.pinnedBinary = K.pinnedDigest) (events : List Event) :
    ∀ v ∈ (runC K cinit events).policyLog, v.2 ∈ K.adminPids := by
  have h := SC10.policy_admin_only (envOf K) hpin (events.map abstractEvent)
  have he := simulation_run K cinit events
  rw [alpha_init] at he
  rw [← he] at h
  exact h

/-- Distinguishing control: a stale-policy enforcement path after a policy
tightening chooses a different version than the fresh reference machine. -/
def staleStep (K : Config) (s : CSt) : Event → CSt
  | .enforce req =>
      if s.stopped then s
      else match s.cached with
        | none => s
        | some i =>
            match s.policyLog[i]? with
            | none => s
            | some vw =>
                { s with decisionReceipts :=
                    s.decisionReceipts ++ [⟨req, some i, vw.1, s.policyLog.length⟩] }
  | e => stepC K s e

def staleRun (K : Config) (s : CSt) (es : List Event) : CSt :=
  es.foldl (staleStep K) s

def testConfig : Config := ⟨[9], id, 40, 40⟩

theorem stale_cache_counterexample :
    (staleRun testConfig cinit
      [.commit 9 5, .readCache, .commit 9 6, .enforce 1]).decisionReceipts =
       [⟨1, some 0, 5, 2⟩] ∧
    (runC testConfig cinit
      [.commit 9 5, .readCache, .commit 9 6, .enforce 1]).decisionReceipts =
       [⟨1, some 1, 6, 2⟩] := by
  decide

end ControlStack.SC10Refinement

#print axioms ControlStack.SC10Refinement.simulation_step
#print axioms ControlStack.SC10Refinement.simulation_run
#print axioms ControlStack.SC10Refinement.concrete_safe
#print axioms ControlStack.SC10Refinement.concrete_admin_only
#print axioms ControlStack.SC10Refinement.stale_cache_counterexample
