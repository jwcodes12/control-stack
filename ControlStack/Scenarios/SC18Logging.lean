/-
SC-18: an agent must not disable inference logging or monitoring.

An abstract serving-node model (pattern of `SC26Transaction.lean`):
- every inference request needs an append-only log record COMMITTED at the trusted log sink before its response is
  released (log-before-release);
- the node writes records to the sink named by its logging configuration; only admins may change that configuration,
  and admins only ever point it at the trusted sink (premise `legal`);
- the sink may go down at any time (adversary-controlled); a fail-closed watchdog halts serving if the sink has
  acknowledged nothing for more than `T` ticks;
- an absorbing admin HALT.

Main results (deployed configuration `full`; adversary class TRACE_ARBITRARY: any interleaving of requests, log writes,
releases, sink outages, ticks and configuration writes by any caller, under `legal`):
- `sc18_safe`: from `init`, every released response's record was in the trusted log AT THE MOMENT OF RELEASE (the log
  cut at its length then), the release happened within `T` ticks of the last sink acknowledgement, and no request is
  released twice;
- `config_untampered`: the logging configuration always names the trusted sink (agent writes are refused);
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`); non-vacuity `honest_logged_release`.

Necessity witnesses: `release_before_log_breaks`, `agent_writable_config_breaks` (an acknowledgement from a sink the
agent chose is not a trusted record), `fail_open_outage_breaks`, `watchdog_off_silent_release`, `no_halt_check_breaks`.

Premises outside the model: the sink's acknowledgement means durable commitment; the node cannot release responses by
any path other than `release`; admin credentials are not held by agents; the trusted sink's identity is authenticated.
Not claimed: that logged content is reviewed, or that the log is tamper-evident after commitment. No new mathematics:
inductions over the trace.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC18

open ControlStack.Gate

/-- a released response: request id, trusted-log length, clock and last acknowledgement time at release -/
structure Rel where
  id : ℕ
  llen : ℕ
  clock : ℕ
  lastAck : ℕ
deriving DecidableEq, Repr

structure St where
  reqs : List ℕ
  /-- the node's view: records some sink acknowledged -/
  acked : List ℕ
  /-- the trusted sink's committed log -/
  logged : List ℕ
  cfg : ℕ
  sinkUp : Bool
  clock : ℕ
  lastAck : ℕ
  released : List Rel
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | request (id : ℕ)
  | logWrite (id : ℕ)
  | release (id : ℕ)
  | setSink (caller v : ℕ)
  | sinkDown
  | sinkRestore
  | tick
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  logFirst : Bool
  failOpen : Bool
  cfgProtect : Bool
  watchdog : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, false, true, true, true⟩

/-- the initial state: logging points at the trusted sink, which is up -/
def init (trusted : ℕ) : St := ⟨[], [], [], trusted, true, 0, 0, [], false⟩

def step (admins : List ℕ) (trusted T : ℕ) (C : Checks) (s : St) : Op → St
  | .request id =>
    if s.halted ∧ C.haltCheck then s else if id ∉ s.reqs then { s with reqs := s.reqs ++ [id] } else s
  | .logWrite id =>
    if s.halted ∧ C.haltCheck then s
    else if id ∈ s.reqs ∧ s.sinkUp then
      { s with acked := s.acked ++ [id], lastAck := s.clock,
               logged := if s.cfg = trusted then s.logged ++ [id] else s.logged }
    else s
  | .release id =>
    if s.halted ∧ C.haltCheck then s
    else if id ∈ s.reqs ∧ id ∉ s.released.map Rel.id ∧
        (C.logFirst → id ∈ s.acked ∨ (C.failOpen ∧ s.sinkUp = false)) then
      { s with released := s.released ++ [⟨id, s.logged.length, s.clock, s.lastAck⟩] }
    else s
  | .setSink c v =>
    if s.halted ∧ C.haltCheck then s else if C.cfgProtect → c ∈ admins then { s with cfg := v } else s
  | .sinkDown => { s with sinkUp := false }
  | .sinkRestore => { s with sinkUp := true }
  | .tick =>
    if s.halted ∧ C.haltCheck then s
    else if C.watchdog ∧ s.lastAck + T < s.clock + 1 then { s with clock := s.clock + 1, halted := true }
    else { s with clock := s.clock + 1 }
  | .halt c => if c ∈ admins then { s with halted := true } else s

def run (admins : List ℕ) (trusted T : ℕ) (C : Checks) (s : St) (ops : List Op) : St :=
  ops.foldl (step admins trusted T C) s

theorem run_cons (admins : List ℕ) (trusted T : ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run admins trusted T C s (o :: ops) = run admins trusted T C (step admins trusted T C s o) ops := rfl

/-- premise: admins only ever point logging at the trusted sink -/
def legal (admins : List ℕ) (trusted : ℕ) : Op → Prop
  | .setSink c v => c ∈ admins → v = trusted
  | _ => True

/-! ## Invariant and safety -/

/-- a release whose record was in the trusted log when it happened, within `T` ticks of the last acknowledgement -/
def RelOk (T : ℕ) (s : St) (r : Rel) : Prop :=
  r.llen ≤ s.logged.length ∧ r.id ∈ s.logged.take r.llen ∧ r.clock ≤ r.lastAck + T

def Good (T : ℕ) (s : St) : Prop := (∀ r ∈ s.released, RelOk T s r) ∧ (s.released.map Rel.id).Nodup

structure Inv (trusted T : ℕ) (s : St) : Prop where
  cfg_ok : s.cfg = trusted
  ack_ok : ∀ x ∈ s.acked, x ∈ s.logged
  rel_ok : ∀ r ∈ s.released, RelOk T s r
  nodup : (s.released.map Rel.id).Nodup
  clk : s.halted = false → s.clock ≤ s.lastAck + T

theorem inv_init (trusted T : ℕ) : Inv trusted T (init trusted) :=
  ⟨rfl, by simp [init], by simp [init], by simp [init], fun _ => by simp [init]⟩

theorem RelOk.mono {T : ℕ} {s t : St} (hp : s.logged <+: t.logged) {r : Rel} (h : RelOk T s r) : RelOk T t r := by
  obtain ⟨u, hu⟩ := hp
  refine ⟨h.1.trans (hu ▸ by simp), ?_, h.2.2⟩
  rw [← hu, List.take_append_of_le_length h.1]
  exact h.2.1

theorem step_inv (admins : List ℕ) (trusted T : ℕ) (s : St) (o : Op) (ho : legal admins trusted o)
    (h : Inv trusted T s) : Inv trusted T (step admins trusted T full s o) := by
  cases o with
  | request id =>
    simp only [step]
    split_ifs
    all_goals first | exact h | exact ⟨h.cfg_ok, h.ack_ok, h.rel_ok, h.nodup, h.clk⟩
  | logWrite id =>
    simp only [step, h.cfg_ok, ite_true]
    split_ifs
    · exact h
    · refine ⟨rfl, fun x hx => ?_, fun r hr => RelOk.mono (List.prefix_append _ _) (h.rel_ok r hr), h.nodup,
        fun _ => Nat.le_add_right _ _⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact List.mem_append_left _ (h.ack_ok x hx)
      · simp at hx; subst hx; simp
    · exact h
  | release id =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · obtain ⟨_, hn, ha⟩ := h2
      simp only [full, true_implies, Bool.false_eq_true, false_and, or_false] at ha
      have hnh : s.halted = false := by
        cases hh : s.halted
        · rfl
        · exact absurd ⟨hh, rfl⟩ h1
      refine ⟨h.cfg_ok, h.ack_ok, fun r hr => ?_, ?_, h.clk⟩
      · rcases List.mem_append.1 hr with hr | hr
        · exact h.rel_ok r hr
        · simp at hr; subst hr
          refine ⟨le_rfl, ?_, h.clk hnh⟩
          rw [List.take_length]
          exact h.ack_ok id ha
      · simp only [List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.2 ⟨h.nodup, List.nodup_singleton _, fun a ha' b hb => ?_⟩
        simp only [List.mem_singleton] at hb
        subst hb
        rintro rfl
        exact hn ha'
    · exact h
  | setSink c v =>
    simp only [legal] at ho
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · have hc : c ∈ admins := h2 rfl
      exact ⟨ho hc, h.ack_ok, h.rel_ok, h.nodup, h.clk⟩
    · exact h
  | sinkDown => exact ⟨h.cfg_ok, h.ack_ok, h.rel_ok, h.nodup, h.clk⟩
  | sinkRestore => exact ⟨h.cfg_ok, h.ack_ok, h.rel_ok, h.nodup, h.clk⟩
  | tick =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · exact ⟨h.cfg_ok, h.ack_ok, h.rel_ok, h.nodup, fun hf => by simp at hf⟩
    · refine ⟨h.cfg_ok, h.ack_ok, h.rel_ok, h.nodup, fun _ => ?_⟩
      simp only [show full.watchdog = true from rfl, true_and, not_lt] at h2
      exact h2
  | halt c =>
    simp only [step]
    split_ifs
    · exact ⟨h.cfg_ok, h.ack_ok, h.rel_ok, h.nodup, fun hf => by simp at hf⟩
    · exact h

theorem run_inv (admins : List ℕ) (trusted T : ℕ) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal admins trusted o)
    (h : Inv trusted T s) : Inv trusted T (run admins trusted T full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih =>
    rw [run_cons]
    exact ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho'))
      (step_inv admins trusted T s o (hops o List.mem_cons_self) h)

/-- **SC-18 safety.** After any legal trace from `init`, every released response's record was in the trusted log at
the moment of release, the release came within `T` ticks of the last sink acknowledgement, and no request was released
twice. Adversary: TRACE_ARBITRARY under `legal`. -/
theorem sc18_safe (admins : List ℕ) (trusted T : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal admins trusted o) :
    Good T (run admins trusted T full (init trusted) ops) :=
  let h := run_inv admins trusted T _ ops hops (inv_init trusted T)
  ⟨h.rel_ok, h.nodup⟩

/-- **Configuration untampered**: after any legal trace, logging still names the trusted sink. -/
theorem config_untampered (admins : List ℕ) (trusted T : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal admins trusted o) :
    (run admins trusted T full (init trusted) ops).cfg = trusted :=
  (run_inv admins trusted T _ ops hops (inv_init trusted T)).cfg_ok

/-! ## Halt -/

theorem step_halted (admins : List ℕ) (trusted T : ℕ) (s : St) (o : Op) (hh : s.halted = true) :
    (step admins trusted T full s o).released = s.released ∧ (step admins trusted T full s o).halted = true := by
  cases o with
  | sinkDown => simp [step, hh]
  | sinkRestore => simp [step, hh]
  | halt c => simp only [step]; split_ifs <;> simp [hh]
  | _ => simp [step, full, hh]

/-- **Halt freezes serving**: once halted, by the watchdog or an admin, no trace releases anything. -/
theorem halt_freezes (admins : List ℕ) (trusted T : ℕ) (s : St) (ops : List Op) (hh : s.halted = true) :
    (run admins trusted T full s ops).released = s.released := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    rw [run_cons]
    obtain ⟨h1, h2⟩ := step_halted admins trusted T s o hh
    rw [ih _ h2, h1]

/-! ## Client of the shared gate interface -/

theorem released_prefix (admins : List ℕ) (trusted T : ℕ) (C : Checks) (s : St) (o : Op) :
    s.released <+: (step admins trusted T C s o).released := by
  cases o with
  | release id =>
    simp only [step]
    split_ifs
    · exact List.prefix_refl _
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  | sinkDown => exact List.prefix_refl _
  | sinkRestore => exact List.prefix_refl _
  | _ =>
    simp only [step]
    split_ifs
    all_goals exact List.prefix_refl _

def sys (admins : List ℕ) (trusted T : ℕ) : System St {o : Op // legal admins trusted o} Rel where
  step := fun s o => step admins trusted T full s o.1
  effects := St.released

def spec (admins : List ℕ) (trusted T : ℕ) : Spec (sys admins trusted T) where
  Inv := Inv trusted T
  ok := RelOk T
  step_inv := fun s o h => step_inv admins trusted T s o.1 o.2 h
  log_prefix := fun s o => released_prefix admins trusted T full s o.1
  inv_ok := fun _ h r hr => h.rel_ok r hr

/-! ## Non-vacuity and necessity witnesses

Admin 9, agent 1, trusted sink 0, watchdog threshold T = 2. -/

/-- **Non-vacuity**: a logged request is released. -/
theorem honest_logged_release :
    let s := run [9] 0 2 full (init 0) [.request 0, .logWrite 0, .release 0]
    s.released = [⟨0, 1, 0, 0⟩] ∧ s.logged = [0] := by
  decide

/-- releasing before logging: the record was not in the log when the response went out -/
theorem release_before_log_breaks :
    let s := run [9] 0 2 { full with logFirst := false } (init 0) [.request 0, .release 0, .logWrite 0]
    s.released = [⟨0, 0, 0, 0⟩] ∧ s.logged = [0] ∧
    (run [9] 0 2 full (init 0) [.request 0, .release 0, .logWrite 0]).released = [] := by
  decide

/-- an agent that can rewrite the logging configuration points it at its own sink: the response is released on that
sink's acknowledgement and the trusted log stays empty -/
theorem agent_writable_config_breaks :
    let s := run [9] 0 2 { full with cfgProtect := false } (init 0) [.setSink 1 7, .request 0, .logWrite 0, .release 0]
    s.released = [⟨0, 0, 0, 0⟩] ∧ s.logged = [] ∧
    (run [9] 0 2 full (init 0) [.setSink 1 7, .request 0, .logWrite 0, .release 0]).logged = [0] := by
  decide

/-- fail-open on a sink outage releases unlogged responses; fail-closed releases nothing -/
theorem fail_open_outage_breaks :
    (run [9] 0 2 { full with failOpen := true } (init 0) [.sinkDown, .request 0, .release 0]).released =
      [⟨0, 0, 0, 0⟩] ∧
    (run [9] 0 2 full (init 0) [.sinkDown, .request 0, .release 0]).released = [] := by
  decide

/-- without the watchdog, a response is released while the sink has been silent for longer than `T`; with it, the
node halts serving -/
theorem watchdog_off_silent_release :
    (run [9] 0 2 { full with watchdog := false } (init 0)
      [.request 0, .logWrite 0, .sinkDown, .tick, .tick, .tick, .release 0]).released = [⟨0, 1, 3, 0⟩] ∧
    (run [9] 0 2 full (init 0) [.request 0, .logWrite 0, .sinkDown, .tick, .tick, .tick, .release 0]).released = [] := by
  decide

/-- without the halt check, serving continues after an admin halt -/
theorem no_halt_check_breaks :
    (run [9] 0 2 { full with haltCheck := false } (init 0) [.halt 9, .request 0, .logWrite 0, .release 0]).released =
      [⟨0, 1, 0, 0⟩] ∧
    (run [9] 0 2 full (init 0) [.halt 9, .request 0, .logWrite 0, .release 0]).released = [] := by
  decide

end ControlStack.SC18

#print axioms ControlStack.SC18.sc18_safe
#print axioms ControlStack.SC18.config_untampered
#print axioms ControlStack.SC18.halt_freezes
#print axioms ControlStack.SC18.spec
#print axioms ControlStack.SC18.honest_logged_release
#print axioms ControlStack.SC18.release_before_log_breaks
#print axioms ControlStack.SC18.agent_writable_config_breaks
#print axioms ControlStack.SC18.fail_open_outage_breaks
#print axioms ControlStack.SC18.watchdog_off_silent_release
#print axioms ControlStack.SC18.no_halt_check_breaks
