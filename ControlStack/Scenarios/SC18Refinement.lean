/-
SC-18 refinement: the runtime's event structure (scenarios/SC-18/harness/proxy.py, log_sink.py, reconcile.py;
prereg/SC18-LOG-PROXY.md) as a concrete machine, with a forward simulation into `SC18Liveness.Resume`, the
non-absorbing watchdog variant. That variant is the one the runtime implements: it resumes when the sink answers
again. This is criterion 3, as for SC-26, SC-25 and SC-16.

Concrete machine (`CSt`, `COp`, `stepC`), one event per runtime action:
- `arrive id`: an HTTP request reaches the proxy. It is refused while the watchdog has stopped serving, and refused if
  its id has been seen before. Otherwise the id is recorded as seen. Every id gets exactly one handler;
- `send id`: the handler sends {rid, digest} to the sink. `log_record` re-checks `serving` first;
- `commit id`: the sink appends the record and `fsync`s it. This needs the sink to be up (alive and not stopped);
- `ack id`: the proxy reads the sink's ack, which names this rid. The sink acks only after `fsync`, so the record is
  in the sink log. The ack must arrive before the proxy has given up on the record. It refreshes `last_ack`.
  An ack the sink wrote before it crashed can still be read: this step does NOT need the sink to be up;
- `timeout id`: `--ack-timeout` expires. The proxy closes the connection, so this record's ack is never read;
- `release id`: the handler replies 200. In the runtime this needs the ack (`log_record` returned True). Each id has
  one handler, so it replies at most once: the guard is `id ∉ released`;
- `tick`: time advances, and the watchdog thread stops serving when no ack (record or ping) has been read for more
  than `T`;
- `ping`: the heartbeat thread's ping succeeds. It needs the sink up. It refreshes `last_ack` and RESUMES serving;
- `sinkCrash` / `sinkRestart`: the controller's SIGSTOP or SIGKILL, and the new sink incarnation on the same file.
Flags (`CFlags`):
- `failOpen`: the runtime's NEGATIVE_CONTROL `--fail-open`. Release on send, without an ack;
- `promptReply`: a SCHEDULING PREMISE, not a runtime check. The handler replies within `T` ticks of reading its ack.
  The proxy does not re-check the watchdog between the ack and the reply. Prereg H1's `fresh` rule (receive − commit
  ≤ T) observed this premise in every repetition; it is TESTED there, not proved.
`real` = (failOpen := false, promptReply := true).

The abstraction α (into `Resume.St`):
- seen ↦ reqs; the record acks the proxy has read, in order ↦ acked = logged; clock ↦ clock;
- the clock of the last RECORD ack ↦ lastAck. Pings refresh the runtime's `last_ack` but log nothing, and the
  abstract model has no step that refreshes lastAck without logging;
- paused ↦ `lastAck + T < clock` (record staleness); released ↦ released; sinkUp ↦ true; halted ↦ false.

Results (deployed `real`; adversary class TRACE_ARBITRARY over the concrete events: any interleaving of arrivals,
sends, commits, acks, timeouts, releases, ticks, pings, crashes and restarts):
- `simulation`, `simulation_run`. arrive ↦ [request] when admitted; ack ↦ [logWrite] when read; release ↦ [release]
  when it happens; tick ↦ [tick]; every other event ↦ [].
- `concrete_safe`: `Resume.resume_safe` transfers to every reachable concrete state. Every 200 reply has its
  record among the acks read before the reply, the reply came within `T` of the last record ack, and no id is
  released twice.
- `concrete_durable`: with the concrete invariant, every released id is in the sink's `fsync`'d log.
- Progress (proved directly on the concrete machine):
  - `honest_path`: with the sink up and the proxy serving, a fresh request is released by
    [arrive, send, commit, ack, release];
  - `resume_then_serve`: the same after a `ping`, from a stopped (paused) proxy;
  - `honest_path_abstract`: α maps that honest path to exactly the Resume model's honest path
    [request, logWrite, release]. `Resume.resume_progress` is the [logWrite, release] part of it.
- Witnesses (`decide`):
  - `fail_open_breaks`: a proxy that releases on send (`failOpen`) releases a response whose record is in neither the
    ack list nor the sink log, and `RelOk` fails. `real` refuses the same trace. This is the runtime's H5 control;
  - `late_reply_breaks_timing`: without `promptReply`, a reply 3 ticks after its ack with T = 1 has its record durable,
    but the within-`T` clause fails. So the premise is needed for that clause and for nothing else;
  - `pause_resume_witness`: outage, then the watchdog stops serving and new arrivals are refused, then restart, ping,
    resume, and a new request is released.

Not covered:
- that the Python code implements this machine (TESTED by reconcile.py in run-1);
- digests: a record's digest equals the body's digest. Every ack in the model names its own record;
- latency;
- adversarial clients, or forged acks;
- the single release path (`single_release_path` is a premise).
Classical forward simulation; no novelty.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC18Liveness

namespace ControlStack.SC18Refinement

open ControlStack.SC18Liveness

/-! ## The concrete machine -/

structure CFlags where
  failOpen : Bool
  promptReply : Bool
deriving DecidableEq, Repr

/-- the runtime's deployed configuration, with the scheduling premise `promptReply` -/
def real : CFlags := ⟨false, true⟩

structure CSt where
  clock : ℕ
  serving : Bool
  sinkUp : Bool
  /-- the runtime's `last_ack`: refreshed by record acks and by pings -/
  lastAck : ℕ
  /-- the clock of the last record ack (ghost; the abstract lastAck) -/
  recAck : ℕ
  seen : List ℕ
  sent : List ℕ
  /-- the sink's `fsync`'d record log -/
  sinkLog : List ℕ
  /-- record acks read by the proxy, with the clock at which each was read -/
  ackd : List (ℕ × ℕ)
  failed : List ℕ
  released : List SC18.Rel
deriving DecidableEq, Repr

inductive COp where
  | arrive (id : ℕ)
  | send (id : ℕ)
  | commit (id : ℕ)
  | ack (id : ℕ)
  | timeout (id : ℕ)
  | release (id : ℕ)
  | tick
  | ping
  | sinkCrash
  | sinkRestart
deriving DecidableEq, Repr

def cinit : CSt := ⟨0, true, true, 0, 0, [], [], [], [], [], []⟩

/-- the proxy reads the ack of `id`: sent, committed (the sink acks only after `fsync`), not read yet, not given up -/
def ackOk (s : CSt) (id : ℕ) : Prop :=
  id ∈ s.sent ∧ id ∈ s.sinkLog ∧ id ∉ s.ackd.map Prod.fst ∧ id ∉ s.failed

instance (s : CSt) (id : ℕ) : Decidable (ackOk s id) := by unfold ackOk; infer_instance

/-- the handler of `id` replies 200: fail-open on send; otherwise after its ack (within `T` of it under
`promptReply`); at most once -/
def relOk (F : CFlags) (T : ℕ) (s : CSt) (id : ℕ) : Prop :=
  ((F.failOpen = true ∧ id ∈ s.sent) ∨
    (F.failOpen = false ∧ ∃ p ∈ s.ackd, p.1 = id ∧ (F.promptReply = true → s.clock ≤ p.2 + T))) ∧
  id ∉ s.released.map SC18.Rel.id

instance (F : CFlags) (T : ℕ) (s : CSt) (id : ℕ) : Decidable (relOk F T s id) := by unfold relOk; infer_instance

def stepC (F : CFlags) (T : ℕ) (s : CSt) : COp → CSt
  | .arrive id => if s.serving = true ∧ id ∉ s.seen then { s with seen := s.seen ++ [id] } else s
  | .send id => if s.serving = true ∧ id ∈ s.seen ∧ id ∉ s.sent then { s with sent := s.sent ++ [id] } else s
  | .commit id =>
    if s.sinkUp = true ∧ id ∈ s.sent ∧ id ∉ s.sinkLog then { s with sinkLog := s.sinkLog ++ [id] } else s
  | .ack id =>
    if ackOk s id then { s with ackd := s.ackd ++ [(id, s.clock)], lastAck := s.clock, recAck := s.clock } else s
  | .timeout id =>
    if id ∈ s.sent ∧ id ∉ s.ackd.map Prod.fst ∧ id ∉ s.failed then { s with failed := s.failed ++ [id] } else s
  | .release id =>
    if relOk F T s id then { s with released := s.released ++ [⟨id, s.ackd.length, s.clock, s.recAck⟩] } else s
  | .tick =>
    if s.serving = true ∧ s.lastAck + T < s.clock + 1 then { s with clock := s.clock + 1, serving := false }
    else { s with clock := s.clock + 1 }
  | .ping => if s.sinkUp = true then { s with lastAck := s.clock, serving := true } else s
  | .sinkCrash => { s with sinkUp := false }
  | .sinkRestart => { s with sinkUp := true }

def runC (F : CFlags) (T : ℕ) (s : CSt) (ops : List COp) : CSt := ops.foldl (stepC F T) s

theorem runC_cons (F : CFlags) (T : ℕ) (s : CSt) (o : COp) (ops : List COp) :
    runC F T s (o :: ops) = runC F T (stepC F T s o) ops := rfl

/-! ## Concrete invariant (deployed) -/

structure CInv (s : CSt) : Prop where
  sent_seen : ∀ x ∈ s.sent, x ∈ s.seen
  log_sent : ∀ x ∈ s.sinkLog, x ∈ s.sent
  ack_log : ∀ p ∈ s.ackd, p.1 ∈ s.sinkLog
  ack_time : ∀ p ∈ s.ackd, p.2 ≤ s.recAck
  rec_le : s.recAck ≤ s.clock
  failed_sent : ∀ x ∈ s.failed, x ∈ s.sent
  rel_ack : ∀ r ∈ s.released, r.id ∈ s.ackd.map Prod.fst

theorem cinv_init : CInv cinit := ⟨by simp [cinit], by simp [cinit], by simp [cinit], by simp [cinit], le_rfl,
  by simp [cinit], by simp [cinit]⟩

theorem CInv.ack_seen {s : CSt} (h : CInv s) {p : ℕ × ℕ} (hp : p ∈ s.ackd) : p.1 ∈ s.seen :=
  h.sent_seen _ (h.log_sent _ (h.ack_log p hp))

theorem cinv_step (T : ℕ) (s : CSt) (o : COp) (h : CInv s) : CInv (stepC real T s o) := by
  cases o with
  | arrive id =>
    simp only [stepC]; split_ifs
    · exact ⟨fun x hx => List.mem_append_left _ (h.sent_seen x hx), h.log_sent, h.ack_log, h.ack_time, h.rec_le,
        h.failed_sent, h.rel_ack⟩
    · exact h
  | send id =>
    simp only [stepC]; split_ifs with hg
    · refine ⟨fun x hx => ?_, fun x hx => List.mem_append_left _ (h.log_sent x hx), h.ack_log, h.ack_time,
        h.rec_le, fun x hx => List.mem_append_left _ (h.failed_sent x hx), h.rel_ack⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact h.sent_seen x hx
      · simp only [List.mem_singleton] at hx; subst hx; exact hg.2.1
    · exact h
  | commit id =>
    simp only [stepC]; split_ifs with hg
    · refine ⟨h.sent_seen, fun x hx => ?_, fun p hp => List.mem_append_left _ (h.ack_log p hp), h.ack_time,
        h.rec_le, h.failed_sent, h.rel_ack⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact h.log_sent x hx
      · simp only [List.mem_singleton] at hx; subst hx; exact hg.2.1
    · exact h
  | ack id =>
    simp only [stepC]; split_ifs with hg
    · obtain ⟨_, hl, _, _⟩ := hg
      refine ⟨h.sent_seen, h.log_sent, fun p hp => ?_, fun p hp => ?_, le_rfl, h.failed_sent, fun r hr => ?_⟩
      · rcases List.mem_append.1 hp with hp | hp
        · exact h.ack_log p hp
        · simp only [List.mem_singleton] at hp; subst hp; exact hl
      · rcases List.mem_append.1 hp with hp | hp
        · exact (h.ack_time p hp).trans h.rec_le
        · simp only [List.mem_singleton] at hp; subst hp; exact le_rfl
      · simp only [List.map_append]; exact List.mem_append_left _ (h.rel_ack r hr)
    · exact h
  | timeout id =>
    simp only [stepC]; split_ifs with hg
    · refine ⟨h.sent_seen, h.log_sent, h.ack_log, h.ack_time, h.rec_le, fun x hx => ?_, h.rel_ack⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact h.failed_sent x hx
      · simp only [List.mem_singleton] at hx; subst hx; exact hg.1
    · exact h
  | release id =>
    simp only [stepC]; split_ifs with hg
    · refine ⟨h.sent_seen, h.log_sent, h.ack_log, h.ack_time, h.rec_le, h.failed_sent, fun r hr => ?_⟩
      rcases List.mem_append.1 hr with hr | hr
      · exact h.rel_ack r hr
      · simp only [List.mem_singleton] at hr; subst hr
        rcases hg.1 with ⟨hf, _⟩ | ⟨_, p, hp, hpid, _⟩
        · exact absurd hf (by decide)
        · exact List.mem_map.2 ⟨p, hp, hpid⟩
    · exact h
  | tick =>
    simp only [stepC]; split_ifs
    · exact ⟨h.sent_seen, h.log_sent, h.ack_log, h.ack_time, h.rec_le.trans (Nat.le_succ _), h.failed_sent,
        h.rel_ack⟩
    · exact ⟨h.sent_seen, h.log_sent, h.ack_log, h.ack_time, h.rec_le.trans (Nat.le_succ _), h.failed_sent,
        h.rel_ack⟩
  | ping =>
    simp only [stepC]; split_ifs
    · exact ⟨h.sent_seen, h.log_sent, h.ack_log, h.ack_time, h.rec_le, h.failed_sent, h.rel_ack⟩
    · exact h
  | sinkCrash => exact ⟨h.sent_seen, h.log_sent, h.ack_log, h.ack_time, h.rec_le, h.failed_sent, h.rel_ack⟩
  | sinkRestart => exact ⟨h.sent_seen, h.log_sent, h.ack_log, h.ack_time, h.rec_le, h.failed_sent, h.rel_ack⟩

theorem cinv_run (T : ℕ) (s : CSt) (ops : List COp) (h : CInv s) : CInv (runC real T s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [runC_cons]; exact ih _ (cinv_step T s o h)

/-! ## Abstraction and forward simulation -/

/-- α into the resumable-watchdog model -/
def α (T : ℕ) (s : CSt) : Resume.St :=
  ⟨s.seen, s.ackd.map Prod.fst, s.ackd.map Prod.fst, true, s.clock, s.recAck, decide (s.recAck + T < s.clock),
    s.released, false⟩

/-- the model steps matching one concrete event -/
def opsOf (T : ℕ) (s : CSt) : COp → List Resume.Op
  | .arrive id => if s.serving = true ∧ id ∉ s.seen then [.request id] else []
  | .ack id => if ackOk s id then [.logWrite id] else []
  | .release id => if relOk real T s id then [.release id] else []
  | .tick => [.tick]
  | _ => []

theorem simulation (admins : List ℕ) (T : ℕ) (s : CSt) (o : COp) (h : CInv s) :
    α T (stepC real T s o) = Resume.run admins T (α T s) (opsOf T s o) := by
  cases o with
  | arrive id =>
    simp only [stepC, opsOf]
    by_cases hg : s.serving = true ∧ id ∉ s.seen
    · rw [ite_eq_left hg, ite_eq_left hg]
      simp [α, Resume.run, Resume.step, hg.2]
    · rw [ite_eq_right hg, ite_eq_right hg]; rfl
  | send id => simp only [stepC, opsOf]; split_ifs <;> rfl
  | commit id => simp only [stepC, opsOf]; split_ifs <;> rfl
  | ack id =>
    simp only [stepC, opsOf]
    by_cases hg : ackOk s id
    · rw [ite_eq_left hg, ite_eq_left hg]
      have hseen : id ∈ s.seen := h.sent_seen _ hg.1
      simp [α, Resume.run, Resume.step, hseen]
    · rw [ite_eq_right hg, ite_eq_right hg]; rfl
  | timeout id => simp only [stepC, opsOf]; split_ifs <;> rfl
  | release id =>
    simp only [stepC, opsOf]
    by_cases hg : relOk real T s id
    · rw [ite_eq_left hg, ite_eq_left hg]
      obtain ⟨hor, hn⟩ := hg
      rcases hor with ⟨hf, _⟩ | ⟨_, p, hp, hpid, hpt⟩
      · exact absurd hf (by decide)
      have ht := hpt rfl
      have hle := h.ack_time p hp
      have hseen : id ∈ s.seen := hpid ▸ h.ack_seen hp
      have hack : id ∈ s.ackd.map Prod.fst := List.mem_map.2 ⟨p, hp, hpid⟩
      have hnp : ¬ s.recAck + T < s.clock := by omega
      simp [α, Resume.run, Resume.step, hseen, hack, hn, hnp]
    · rw [ite_eq_right hg, ite_eq_right hg]; rfl
  | tick =>
    simp only [stepC, opsOf, Resume.run, List.foldl_cons, List.foldl_nil]
    by_cases hw : s.recAck + T < s.clock + 1
    · have hs : Resume.step admins T (α T s) .tick =
          { α T s with clock := s.clock + 1, paused := true } := by
        simp [Resume.step, α, hw]
      rw [hs]
      split_ifs <;> simp [α, hw]
    · have hs : Resume.step admins T (α T s) .tick = { α T s with clock := s.clock + 1 } := by
        simp [Resume.step, α, hw]
      have hw' : ¬ s.recAck + T < s.clock := by omega
      rw [hs]
      split_ifs <;> simp [α, hw, hw']
  | ping => simp only [stepC, opsOf]; split_ifs <;> rfl
  | sinkCrash => rfl
  | sinkRestart => rfl

/-- the model trace of a concrete trace -/
def absTrace (T : ℕ) : CSt → List COp → List Resume.Op
  | _, [] => []
  | s, o :: ops => opsOf T s o ++ absTrace T (stepC real T s o) ops

theorem simulation_run (admins : List ℕ) (T : ℕ) (s : CSt) (ops : List COp) (h : CInv s) :
    α T (runC real T s ops) = Resume.run admins T (α T s) (absTrace T s ops) := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    change α T (runC real T (stepC real T s o) ops) = _
    rw [ih _ (cinv_step T s o h), simulation admins T s o h]
    simp [absTrace, Resume.run, List.foldl_append]

theorem α_cinit (T : ℕ) : α T cinit = Resume.init := by
  simp [α, cinit, Resume.init]

/-! ## Transfer -/

/-- **SC-18 safety for the concrete proxy** (`Resume.resume_safe` transferred). For every concrete trace, every 200
reply has its record among the acks read before the reply (`RelOk`), the reply came within `T` of the last record
ack, and no request id is released twice. -/
theorem concrete_safe (T : ℕ) (ops : List COp) :
    (∀ r ∈ (runC real T cinit ops).released, Resume.RelOk T (α T (runC real T cinit ops)) r) ∧
      ((runC real T cinit ops).released.map SC18.Rel.id).Nodup := by
  have hs := simulation_run [] T cinit ops cinv_init
  have key := Resume.resume_safe [] T (absTrace T cinit ops)
  rw [← α_cinit T, ← hs] at key
  exact key

/-- **Durable before reply.** Every released id was acked among the first `r.llen` record acks (before its
reply), each such ack follows the sink's `fsync` of that record, and the reply came within `T` of the last record
ack. -/
theorem concrete_durable (T : ℕ) (ops : List COp) :
    ∀ r ∈ (runC real T cinit ops).released,
      r.id ∈ ((runC real T cinit ops).ackd.map Prod.fst).take r.llen ∧ r.id ∈ (runC real T cinit ops).sinkLog ∧
        r.clock ≤ r.lastAck + T := by
  intro r hr
  have hok := (concrete_safe T ops).1 r hr
  have hinv := cinv_run T cinit ops cinv_init
  refine ⟨hok.2.1, ?_, hok.2.2⟩
  obtain ⟨p, hp, hpid⟩ := List.mem_map.1 (hinv.rel_ack r hr)
  exact hpid ▸ hinv.ack_log p hp

/-! ## Progress -/

theorem fresh_facts {s : CSt} (h : CInv s) {i : ℕ} (hi : i ∉ s.seen) :
    i ∉ s.sent ∧ i ∉ s.sinkLog ∧ i ∉ s.ackd.map Prod.fst ∧ i ∉ s.failed ∧ i ∉ s.released.map SC18.Rel.id := by
  have h1 : i ∉ s.sent := fun hs => hi (h.sent_seen _ hs)
  have h2 : i ∉ s.sinkLog := fun hl => h1 (h.log_sent _ hl)
  have h3 : i ∉ s.ackd.map Prod.fst := fun ha => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha; exact h2 (h.ack_log p hp)
  refine ⟨h1, h2, h3, fun hf => h1 (h.failed_sent _ hf), fun hrel => ?_⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hrel
  exact h3 (h.rel_ack r hr)

/-- **Honest path.** With the sink up and the proxy serving, a fresh request is released by
[arrive, send, commit, ack, release]. -/
theorem honest_path (T : ℕ) (s : CSt) (i : ℕ) (h : CInv s) (hs : s.serving = true) (hu : s.sinkUp = true)
    (hi : i ∉ s.seen) :
    i ∈ (runC real T s [.arrive i, .send i, .commit i, .ack i, .release i]).released.map SC18.Rel.id := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := fresh_facts h hi
  simp [runC, stepC, ackOk, relOk, real, hs, hu, hi, h1, h2, h3, h4, h5]

/-- **Resume, then serve.** From a stopped proxy (any serving state) with the sink back up, a successful ping
resumes serving, and a fresh request is then released. -/
theorem resume_then_serve (T : ℕ) (s : CSt) (i : ℕ) (h : CInv s) (hu : s.sinkUp = true) (hi : i ∉ s.seen) :
    i ∈ (runC real T s [.ping, .arrive i, .send i, .commit i, .ack i, .release i]).released.map SC18.Rel.id := by
  rw [runC_cons]
  have hp : stepC real T s .ping = { s with lastAck := s.clock, serving := true } := by simp [stepC, hu]
  rw [hp]
  exact honest_path T _ i ⟨h.sent_seen, h.log_sent, h.ack_log, h.ack_time, h.rec_le, h.failed_sent, h.rel_ack⟩ rfl hu hi

/-- **The honest path is the model's honest path.** α maps [arrive, send, commit, ack, release] to exactly
[request, logWrite, release]; `Resume.resume_progress` is its [logWrite, release] part. -/
theorem honest_path_abstract (T : ℕ) (s : CSt) (i : ℕ) (h : CInv s) (hs : s.serving = true)
    (hu : s.sinkUp = true) (hi : i ∉ s.seen) :
    absTrace T s [.arrive i, .send i, .commit i, .ack i, .release i] = [.request i, .logWrite i, .release i] := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := fresh_facts h hi
  simp [absTrace, opsOf, stepC, ackOk, relOk, real, hs, hu, hi, h1, h2, h3, h4, h5]

/-! ## Witnesses -/

/-- **Fail-open breaks the transferred property** (runtime H5 control). A proxy that releases on send, with the
sink stopped before the commit, releases request 0. Its record is in neither the ack list nor the sink log, and
`RelOk` fails. The deployed proxy refuses the same trace. -/
theorem fail_open_breaks :
    let t := runC ⟨true, true⟩ 1 cinit [.arrive 0, .send 0, .sinkCrash, .commit 0, .release 0]
    t.released.map SC18.Rel.id = [0] ∧ 0 ∉ t.sinkLog ∧ ¬ (∀ r ∈ t.released, Resume.RelOk 1 (α 1 t) r) ∧
      (runC real 1 cinit [.arrive 0, .send 0, .sinkCrash, .commit 0, .release 0]).released = [] := by
  refine ⟨by decide, by decide, ?_, by decide⟩
  intro hall
  have := hall _ (by decide : (⟨0, 0, 0, 0⟩ : SC18.Rel) ∈ _)
  exact absurd this.2.1 (by decide)

/-- **Why `promptReply` is a premise.** Without it, T = 1, a reply 3 ticks after its ack: the record is durable, but
the within-`T` clause fails. With the premise, the late reply does not happen. -/
theorem late_reply_breaks_timing :
    let ops : List COp := [.arrive 0, .send 0, .commit 0, .ack 0, .tick, .tick, .tick, .release 0]
    let t := runC ⟨false, false⟩ 1 cinit ops
    t.released = [⟨0, 1, 3, 0⟩] ∧ 0 ∈ t.sinkLog ∧ ¬ (3 ≤ 0 + 1) ∧ (runC real 1 cinit ops).released = [] := by
  decide

/-- **Pause, then resume** (runtime H2 and H3). T = 1: after a release, the sink crashes. The watchdog stops serving,
and a new arrival is refused. The sink restarts, a ping resumes serving, and the new request is released. -/
theorem pause_resume_witness :
    let pre : List COp := [.arrive 0, .send 0, .commit 0, .ack 0, .release 0, .sinkCrash, .tick, .tick, .tick,
      .arrive 1]
    (runC real 1 cinit pre).serving = false ∧ 1 ∉ (runC real 1 cinit pre).seen ∧
      (runC real 1 cinit (pre ++ [.sinkRestart, .ping, .arrive 1, .send 1, .commit 1, .ack 1, .release 1])).released.map
        SC18.Rel.id = [0, 1] := by
  decide

end ControlStack.SC18Refinement

#print axioms ControlStack.SC18Refinement.simulation
#print axioms ControlStack.SC18Refinement.simulation_run
#print axioms ControlStack.SC18Refinement.concrete_safe
#print axioms ControlStack.SC18Refinement.concrete_durable
#print axioms ControlStack.SC18Refinement.honest_path
#print axioms ControlStack.SC18Refinement.resume_then_serve
#print axioms ControlStack.SC18Refinement.honest_path_abstract
#print axioms ControlStack.SC18Refinement.fail_open_breaks
#print axioms ControlStack.SC18Refinement.late_reply_breaks_timing
#print axioms ControlStack.SC18Refinement.pause_resume_witness
