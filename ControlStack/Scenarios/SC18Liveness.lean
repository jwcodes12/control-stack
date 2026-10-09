/-
SC-18 liveness: the usefulness counterpart of `SC18Logging.sc18_safe`, plus a model of the runtime's RESUME
behaviour, which the original model does not have.

Results on the original model (`ControlStack.SC18`, deployed `full`; adversary TRACE_ARBITRARY under `legal`):
- `honest_release`: from an invariant state, not halted, with the trusted sink up, an honest request
  [request, logWrite, release] is released, its record in the trusted log at release time (by `sc18_safe`).
- `progress_interleaved`: arbitrary legal operations interleaved around the three honest steps. At the end the request
  is released, or the proxy is halted, or the sink was down when the honest log write ran. Nothing else blocks it.
- `silent_ticks_halt`: the availability price. If the sink acknowledges nothing for more than `T` ticks, the
  watchdog halts serving, and `SC18.halt_freezes` then forbids every release (fail-closed).
- In this model the watchdog halt is ABSORBING: there is no recovery.

Model/runtime mismatch, recorded: the runtime proxy RESUMES serving when the sink answers again (prereg H3, measured
resume 9.2–32 ms after the restarted sink was ready). The original model cannot express this. The `Resume` section
therefore adds a variant with a non-absorbing watchdog PAUSE: the watchdog pauses serving after `T` silent ticks, and a
successful log write (the sink acknowledging again) clears the pause.
- `Resume.resume_safe`: the same safety property as `sc18_safe`: every release's record was in the trusted log at
  release time, the release came within `T` ticks of the last acknowledgement, and no request is released twice.
  A paused proxy releases nothing.
- `Resume.resume_progress`: after the sink is restored, an honest [logWrite, release] is released, even if the proxy
  was paused.
- `Resume.pause_then_resume`: outage, then pause (nothing released), then restore, then release (witness).

Runtime counterparts (prereg/SC18-LOG-PROXY.md, evidence scenarios/SC-18/evidence/run-1):
- H1 (released ⇒ committed before receive, within T, no duplicate): `SC18.sc18_safe` and `Resume.resume_safe`;
  usefulness side `honest_release`;
- H2 (outage ⇒ fail closed within T + TAU_W): `silent_ticks_halt` with `SC18.halt_freezes`, and the pause in
  `Resume`;
- H3 (recovery after a sink crash): `Resume.resume_progress` and `Resume.pause_then_resume`, in the VARIANT model
  only;
- H4 (usefulness: 100/100 served, latency p50/p99): `honest_release` and `progress_interleaved` (every honest request
  is eventually served). Latency is NOT modelled: the model has no wall-clock durations below a tick;
- H5 (negative control, fail-open): `SC18.fail_open_outage_breaks`.
No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC18Logging

namespace ControlStack.SC18Liveness

open ControlStack.SC18

variable (admins : List ℕ) (trusted T : ℕ)

/-! ## Monotonicity -/

structure Mono (s t : St) : Prop where
  reqs : s.reqs ⊆ t.reqs
  acked : s.acked ⊆ t.acked
  rel : s.released.map Rel.id ⊆ t.released.map Rel.id
  halt : s.halted = true → t.halted = true

theorem Mono.refl (s : St) : Mono s s := ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun h => h⟩

theorem Mono.trans {s t u : St} (h1 : Mono s t) (h2 : Mono t u) : Mono s u :=
  ⟨fun _ h => h2.reqs (h1.reqs h), fun _ h => h2.acked (h1.acked h), fun _ h => h2.rel (h1.rel h),
    fun h => h2.halt (h1.halt h)⟩

theorem step_mono (s : St) (o : Op) : Mono s (step admins trusted T full s o) := by
  cases o with
  | request id =>
    simp only [step]
    split_ifs
    all_goals first | exact Mono.refl s | exact ⟨fun _ h => List.mem_append_left _ h, fun _ h => h, fun _ h => h, fun h => h⟩
  | logWrite id =>
    simp only [step]
    split_ifs
    all_goals first | exact Mono.refl s | exact ⟨fun _ h => h, fun _ h => List.mem_append_left _ h, fun _ h => h, fun h => h⟩
  | release id =>
    simp only [step]
    split_ifs
    all_goals first | exact Mono.refl s |
      exact ⟨fun _ h => h, fun _ h => h, fun _ h => by simp only [List.map_append]; exact List.mem_append_left _ h, fun h => h⟩
  | tick =>
    simp only [step]
    split_ifs
    all_goals first | exact Mono.refl s | exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ => rfl⟩ |
      exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun h => h⟩
  | halt c =>
    simp only [step]
    split_ifs
    · exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ => rfl⟩
    · exact Mono.refl s
  | _ =>
    simp only [step]
    try split_ifs
    all_goals first | exact Mono.refl s | exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun h => h⟩

theorem run_mono (s : St) (ops : List Op) : Mono s (run admins trusted T full s ops) := by
  induction ops generalizing s with
  | nil => exact Mono.refl s
  | cons o ops ih => rw [run_cons]; exact (step_mono admins trusted T s o).trans (ih _)

theorem not_halted_of {s t : St} (h : Mono s t) (ht : t.halted = false) : s.halted = false := by
  cases hs : s.halted
  · rfl
  · have := h.halt hs; rw [ht] at this; exact absurd this (by decide)

/-! ## The honest steps -/

theorem request_fields (s : St) (i : ℕ) :
    (step admins trusted T full s (.request i)).halted = s.halted ∧
      (step admins trusted T full s (.request i)).sinkUp = s.sinkUp := by
  simp only [step]; split_ifs <;> exact ⟨rfl, rfl⟩

theorem logWrite_halted (s : St) (i : ℕ) : (step admins trusted T full s (.logWrite i)).halted = s.halted := by
  simp only [step]; split_ifs <;> rfl

theorem request_adds (s : St) (i : ℕ) (hh : s.halted = false) : i ∈ (step admins trusted T full s (.request i)).reqs := by
  by_cases h : i ∈ s.reqs
  · exact (step_mono admins trusted T s _).reqs h
  · simp [step, hh, h]

theorem logWrite_acks (s : St) (i : ℕ) (hh : s.halted = false) (hr : i ∈ s.reqs) (hu : s.sinkUp = true) :
    i ∈ (step admins trusted T full s (.logWrite i)).acked := by
  simp [step, hh, hr, hu]

theorem release_releases (s : St) (i : ℕ) (hh : s.halted = false) (hr : i ∈ s.reqs) (ha : i ∈ s.acked) :
    i ∈ (step admins trusted T full s (.release i)).released.map Rel.id := by
  by_cases hrel : i ∈ s.released.map Rel.id
  · exact (step_mono admins trusted T s _).rel hrel
  · simp only [step, hh, Bool.false_eq_true, false_and, ite_false]
    rw [ite_eq_left ⟨hr, hrel, fun _ => Or.inl ha⟩]
    simp

/-- **Honest release.** From a state that is not halted, with the sink up, the honest request is released. -/
theorem honest_release (s : St) (i : ℕ) (hh : s.halted = false) (hu : s.sinkUp = true) :
    i ∈ (run admins trusted T full s [.request i, .logWrite i, .release i]).released.map Rel.id := by
  set s1 := step admins trusted T full s (.request i)
  have h1 := request_adds admins trusted T s i hh
  obtain ⟨hh1, hu1⟩ := request_fields admins trusted T s i
  rw [hh] at hh1; rw [hu] at hu1
  set s2 := step admins trusted T full s1 (.logWrite i)
  have h2 := logWrite_acks admins trusted T s1 i hh1 h1 hu1
  have hh2 : s2.halted = false := by rw [logWrite_halted]; exact hh1
  exact release_releases admins trusted T s2 i hh2 ((step_mono admins trusted T s1 _).reqs h1) h2

/-- **Progress despite any interleaving.** Around the honest [request, logWrite, release], arbitrary operations
`a0`–`a3`. At the end the request is released, or the proxy is halted, or the sink was down when the honest log write
ran. -/
theorem progress_interleaved (s : St) (i : ℕ) (a0 a1 a2 a3 : List Op) :
    let t := run admins trusted T full s (a0 ++ .request i :: a1 ++ .logWrite i :: a2 ++ .release i :: a3)
    i ∈ t.released.map Rel.id ∨ t.halted = true ∨
      (run admins trusted T full (step admins trusted T full (run admins trusted T full s a0) (.request i)) a1).sinkUp
        = false := by
  intro t
  set s0 := run admins trusted T full s a0
  set s1 := step admins trusted T full s0 (.request i)
  set s1' := run admins trusted T full s1 a1
  set s2 := step admins trusted T full s1' (.logWrite i)
  set s2' := run admins trusted T full s2 a2
  set s3 := step admins trusted T full s2' (.release i)
  have ht : t = run admins trusted T full s3 a3 := by
    simp only [t, run, List.foldl_append, List.foldl_cons]; rfl
  rw [ht]
  have m1 := step_mono admins trusted T s0 (.request i)
  have m1' := run_mono admins trusted T s1 a1
  have m2 := step_mono admins trusted T s1' (.logWrite i)
  have m2' := run_mono admins trusted T s2 a2
  have m3 := step_mono admins trusted T s2' (.release i)
  have m3' := run_mono admins trusted T s3 a3
  cases hT : (run admins trusted T full s3 a3).halted
  · cases hU : s1'.sinkUp
    · right; right; rfl
    · left
      have hh3 := not_halted_of m3' hT
      have hh2' := not_halted_of m3 hh3
      have hh2 := not_halted_of m2' hh2'
      have hh1' := not_halted_of m2 hh2
      have hh1 := not_halted_of m1' hh1'
      have hh0 := not_halted_of m1 hh1
      have hr1 := request_adds admins trusted T s0 i hh0
      have hr1' := m1'.reqs hr1
      have ha2 := logWrite_acks admins trusted T s1' i hh1' hr1' hU
      exact m3'.rel (release_releases admins trusted T s2' i hh2' (m2'.reqs (m2.reqs hr1')) (m2'.acked ha2))
  · right; left; rfl

/-! ## The availability price: silence halts serving -/

/-- **Silence beyond T halts serving.** From a state satisfying the watchdog invariant (not halted ⇒ within T of the
last acknowledgement), n ticks without any acknowledgement, with lastAck + T < clock + n, end halted. By
`SC18.halt_freezes`, nothing is released afterwards. -/
theorem ticks_keep_halted (m : ℕ) (t : St) (ht : t.halted = true) :
    (run admins trusted T full t (List.replicate m .tick)).halted = true := by
  induction m generalizing t with
  | zero => simpa [run] using ht
  | succ m ihm =>
    rw [List.replicate_succ, run_cons]
    apply ihm; simp [step, ht, full]

theorem silent_ticks_halt (s : St) (n : ℕ) (hinv : s.halted = false → s.clock ≤ s.lastAck + T)
    (hn : s.lastAck + T < s.clock + n) :
    (run admins trusted T full s (List.replicate n .tick)).halted = true := by
  induction n generalizing s with
  | zero =>
    cases hh : s.halted
    · have := hinv hh; omega
    · simpa [run] using hh
  | succ n ih =>
    cases hh : s.halted
    · rw [List.replicate_succ, run_cons]
      simp only [step, hh, Bool.false_eq_true, false_and, ite_false, show full.watchdog = true from rfl, true_and]
      split_ifs with hw
      · exact ticks_keep_halted admins trusted T n _ rfl
      · exact ih _ (fun _ => by simp only; omega) (by simp only; omega)
    · rw [List.replicate_succ, run_cons]
      exact ticks_keep_halted admins trusted T n _ (by simp [step, hh, full])

/-- the outage witness in numbers: T = 2, three silent ticks after the last acknowledgement halt the proxy, and a
later honest request is not released -/
theorem outage_fail_closed :
    (run [9] 0 2 full (init 0) [.request 0, .logWrite 0, .sinkDown, .tick, .tick, .tick]).halted = true ∧
    (run [9] 0 2 full (init 0) [.request 0, .logWrite 0, .sinkDown, .tick, .tick, .tick, .sinkRestore, .request 1,
      .logWrite 1, .release 1]).released = [] := by
  decide

/-! ## Resume: a variant with a non-absorbing watchdog pause (the runtime's H3 behaviour) -/

namespace Resume

structure St where
  reqs : List ℕ
  acked : List ℕ
  logged : List ℕ
  sinkUp : Bool
  clock : ℕ
  lastAck : ℕ
  paused : Bool
  released : List SC18.Rel
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | request (id : ℕ)
  | logWrite (id : ℕ)
  | release (id : ℕ)
  | sinkDown
  | sinkRestore
  | tick
  | halt (caller : ℕ)
deriving DecidableEq, Repr

def init : St := ⟨[], [], [], true, 0, 0, false, [], false⟩

/-- the trusted sink is fixed here (configuration protection is `SC18.config_untampered`) -/
def step (admins : List ℕ) (T : ℕ) (s : St) : Op → St
  | .request id => if s.halted then s else if id ∉ s.reqs then { s with reqs := s.reqs ++ [id] } else s
  | .logWrite id =>
    if s.halted then s
    else if id ∈ s.reqs ∧ s.sinkUp then
      { s with acked := s.acked ++ [id], logged := s.logged ++ [id], lastAck := s.clock, paused := false }
    else s
  | .release id =>
    if s.halted ∨ s.paused then s
    else if id ∈ s.reqs ∧ id ∉ s.released.map SC18.Rel.id ∧ id ∈ s.acked then
      { s with released := s.released ++ [⟨id, s.logged.length, s.clock, s.lastAck⟩] }
    else s
  | .sinkDown => { s with sinkUp := false }
  | .sinkRestore => { s with sinkUp := true }
  | .tick =>
    if s.halted then s
    else if s.lastAck + T < s.clock + 1 then { s with clock := s.clock + 1, paused := true }
    else { s with clock := s.clock + 1 }
  | .halt c => if c ∈ admins then { s with halted := true } else s

def run (admins : List ℕ) (T : ℕ) (s : St) (ops : List Op) : St := ops.foldl (step admins T) s

theorem run_cons (admins : List ℕ) (T : ℕ) (s : St) (o : Op) (ops : List Op) :
    run admins T s (o :: ops) = run admins T (step admins T s o) ops := rfl

def RelOk (T : ℕ) (s : St) (r : SC18.Rel) : Prop :=
  r.llen ≤ s.logged.length ∧ r.id ∈ s.logged.take r.llen ∧ r.clock ≤ r.lastAck + T

structure Inv (T : ℕ) (s : St) : Prop where
  ack_ok : ∀ x ∈ s.acked, x ∈ s.logged
  rel_ok : ∀ r ∈ s.released, RelOk T s r
  nodup : (s.released.map SC18.Rel.id).Nodup
  clk : s.paused = false → s.clock ≤ s.lastAck + T

theorem inv_init (T : ℕ) : Inv T init := ⟨by simp [init], by simp [init], by simp [init], fun _ => by simp [init]⟩

theorem RelOk.mono {T : ℕ} {s t : St} (hp : s.logged <+: t.logged) {r : SC18.Rel} (h : RelOk T s r) : RelOk T t r := by
  obtain ⟨u, hu⟩ := hp
  refine ⟨h.1.trans (hu ▸ by simp), ?_, h.2.2⟩
  rw [← hu, List.take_append_of_le_length h.1]
  exact h.2.1

theorem step_inv (admins : List ℕ) (T : ℕ) (s : St) (o : Op) (h : Inv T s) : Inv T (step admins T s o) := by
  cases o with
  | request id =>
    simp only [step]; split_ifs
    all_goals first | exact h | exact ⟨h.ack_ok, h.rel_ok, h.nodup, h.clk⟩
  | logWrite id =>
    simp only [step]; split_ifs
    · exact h
    · refine ⟨fun x hx => ?_, fun r hr => RelOk.mono (List.prefix_append _ _) (h.rel_ok r hr), h.nodup,
        fun _ => Nat.le_add_right _ _⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact List.mem_append_left _ (h.ack_ok x hx)
      · simp at hx; subst hx; simp
    · exact h
  | release id =>
    simp only [step]; split_ifs with h1 h2
    · exact h
    · obtain ⟨_, hn, ha⟩ := h2
      have hp : s.paused = false := by cases hp : s.paused <;> simp_all
      refine ⟨h.ack_ok, fun r hr => ?_, ?_, h.clk⟩
      · rcases List.mem_append.1 hr with hr | hr
        · exact h.rel_ok r hr
        · simp at hr; subst hr
          exact ⟨le_rfl, by rw [List.take_length]; exact h.ack_ok id ha, h.clk hp⟩
      · simp only [List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.2 ⟨h.nodup, List.nodup_singleton _, fun a ha' b hb => ?_⟩
        simp only [List.mem_singleton] at hb
        subst hb; rintro rfl; exact hn ha'
    · exact h
  | sinkDown => exact ⟨h.ack_ok, h.rel_ok, h.nodup, h.clk⟩
  | sinkRestore => exact ⟨h.ack_ok, h.rel_ok, h.nodup, h.clk⟩
  | tick =>
    simp only [step]; split_ifs with h1 h2
    · exact h
    · exact ⟨h.ack_ok, h.rel_ok, h.nodup, fun hf => by simp at hf⟩
    · refine ⟨h.ack_ok, h.rel_ok, h.nodup, fun hp => ?_⟩
      simp only at hp ⊢
      omega
  | halt c =>
    simp only [step]; split_ifs
    all_goals first | exact h | exact ⟨h.ack_ok, h.rel_ok, h.nodup, h.clk⟩

theorem run_inv (admins : List ℕ) (T : ℕ) (s : St) (ops : List Op) (h : Inv T s) : Inv T (run admins T s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv admins T s o h)

/-- **Safety with a resumable watchdog.** Every release's record was in the trusted log at release time, the release
came within `T` ticks of the last acknowledgement, and no request is released twice. -/
theorem resume_safe (admins : List ℕ) (T : ℕ) (ops : List Op) :
    (∀ r ∈ (run admins T init ops).released, RelOk T (run admins T init ops) r) ∧
      ((run admins T init ops).released.map SC18.Rel.id).Nodup :=
  let h := run_inv admins T init ops (inv_init T)
  ⟨h.rel_ok, h.nodup⟩

/-- a paused proxy releases nothing -/
theorem paused_no_release (admins : List ℕ) (T : ℕ) (s : St) (id : ℕ) (hp : s.paused = true) :
    step admins T s (.release id) = s := by
  simp [step, hp]

/-- **Progress after resume.** Once the sink is up again, an honest log write clears the pause and the request is
released (not halted, request present). -/
theorem resume_progress (admins : List ℕ) (T : ℕ) (s : St) (i : ℕ) (hh : s.halted = false) (hu : s.sinkUp = true)
    (hr : i ∈ s.reqs) : i ∈ (run admins T s [.logWrite i, .release i]).released.map SC18.Rel.id := by
  simp only [run, List.foldl_cons, List.foldl_nil]
  have h1 : step admins T s (.logWrite i) =
      { s with acked := s.acked ++ [i], logged := s.logged ++ [i], lastAck := s.clock, paused := false } := by
    simp [step, hh, hr, hu]
  rw [h1]
  by_cases hrel : i ∈ s.released.map SC18.Rel.id
  · simp only [step]; split_ifs <;> simp [hrel]
  · simp [step, hh, hr, hrel]

/-- **Witness**: outage, pause (nothing released), restore, resume (released). T = 2. -/
theorem pause_then_resume :
    (run [9] 2 init [.request 0, .logWrite 0, .sinkDown, .tick, .tick, .tick, .release 0]).released = [] ∧
    (run [9] 2 init [.request 0, .logWrite 0, .sinkDown, .tick, .tick, .tick, .release 0]).paused = true ∧
    (run [9] 2 init [.request 0, .logWrite 0, .sinkDown, .tick, .tick, .tick, .release 0, .sinkRestore, .logWrite 0,
      .release 0]).released.map SC18.Rel.id = [0] := by
  decide

end Resume

end ControlStack.SC18Liveness

#print axioms ControlStack.SC18Liveness.honest_release
#print axioms ControlStack.SC18Liveness.progress_interleaved
#print axioms ControlStack.SC18Liveness.silent_ticks_halt
#print axioms ControlStack.SC18Liveness.outage_fail_closed
#print axioms ControlStack.SC18Liveness.Resume.resume_safe
#print axioms ControlStack.SC18Liveness.Resume.paused_no_release
#print axioms ControlStack.SC18Liveness.Resume.resume_progress
#print axioms ControlStack.SC18Liveness.Resume.pause_then_resume
