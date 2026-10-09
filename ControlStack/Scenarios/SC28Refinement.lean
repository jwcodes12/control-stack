/-
SC-28 refinement: the runtime's event structure (scenarios/SC-28/harness/meter.py, run_sc28.py;
prereg/SC28-CGROUP-METER.md) as a concrete machine, with a forward simulation into `ControlStack.SC28`
(criterion 3, as for SC-26, SC-25, SC-16 and SC-18).

Concrete machine (`CSt`, `COp`, `stepC`). There is one run cgroup with the global cap `G`, and one child cgroup per
lease. The meter is the trusted root controller, identity 0.
- `createLease lid lim`: the controller creates lease cgroup `lid` with limit `lim`. It writes the limit and reads it
  back before any process can enter. It refuses after HALT and refuses an existing lease.
- `launch pid lid`: launch with PLACEMENT. The forked child writes its own pid into the lease's `cgroup.procs`
  before exec. The controller refuses after HALT, for an unknown lease, and for a REVOKED lease. The controller's
  refusal is its own state check, not the kernel's (prereg §1).
- `fork p ch`: a live process forks. KERNEL PREMISE (`fork_inherits`): the child is in its parent's cgroup. A
  daemon that starts its own session (`start_new_session=True`, prereg H1) is still a fork.
- `consume pid x` (x ≥ 1): a live process consumes x units. The kernel charges them to its cgroup and to every
  ancestor. KERNEL PREMISE (`kernel_enforcement`): consumption happens only within the lease limit and the run's
  cap, as hierarchical `cpu.max`/`pids.max` enforcement does. The counters (`acct`, a ghost log whose sums are the
  per-cgroup usage counters) only grow. A process outside the run cgroup consumes without limit or accounting
  (`outside`);
- `read lid`: the meter reads the kernel's counters. This changes nothing;
- `revoke lid`: mark the lease revoked (refuse first), then `cgroup.kill`: every process in the lease dies;
- `halt`: mark the run halted (refuse first), then `cgroup.freeze` and `cgroup.kill` on the run. Every placed process
  dies;
- `launchUnplaced pid`: CONTROL ONLY (prereg H5). The same credential drop but no placement: the process is outside
  the run cgroup.

α (into `SC28.St`; admins = [0]):
- lease cgroups ↦ leases (limit ↦ budget);
- placed processes, newest first ↦ assign;
- revoked ↦ revoked; halted ↦ halted;
- the kernel accounting log ↦ usage, and ↦ ledger as (lease, units). The meter's counters ARE the kernel's
  counters.

Results (adversary class TRACE_ARBITRARY over the concrete events, including the control event):
- `simulation`, `simulation_run`. Each concrete event maps to 0 or 1 model steps:
  - createLease ↦ [issue], launch ↦ [assignTo], placed fork ↦ [fork], placed consume ↦ [work pid x x],
    revoke ↦ [revoke], halt ↦ [halt];
  - unplaced launch, unplaced fork or consume, read, and every refused event ↦ [].
- `concrete_safe` (`SC28.sc28_safe` transferred, read on the kernel counters as `concrete_counters_safe`):
  - the run counter is ≤ G, and every lease counter is ≤ its limit;
  - there are at most G accounted consumption events.
- `concrete_revoked_stops` (`SC28.revoked_lease_stops` transferred): after `revoke lid`, the counter of `lid` never
  grows again.
- `concrete_halt_freezes` (`SC28.halt_freezes` transferred): after HALT the accounting log never changes.
- `exclusive_placement_safe`: without `launchUnplaced`, nothing is consumed outside the run cgroup. So REAL total
  consumption = run counter ≤ G.
- `unplaced_invisible` (the runtime H5 control):
  - an unplaced process and its fork consume 100 units with G = 10. α's ledger and usage stay empty, so the
    transferred property is silent about them;
  - the same tree launched with placement is throttled at the limit.
  This is the EXCLUSIVE-PLACEMENT premise: every consuming process descends from a controller launch with
  placement.

Premises named here:
- `kernel_enforcement`: hierarchical cgroup limits and monotone counters;
- `fork_inherits`;
- exclusive placement;
- the controller's own refusals;
- counter durability: the run is a single controller lifetime. Durability across restarts is the anti-rollback
  premise, measured in experiments/anti-rollback/evidence/run-1;
- a TRUSTED root controller.

Not covered:
- that meter.py implements this machine (TESTED: prereg H1–H5, run-1);
- resource kinds: one scalar unit stands for CPU time. Prereg H2 measured CPU and pids caps separately; memory is
  not tested;
- adversarial workloads racing the kill. Kill and freeze are atomic steps here; the runtime measured termination
  within 1.0 s.

Classical forward simulation; no novelty.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC28Budget

namespace ControlStack.SC28Refinement

/-! ## The concrete machine -/

/-- a process: pid, its cgroup (`none`: outside the run cgroup), alive -/
structure PR where
  pid : ℕ
  cg : Option ℕ
  alive : Bool
deriving DecidableEq, Repr

structure CSt where
  /-- lease cgroups: (lease id, limit) -/
  cg : List (ℕ × ℕ)
  /-- processes, newest first -/
  procs : List PR
  revoked : List ℕ
  /-- the kernel's accounting log: (pid, lease cgroup, units); its sums are the cgroup usage counters -/
  acct : List (ℕ × ℕ × ℕ)
  /-- consumption outside the run cgroup: (pid, units); the meter cannot see it -/
  outside : List (ℕ × ℕ)
  halted : Bool
deriving DecidableEq, Repr

inductive COp where
  | createLease (lid lim : ℕ)
  | launch (pid lid : ℕ)
  | launchUnplaced (pid : ℕ)
  | fork (p ch : ℕ)
  | consume (pid x : ℕ)
  | read (lid : ℕ)
  | revoke (lid : ℕ)
  | halt
deriving DecidableEq, Repr

def cinit : CSt := ⟨[], [], [], [], [], false⟩

def procOf (s : CSt) (pid : ℕ) : Option PR := s.procs.find? (fun q => q.pid = pid)

def limitOf (s : CSt) (lid : ℕ) : Option ℕ := (s.cg.find? (fun e => e.1 = lid)).map Prod.snd

/-- the kernel's usage counter of lease cgroup `lid` -/
def counter (s : CSt) (lid : ℕ) : ℕ := ((s.acct.filter (fun e => e.2.1 = lid)).map (fun e => e.2.2)).sum

/-- the run cgroup's usage counter (the kernel charges every ancestor) -/
def runCounter (s : CSt) : ℕ := (s.acct.map (fun e => e.2.2)).sum

/-- all consumption, accounted or not -/
def realTotal (s : CSt) : ℕ := runCounter s + (s.outside.map Prod.snd).sum

/-- the lease whose counters a consumption is charged to, if the kernel lets it happen (`kernel_enforcement`) -/
def consumeLease (G : ℕ) (s : CSt) (pid x : ℕ) : Option ℕ :=
  match procOf s pid with
  | some ⟨_, some lid, true⟩ =>
    if 1 ≤ x then
      match limitOf s lid with
      | some b => if counter s lid + x ≤ b ∧ runCounter s + x ≤ G then some lid else none
      | none => none
    else none
  | _ => none

/-- a live process outside the run cgroup consumes, unaccounted -/
def consumeOutside (s : CSt) (pid x : ℕ) : Bool :=
  match procOf s pid with
  | some ⟨_, none, true⟩ => decide (1 ≤ x)
  | _ => false

/-- the cgroup a forked child lands in (`fork_inherits`), if the fork happens -/
def forkCg (s : CSt) (p ch : ℕ) : Option (Option ℕ) :=
  match procOf s p with
  | some q => if q.alive = true ∧ ch ∉ s.procs.map PR.pid then some q.cg else none
  | none => none

def kill (lid : ℕ) (q : PR) : PR := if q.cg = some lid then { q with alive := false } else q

def killPlaced (q : PR) : PR := if q.cg.isSome then { q with alive := false } else q

def stepC (G : ℕ) (s : CSt) : COp → CSt
  | .createLease lid lim =>
    if s.halted = false ∧ limitOf s lid = none then { s with cg := s.cg ++ [(lid, lim)] } else s
  | .launch pid lid =>
    if s.halted = false ∧ limitOf s lid ≠ none ∧ lid ∉ s.revoked ∧ pid ∉ s.procs.map PR.pid then
      { s with procs := ⟨pid, some lid, true⟩ :: s.procs }
    else s
  | .launchUnplaced pid =>
    if pid ∉ s.procs.map PR.pid then { s with procs := ⟨pid, none, true⟩ :: s.procs } else s
  | .fork p ch =>
    match forkCg s p ch with
    | some c => { s with procs := ⟨ch, c, true⟩ :: s.procs }
    | none => s
  | .consume pid x =>
    match consumeLease G s pid x with
    | some lid => { s with acct := s.acct ++ [(pid, lid, x)] }
    | none => if consumeOutside s pid x then { s with outside := s.outside ++ [(pid, x)] } else s
  | .read _ => s
  | .revoke lid => { s with revoked := s.revoked ++ [lid], procs := s.procs.map (kill lid) }
  | .halt => { s with halted := true, procs := s.procs.map killPlaced }

def runC (G : ℕ) (s : CSt) (ops : List COp) : CSt := ops.foldl (stepC G) s

theorem runC_cons (G : ℕ) (s : CSt) (o : COp) (ops : List COp) :
    runC G s (o :: ops) = runC G (stepC G s o) ops := rfl

theorem runC_append (G : ℕ) (s : CSt) (a b : List COp) : runC G s (a ++ b) = runC G (runC G s a) b := by
  simp [runC, List.foldl_append]

/-! ## Facts about lookups -/

theorem procOf_mem {s : CSt} {pid : ℕ} {q : PR} (h : procOf s pid = some q) : q ∈ s.procs ∧ q.pid = pid := by
  unfold procOf at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem consumeLease_spec {G : ℕ} {s : CSt} {pid x lid : ℕ} (h : consumeLease G s pid x = some lid) :
    ∃ q, procOf s pid = some q ∧ q.alive = true ∧ q.cg = some lid ∧ 1 ≤ x ∧
      ∃ b, limitOf s lid = some b ∧ counter s lid + x ≤ b ∧ runCounter s + x ≤ G := by
  unfold consumeLease at h
  match hq : procOf s pid with
  | none => rw [hq] at h; exact absurd h (by simp)
  | some ⟨qp, none, qa⟩ => rw [hq] at h; exact absurd h (by simp)
  | some ⟨qp, some l, false⟩ => rw [hq] at h; exact absurd h (by simp)
  | some ⟨qp, some l, true⟩ =>
    rw [hq] at h
    dsimp only at h
    by_cases hx : 1 ≤ x
    · rw [ite_eq_left hx] at h
      cases hb : limitOf s l with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some b =>
        rw [hb] at h
        dsimp only at h
        by_cases hc : counter s l + x ≤ b ∧ runCounter s + x ≤ G
        · rw [ite_eq_left hc] at h
          cases h
          exact ⟨_, rfl, rfl, rfl, hx, b, hb, hc⟩
        · rw [ite_eq_right hc] at h; exact absurd h (by simp)
    · rw [ite_eq_right hx] at h; exact absurd h (by simp)

theorem consumeOutside_spec {s : CSt} {pid x : ℕ} (h : consumeOutside s pid x = true) :
    ∃ q, procOf s pid = some q ∧ q.cg = none := by
  unfold consumeOutside at h
  match hq : procOf s pid with
  | none => rw [hq] at h; exact absurd h (by simp)
  | some ⟨qp, none, true⟩ => exact ⟨_, rfl, rfl⟩
  | some ⟨qp, none, false⟩ => rw [hq] at h; exact absurd h (by simp)
  | some ⟨qp, some l, qa⟩ => rw [hq] at h; exact absurd h (by simp)

theorem forkCg_spec {s : CSt} {p ch : ℕ} {c : Option ℕ} (h : forkCg s p ch = some c) :
    ∃ q, procOf s p = some q ∧ q.alive = true ∧ q.cg = c ∧ ch ∉ s.procs.map PR.pid := by
  unfold forkCg at h
  cases hq : procOf s p with
  | none => rw [hq] at h; exact absurd h (by simp)
  | some q =>
    rw [hq] at h
    dsimp only at h
    by_cases hc : q.alive = true ∧ ch ∉ s.procs.map PR.pid
    · rw [ite_eq_left hc] at h; cases h; exact ⟨q, rfl, hc.1, rfl, hc.2⟩
    · rw [ite_eq_right hc] at h; exact absurd h (by simp)

/-! ## Concrete invariant -/

structure CInv (s : CSt) : Prop where
  nodup : (s.procs.map PR.pid).Nodup
  alive_rev : ∀ q ∈ s.procs, q.alive = true → ∀ l, q.cg = some l → l ∉ s.revoked
  alive_halt : ∀ q ∈ s.procs, q.alive = true → q.cg ≠ none → s.halted = false

theorem cinv_init : CInv cinit := ⟨by simp [cinit], by simp [cinit], by simp [cinit]⟩

@[simp] theorem kill_pid (lid : ℕ) (q : PR) : (kill lid q).pid = q.pid := by unfold kill; split_ifs <;> rfl
@[simp] theorem kill_cg (lid : ℕ) (q : PR) : (kill lid q).cg = q.cg := by unfold kill; split_ifs <;> rfl
@[simp] theorem killPlaced_pid (q : PR) : (killPlaced q).pid = q.pid := by unfold killPlaced; split_ifs <;> rfl
@[simp] theorem killPlaced_cg (q : PR) : (killPlaced q).cg = q.cg := by unfold killPlaced; split_ifs <;> rfl

theorem kill_dead {lid : ℕ} {q : PR} (hk : q.cg = some lid) : (kill lid q).alive = false := by simp [kill, hk]
theorem kill_other {lid : ℕ} {q : PR} (hk : ¬ q.cg = some lid) : kill lid q = q := by simp [kill, hk]
theorem killPlaced_dead {q : PR} (hk : q.cg.isSome = true) : (killPlaced q).alive = false := by
  simp [killPlaced, hk]
theorem killPlaced_other {q : PR} (hk : ¬ q.cg.isSome = true) : killPlaced q = q := by simp [killPlaced, hk]

theorem map_kill_pid (lid : ℕ) (l : List PR) : (l.map (kill lid)).map PR.pid = l.map PR.pid := by
  simp [Function.comp_def]

theorem map_killPlaced_pid (l : List PR) : (l.map killPlaced).map PR.pid = l.map PR.pid := by
  simp [Function.comp_def]

theorem cinv_step (G : ℕ) (s : CSt) (o : COp) (h : CInv s) : CInv (stepC G s o) := by
  cases o with
  | createLease lid lim =>
    simp only [stepC]; split_ifs
    · exact ⟨h.nodup, h.alive_rev, h.alive_halt⟩
    · exact h
  | launch pid lid =>
    simp only [stepC]; split_ifs with hg
    · obtain ⟨hh, _, hr, hf⟩ := hg
      refine ⟨List.nodup_cons.2 ⟨hf, h.nodup⟩, fun q hq ha l hl => ?_, fun q hq ha hc => ?_⟩
      · rcases List.mem_cons.1 hq with rfl | hq
        · simp only [Option.some.injEq] at hl; subst hl; exact hr
        · exact h.alive_rev q hq ha l hl
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact hh
        · exact h.alive_halt q hq ha hc
    · exact h
  | launchUnplaced pid =>
    simp only [stepC]
    by_cases hf : pid ∉ s.procs.map PR.pid
    · rw [ite_eq_left hf]
      refine ⟨List.nodup_cons.2 ⟨hf, h.nodup⟩, fun q hq ha l hl => ?_, fun q hq ha hc => ?_⟩
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact absurd hl (by simp)
        · exact h.alive_rev q hq ha l hl
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact absurd rfl hc
        · exact h.alive_halt q hq ha hc
    · rw [ite_eq_right hf]; exact h
  | fork p ch =>
    simp only [stepC]
    cases hf : forkCg s p ch with
    | none => exact h
    | some c =>
      obtain ⟨q0, hq0, ha0, hc0, hfresh⟩ := forkCg_spec hf
      have hm0 := (procOf_mem hq0).1
      refine ⟨List.nodup_cons.2 ⟨hfresh, h.nodup⟩, fun q hq ha l hl => ?_, fun q hq ha hc => ?_⟩
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact h.alive_rev q0 hm0 ha0 l (hc0.trans hl)
        · exact h.alive_rev q hq ha l hl
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact h.alive_halt q0 hm0 ha0 (hc0 ▸ hc)
        · exact h.alive_halt q hq ha hc
  | consume pid x =>
    simp only [stepC]
    cases hc : consumeLease G s pid x with
    | some lid => exact ⟨h.nodup, h.alive_rev, h.alive_halt⟩
    | none =>
      dsimp only
      split_ifs
      · exact ⟨h.nodup, h.alive_rev, h.alive_halt⟩
      · exact h
  | read lid => exact h
  | revoke lid =>
    refine ⟨by simp only [stepC]; rw [map_kill_pid]; exact h.nodup, fun q hq ha l hl => ?_, fun q hq ha hc => ?_⟩
    · simp only [stepC, List.mem_map] at hq
      obtain ⟨q0, hq0, rfl⟩ := hq
      simp only [stepC, List.mem_append, List.mem_singleton, not_or]
      by_cases hk : q0.cg = some lid
      · rw [kill_dead hk] at ha; exact absurd ha (by simp)
      · rw [kill_other hk] at ha hl
        exact ⟨h.alive_rev q0 hq0 ha l hl, fun he => hk (he ▸ hl)⟩
    · simp only [stepC, List.mem_map] at hq
      obtain ⟨q0, hq0, rfl⟩ := hq
      by_cases hk : q0.cg = some lid
      · rw [kill_dead hk] at ha; exact absurd ha (by simp)
      · rw [kill_other hk] at ha hc; exact h.alive_halt q0 hq0 ha hc
  | halt =>
    refine ⟨by simp only [stepC]; rw [map_killPlaced_pid]; exact h.nodup, fun q hq ha l hl => ?_,
      fun q hq ha hc => ?_⟩
    · simp only [stepC, List.mem_map] at hq
      obtain ⟨q0, hq0, rfl⟩ := hq
      by_cases hk : q0.cg.isSome = true
      · rw [killPlaced_dead hk] at ha; exact absurd ha (by simp)
      · rw [killPlaced_other hk] at hl; simp [hl] at hk
    · simp only [stepC, List.mem_map] at hq
      obtain ⟨q0, hq0, rfl⟩ := hq
      by_cases hk : q0.cg.isSome = true
      · rw [killPlaced_dead hk] at ha; exact absurd ha (by simp)
      · rw [killPlaced_other hk] at hc; exact absurd (Option.ne_none_iff_isSome.1 hc) hk

theorem cinv_run (G : ℕ) (s : CSt) (ops : List COp) (h : CInv s) : CInv (runC G s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [runC_cons]; exact ih _ (cinv_step G s o h)

/-! ## Abstraction -/

/-- placed processes as (pid, lease), newest first -/
def placed (l : List PR) : List (ℕ × ℕ) := l.filterMap fun q => q.cg.map fun c => (q.pid, c)

/-- α into the SC-28 model -/
def α (s : CSt) : SC28.St := ⟨s.cg, placed s.procs, s.revoked, s.acct.map (fun e => (e.2.1, e.2.2)), s.acct, s.halted⟩

theorem placed_fst_sub (l : List PR) (w : ℕ) (hw : w ∉ l.map PR.pid) : w ∉ (placed l).map Prod.fst := by
  intro hm
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
  obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.1 he
  cases hc : q.cg with
  | none => rw [hc] at hqe; exact absurd hqe (by simp)
  | some c =>
    rw [hc] at hqe
    simp only [Option.map_some, Option.some.injEq] at hqe
    subst hqe
    exact hw (List.mem_map.2 ⟨q, hq, rfl⟩)

/-- the model's lease lookup is the concrete process's cgroup (pids are unique) -/
theorem leaseOf_placed (l : List PR) (hnd : (l.map PR.pid).Nodup) (w : ℕ) :
    ((placed l).find? (fun e => e.1 = w)).map Prod.snd = (l.find? (fun q => q.pid = w)).bind PR.cg := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    have hnd2 : (q.pid :: l.map PR.pid).Nodup := hnd
    have hnd' := (List.nodup_cons.1 hnd2).2
    have hq := (List.nodup_cons.1 hnd2).1
    by_cases hw : q.pid = w
    · subst hw
      have hnone : (placed l).find? (fun e => e.1 = q.pid) = none := by
        rw [List.find?_eq_none]
        intro e he hep
        exact placed_fst_sub l q.pid hq (List.mem_map.2 ⟨e, he, by simpa using hep⟩)
      cases hc : q.cg with
      | none => simp [placed, hc]; simpa [placed] using hnone
      | some c => simp [placed, hc]
    · cases hc : q.cg with
      | none => simp [placed, hc, hw]; simpa [placed] using ih hnd'
      | some c => simp [placed, hc, hw]; simpa [placed] using ih hnd'

theorem leaseOf_α (s : CSt) (h : CInv s) (w : ℕ) : SC28.leaseOf (α s) w = (procOf s w).bind PR.cg :=
  leaseOf_placed s.procs h.nodup w

theorem budgetOf_α (s : CSt) (lid : ℕ) : SC28.budgetOf (α s) lid = limitOf s lid := rfl

theorem spentL_α (s : CSt) (lid : ℕ) : SC28.spentL (α s) lid = counter s lid := by
  simp [SC28.spentL, counter, α, List.filter_map, Function.comp_def]

theorem spentT_α (s : CSt) : SC28.spentT (α s) = runCounter s := by
  simp [SC28.spentT, runCounter, α, Function.comp_def]

theorem usedL_α (s : CSt) (lid : ℕ) : SC28.usedL (α s) lid = counter s lid := rfl

theorem usedT_α (s : CSt) : SC28.usedT (α s) = runCounter s := rfl

theorem placed_kill (lid : ℕ) (l : List PR) : placed (l.map (kill lid)) = placed l := by
  simp [placed, List.filterMap_map]

theorem placed_killPlaced (l : List PR) : placed (l.map killPlaced) = placed l := by
  simp [placed, List.filterMap_map]

/-! ## Forward simulation -/

/-- the model steps matching one concrete event (the controller is admin 0) -/
def opsOf (G : ℕ) (s : CSt) : COp → List SC28.Op
  | .createLease lid lim => if s.halted = false ∧ limitOf s lid = none then [.issue 0 lid lim] else []
  | .launch pid lid =>
    if s.halted = false ∧ limitOf s lid ≠ none ∧ lid ∉ s.revoked ∧ pid ∉ s.procs.map PR.pid then
      [.assignTo 0 pid lid]
    else []
  | .fork p ch =>
    match forkCg s p ch with
    | some (some _) => [.fork 0 p ch 0]
    | _ => []
  | .consume pid x =>
    match consumeLease G s pid x with
    | some _ => [.work pid x x]
    | none => []
  | .revoke lid => [.revoke 0 lid]
  | .halt => [.halt 0]
  | _ => []

theorem simulation (G : ℕ) (s : CSt) (o : COp) (h : CInv s) :
    α (stepC G s o) = SC28.run [0] G SC28.full (α s) (opsOf G s o) := by
  cases o with
  | createLease lid lim =>
    simp only [stepC, opsOf]
    by_cases hg : s.halted = false ∧ limitOf s lid = none
    · rw [ite_eq_left hg, ite_eq_left hg]
      simp only [SC28.run, List.foldl_cons, List.foldl_nil, SC28.step]
      rw [ite_eq_right (by simp [α, hg.1]), ite_eq_left ⟨List.mem_singleton_self 0, hg.2⟩]
      rfl
    · rw [ite_eq_right hg, ite_eq_right hg]; rfl
  | launch pid lid =>
    simp only [stepC, opsOf]
    by_cases hg : s.halted = false ∧ limitOf s lid ≠ none ∧ lid ∉ s.revoked ∧ pid ∉ s.procs.map PR.pid
    · rw [ite_eq_left hg, ite_eq_left hg]
      simp only [SC28.run, List.foldl_cons, List.foldl_nil, SC28.step]
      rw [ite_eq_right (by simp [α, hg.1]), ite_eq_left ⟨List.mem_singleton_self 0, hg.2.1⟩]
      rfl
    · rw [ite_eq_right hg, ite_eq_right hg]; rfl
  | launchUnplaced pid =>
    simp only [stepC, opsOf]
    by_cases hf : pid ∉ s.procs.map PR.pid
    · rw [ite_eq_left hf]; simp [SC28.run, α, placed]
    · rw [ite_eq_right hf]; rfl
  | fork p ch =>
    simp only [stepC, opsOf]
    cases hf : forkCg s p ch with
    | none => rfl
    | some c =>
      obtain ⟨q, hq, ha, hc, hfresh⟩ := forkCg_spec hf
      cases c with
      | none => simp [SC28.run, α, placed]
      | some lid =>
        have hh : s.halted = false := h.alive_halt q (procOf_mem hq).1 ha (by rw [hc]; simp)
        have hl : SC28.leaseOf (α s) p = some lid := by rw [leaseOf_α s h, hq]; exact hc
        have hn : ch ∉ (α s).assign.map Prod.fst := placed_fst_sub s.procs ch hfresh
        have hfu : SC28.forkUpd SC28.full (α s) p ch 0 = ((α s).leases, (ch, lid) :: (α s).assign) := by
          simp [SC28.forkUpd, hl, hn, SC28.full]
        simp only [SC28.run, List.foldl_cons, List.foldl_nil, SC28.step]
        rw [ite_eq_right (by simp [α, hh])]
        rw [hfu]
        simp [α, placed]
  | consume pid x =>
    simp only [stepC, opsOf]
    cases hc : consumeLease G s pid x with
    | none =>
      dsimp only
      split_ifs with ho
      · obtain ⟨q, hq, hcg⟩ := consumeOutside_spec ho
        simp [SC28.run, α]
      · rfl
    | some lid =>
      obtain ⟨q, hq, ha, hcg, hx, b, hb, hcl, hcg2⟩ := consumeLease_spec hc
      have hm := (procOf_mem hq).1
      have hh : s.halted = false := h.alive_halt q hm ha (by rw [hcg]; simp)
      have hr : lid ∉ s.revoked := h.alive_rev q hm ha lid hcg
      have hl : SC28.leaseOf (α s) pid = some lid := by rw [leaseOf_α s h, hq]; exact hcg
      have hb' : SC28.budgetOf (α s) lid = some b := hb
      have hch : SC28.charge SC28.full x x = x := by simp [SC28.charge, SC28.full]; omega
      have hguard : lid ∉ (α s).revoked ∧ SC28.spentL (α s) lid + SC28.charge SC28.full x x ≤ b ∧
          (SC28.full.global = true → SC28.spentT (α s) + SC28.charge SC28.full x x ≤ G) := by
        rw [hch, spentL_α, spentT_α]; exact ⟨hr, hcl, fun _ => hcg2⟩
      simp only [SC28.run, List.foldl_cons, List.foldl_nil, SC28.step]
      rw [ite_eq_right (by simp [α, hh]), hl]
      dsimp only
      rw [hb']
      dsimp only
      rw [ite_eq_left hguard, hch]
      simp [α]
  | read lid => rfl
  | revoke lid =>
    simp only [stepC, opsOf, SC28.run, List.foldl_cons, List.foldl_nil, SC28.step]
    simp [α, placed_kill]
  | halt =>
    simp only [stepC, opsOf, SC28.run, List.foldl_cons, List.foldl_nil, SC28.step]
    simp [α, placed_killPlaced]

/-- the model trace of a concrete trace -/
def absTrace (G : ℕ) : CSt → List COp → List SC28.Op
  | _, [] => []
  | s, o :: ops => opsOf G s o ++ absTrace G (stepC G s o) ops

theorem simulation_run (G : ℕ) (s : CSt) (ops : List COp) (h : CInv s) :
    α (runC G s ops) = SC28.run [0] G SC28.full (α s) (absTrace G s ops) := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    change α (runC G (stepC G s o) ops) = _
    rw [ih _ (cinv_step G s o h), simulation G s o h]
    simp [absTrace, SC28.run, List.foldl_append]

theorem opsOf_legal (G : ℕ) (s : CSt) (o : COp) : ∀ a ∈ opsOf G s o, SC28.legal a := by
  cases o <;> simp only [opsOf] <;> (try split_ifs) <;> (try split) <;> simp [SC28.legal]

theorem absTrace_legal (G : ℕ) (s : CSt) (ops : List COp) : ∀ a ∈ absTrace G s ops, SC28.legal a := by
  induction ops generalizing s with
  | nil => simp [absTrace]
  | cons o ops ih =>
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact opsOf_legal G s o a ha
    · exact ih _ a ha

theorem α_cinit : α cinit = SC28.init := rfl

/-! ## Transfer -/

/-- **SC-28 safety for the concrete controller** (`SC28.sc28_safe` transferred): for every concrete trace (any
leases, launches, forks, consumption, reads, revocations, HALT, and unplaced launches), α of the reached state is
`SC28.Good`. -/
theorem concrete_safe (G : ℕ) (ops : List COp) : SC28.Good G (α (runC G cinit ops)) := by
  rw [simulation_run G cinit ops cinv_init, α_cinit]
  exact SC28.sc28_safe [0] G _ (absTrace_legal G cinit ops)

/-- the same, read on the kernel's counters: run counter ≤ G, every lease counter ≤ its limit, at most G accounted
consumption events -/
theorem concrete_counters_safe (G : ℕ) (ops : List COp) :
    runCounter (runC G cinit ops) ≤ G ∧
      (∀ lid, counter (runC G cinit ops) lid ≤ (limitOf (runC G cinit ops) lid).getD 0) ∧
      (runC G cinit ops).acct.length ≤ G :=
  concrete_safe G ops

/-- **Revocation stops the lease** (`SC28.revoked_lease_stops` transferred): once `lid` is revoked, its kernel
counter never grows, whatever follows. -/
theorem concrete_revoked_stops (G : ℕ) (pre post : List COp) (lid : ℕ) (hr : lid ∈ (runC G cinit pre).revoked) :
    counter (runC G cinit (pre ++ post)) lid = counter (runC G cinit pre) lid := by
  have hinv := cinv_run G cinit pre cinv_init
  rw [← usedL_α, ← usedL_α, runC_append, simulation_run G _ post hinv]
  exact SC28.revoked_lease_stops [0] G SC28.full _ _ lid hr

/-- **HALT freezes accounting** (`SC28.halt_freezes` transferred). -/
theorem concrete_halt_freezes (G : ℕ) (pre post : List COp) (hh : (runC G cinit pre).halted = true) :
    (runC G cinit (pre ++ post)).acct = (runC G cinit pre).acct := by
  have hinv := cinv_run G cinit pre cinv_init
  have e := congrArg SC28.St.usage (simulation_run G _ post hinv)
  rw [runC_append]
  exact e.trans (SC28.halt_freezes [0] G _ _ hh)

/-! ## Exclusive placement -/

def isUnplaced : COp → Bool
  | .launchUnplaced _ => true
  | _ => false

theorem step_placed (G : ℕ) (s : CSt) (o : COp) (hu : isUnplaced o = false) (hall : ∀ q ∈ s.procs, q.cg ≠ none)
    (hout : s.outside = []) : (∀ q ∈ (stepC G s o).procs, q.cg ≠ none) ∧ (stepC G s o).outside = [] := by
  cases o with
  | launchUnplaced pid => exact absurd hu (by simp [isUnplaced])
  | createLease lid lim => simp only [stepC]; split_ifs <;> exact ⟨hall, hout⟩
  | launch pid lid =>
    simp only [stepC]; split_ifs
    · refine ⟨fun q hq => ?_, hout⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · simp
      · exact hall q hq
    · exact ⟨hall, hout⟩
  | fork p ch =>
    simp only [stepC]
    cases hf : forkCg s p ch with
    | none => exact ⟨hall, hout⟩
    | some c =>
      obtain ⟨q0, hq0, _, hc0, _⟩ := forkCg_spec hf
      refine ⟨fun q hq => ?_, hout⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · rw [← hc0]; exact hall q0 (procOf_mem hq0).1
      · exact hall q hq
  | consume pid x =>
    simp only [stepC]
    cases hc : consumeLease G s pid x with
    | some lid => exact ⟨hall, hout⟩
    | none =>
      dsimp only
      split_ifs with ho
      · obtain ⟨q, hq, hcg⟩ := consumeOutside_spec ho
        exact absurd hcg (hall q (procOf_mem hq).1)
      · exact ⟨hall, hout⟩
  | read lid => exact ⟨hall, hout⟩
  | revoke lid =>
    refine ⟨fun q hq => ?_, hout⟩
    simp only [stepC, List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    rw [kill_cg]; exact hall q0 hq0
  | halt =>
    refine ⟨fun q hq => ?_, hout⟩
    simp only [stepC, List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    rw [killPlaced_cg]; exact hall q0 hq0

/-- **Exclusive placement makes the meter complete.** In a trace without unplaced launches, nothing is consumed
outside the run cgroup, so REAL total consumption equals the run counter and is ≤ G. -/
theorem exclusive_placement_safe (G : ℕ) (ops : List COp) (hu : ∀ o ∈ ops, isUnplaced o = false) :
    (runC G cinit ops).outside = [] ∧ realTotal (runC G cinit ops) ≤ G := by
  have key : ∀ (ops : List COp) (s : CSt), (∀ o ∈ ops, isUnplaced o = false) → (∀ q ∈ s.procs, q.cg ≠ none) →
      s.outside = [] → (runC G s ops).outside = [] := by
    intro ops
    induction ops with
    | nil => intro s _ _ h; exact h
    | cons o ops ih =>
      intro s hu hall hout
      obtain ⟨h1, h2⟩ := step_placed G s o (hu o List.mem_cons_self) hall hout
      exact ih _ (fun o' ho' => hu o' (List.mem_cons_of_mem o ho')) h1 h2
  have hout := key ops cinit hu (by simp [cinit]) rfl
  refine ⟨hout, ?_⟩
  unfold realTotal
  rw [hout]
  simpa using (concrete_counters_safe G ops).1

/-! ## Witnesses -/

/-- the H5 control: lease 1 (limit 10, G = 10); process 7 launched WITHOUT placement forks 8; both consume 50 -/
def unplacedTrace : List COp := [.createLease 1 10, .launchUnplaced 7, .consume 7 50, .fork 7 8, .consume 8 50]

/-- the same tree launched WITH placement: throttled at the limit; the forked child is charged to the same lease -/
def placedTrace : List COp :=
  [.createLease 1 10, .launch 7 1, .consume 7 50, .consume 7 10, .fork 7 8, .consume 8 1]

/-- **Unplaced consumption is invisible to the transferred property** (prereg H5): 100 units are consumed with G = 10,
while α's ledger and usage are empty, so `concrete_safe` holds and says nothing about them. With placement, the
kernel throttles: 10 units, the child is on the same lease, and its extra unit is refused. -/
theorem unplaced_invisible :
    realTotal (runC 10 cinit unplacedTrace) = 100 ∧ (α (runC 10 cinit unplacedTrace)).usage = [] ∧
      (α (runC 10 cinit unplacedTrace)).ledger = [] ∧
      (runC 10 cinit placedTrace).acct = [(7, 1, 10)] ∧ realTotal (runC 10 cinit placedTrace) = 10 ∧
      (procOf (runC 10 cinit placedTrace) 8).bind PR.cg = some 1 := by
  decide

/-- revoke kills the lease and refuses later launches into it; another lease keeps working -/
theorem revoke_witness :
    let t := runC 10 cinit [.createLease 1 5, .createLease 2 5, .launch 7 1, .launch 8 2, .consume 7 2, .revoke 1,
      .consume 7 1, .launch 9 1, .consume 9 1, .consume 8 3]
    counter t 1 = 2 ∧ counter t 2 = 3 ∧ procOf t 9 = none := by
  decide

end ControlStack.SC28Refinement

#print axioms ControlStack.SC28Refinement.simulation
#print axioms ControlStack.SC28Refinement.simulation_run
#print axioms ControlStack.SC28Refinement.concrete_safe
#print axioms ControlStack.SC28Refinement.concrete_counters_safe
#print axioms ControlStack.SC28Refinement.concrete_revoked_stops
#print axioms ControlStack.SC28Refinement.concrete_halt_freezes
#print axioms ControlStack.SC28Refinement.exclusive_placement_safe
#print axioms ControlStack.SC28Refinement.unplaced_invisible
#print axioms ControlStack.SC28Refinement.revoke_witness
