-- EXCERPT of ControlStack/Scenarios/SC28Refinement.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC28Refinement



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

structure CInv (s : CSt) : Prop where
  nodup : (s.procs.map PR.pid).Nodup
  alive_rev : ∀ q ∈ s.procs, q.alive = true → ∀ l, q.cg = some l → l ∉ s.revoked
  alive_halt : ∀ q ∈ s.procs, q.alive = true → q.cg ≠ none → s.halted = false

/-- placed processes as (pid, lease), newest first -/
def placed (l : List PR) : List (ℕ × ℕ) := l.filterMap fun q => q.cg.map fun c => (q.pid, c)

/-- α into the SC-28 model -/
def α (s : CSt) : SC28.St := ⟨s.cg, placed s.procs, s.revoked, s.acct.map (fun e => (e.2.1, e.2.2)), s.acct, s.halted⟩

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

/-- the model trace of a concrete trace -/
def absTrace (G : ℕ) : CSt → List COp → List SC28.Op
  | _, [] => []
  | s, o :: ops => opsOf G s o ++ absTrace G (stepC G s o) ops

def isUnplaced : COp → Bool
  | .launchUnplaced _ => true
  | _ => false

/-- the H5 control: lease 1 (limit 10, G = 10); process 7 launched WITHOUT placement forks 8; both consume 50 -/
def unplacedTrace : List COp := [.createLease 1 10, .launchUnplaced 7, .consume 7 50, .fork 7 8, .consume 8 50]

/-- the same tree launched WITH placement: throttled at the limit; the forked child is charged to the same lease -/
def placedTrace : List COp :=
  [.createLease 1 10, .launch 7 1, .consume 7 50, .consume 7 10, .fork 7 8, .consume 8 1]

end ControlStack.SC28Refinement

