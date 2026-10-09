/-
SC-25: no irreversible operation before a trusted audit (and, for irreversible operations, an approval) completes.

The SC-25 bad event is an agent hiding or MISORDERING hazardous actions behind after-the-fact monitoring. One JOINT
shared-state transition system (pattern of `SC26Transaction.lean`; the single-row ancestor is `AuditDispatch.lean`):
- a durable queue of operations submitted by agents (an agent may AMEND a queued operation's content);
- a trusted auditor records verdicts (operation id, digest of the content it audited, pass/fail);
- a trusted classifier `cls` decides which contents are irreversible; those also need an approval of exactly that
  digest from an approver other than the submitter;
- an executor in two phases, `check` then `fire`, with a volatile `checked` set that a crash erases; `fire` in the
  deployed configuration re-validates atomically against the CURRENT content;
- a timeout for an operation with no verdict: fail CLOSED (the operation expires and never executes);
- an absorbing admin HALT.

Main results (deployed configuration `full`; adversary: TRACE_ARBITRARY over this system):
- `sc25_safe`: from `init`, after any trace, every executed operation had, AT THE MOMENT IT EXECUTED (the verdict and
  approval logs are cut at their lengths then), a passing verdict from an auditor for exactly the executed content's
  digest, and, if the content is irreversible, an approval of exactly that digest by an approver who is not the
  submitter; each operation executes at most once;
- `expired_never_executes`: once an operation timed out without a verdict, no trace executes it (fail closed);
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`); non-vacuity `honest_reversible`,
  `honest_irreversible_with_crash`.

Necessity witnesses: `fail_open_timeout_breaks`, `digest_unchecked_breaks` (an audit of different content),
`nonatomic_check_race_breaks` (check, amend, fire), `agent_declared_class_breaks`, `no_halt_check_breaks`; and the
positive `audit_fail_blocks`.

Premises outside the model: the executor is the only path to the effect; auditor/approver/admin credentials are held by
those principals; the digest is collision-resistant on the contents in play (as in SC-16; here the digest is `h`,
compared exactly); the classifier is right about which contents are irreversible. Not claimed: that a passing audit
means the operation is harmless. No new mathematics: inductions over the trace.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC25

open ControlStack.Gate

structure Roles where
  agents : List ℕ
  auditors : List ℕ
  approvers : List ℕ
  admins : List ℕ

/-- a queued operation; `declared` is the agent's own irreversibility label -/
structure Item where
  id : ℕ
  content : ℕ
  declared : Bool
  submitter : ℕ
deriving DecidableEq, Repr

/-- a verdict on digest `d` of operation `id`; `by = none` is a system-generated (fail-open) verdict -/
structure Verdict where
  id : ℕ
  d : ℕ
  pass : Bool
  by_ : Option ℕ
deriving DecidableEq, Repr

structure Appr where
  id : ℕ
  d : ℕ
  approver : ℕ
deriving DecidableEq, Repr

/-- an execution: the content run, its submitter, and the lengths of the verdict and approval logs at that moment -/
structure Exec where
  id : ℕ
  content : ℕ
  submitter : ℕ
  vlen : ℕ
  alen : ℕ
deriving DecidableEq, Repr

structure St where
  /-- newest version first -/
  queue : List Item
  verdicts : List Verdict
  approvals : List Appr
  expired : List ℕ
  /-- the executor's volatile state, lost on a crash -/
  checked : List ℕ
  executed : List Exec
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | submit (caller id content : ℕ) (declared : Bool)
  | amend (caller id content : ℕ)
  | audit (caller id : ℕ) (pass : Bool)
  | approve (caller id : ℕ)
  | timeout (id : ℕ)
  | check (id : ℕ)
  | fire (id : ℕ)
  | crash
  | halt (caller : ℕ)
deriving DecidableEq, Repr

/-- implementation checks; `full` is the deployed configuration (note `failOpen = false`) -/
structure Checks where
  digest : Bool
  atomic : Bool
  failOpen : Bool
  trustedClass : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, false, true, true⟩

def init : St := ⟨[], [], [], [], [], [], false⟩

def itemOf (s : St) (id : ℕ) : Option Item := s.queue.find? (fun it => it.id = id)

def irrevOf (cls : ℕ → Bool) (C : Checks) (it : Item) : Bool := if C.trustedClass then cls it.content else it.declared

/-- the executor's validity test for queued item `it` -/
abbrev Valid (h : ℕ → ℕ) (cls : ℕ → Bool) (C : Checks) (s : St) (it : Item) : Prop :=
  it.id ∉ s.expired ∧ (∃ v ∈ s.verdicts, v.id = it.id ∧ v.pass = true ∧ (C.digest = true → v.d = h it.content)) ∧
    (irrevOf cls C it = true →
      ∃ ap ∈ s.approvals, ap.id = it.id ∧ (C.digest = true → ap.d = h it.content) ∧ ap.approver ≠ it.submitter)

def step (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (C : Checks) (s : St) : Op → St
  | .submit c id x decl =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ R.agents ∧ itemOf s id = none then { s with queue := ⟨id, x, decl, c⟩ :: s.queue } else s
  | .amend c id x =>
    if s.halted ∧ C.haltCheck then s
    else match itemOf s id with
      | none => s
      | some it =>
        if c ∈ R.agents ∧ id ∉ s.executed.map Exec.id then { s with queue := { it with content := x } :: s.queue }
        else s
  | .audit c id pass =>
    if s.halted ∧ C.haltCheck then s
    else match itemOf s id with
      | none => s
      | some it => if c ∈ R.auditors then { s with verdicts := s.verdicts ++ [⟨id, h it.content, pass, some c⟩] } else s
  | .approve c id =>
    if s.halted ∧ C.haltCheck then s
    else match itemOf s id with
      | none => s
      | some it => if c ∈ R.approvers then { s with approvals := s.approvals ++ [⟨id, h it.content, c⟩] } else s
  | .timeout id =>
    if s.halted ∧ C.haltCheck then s
    else match itemOf s id with
      | none => s
      | some it =>
        if ∃ v ∈ s.verdicts, v.id = id then s
        else if C.failOpen then { s with verdicts := s.verdicts ++ [⟨id, h it.content, true, none⟩] }
        else { s with expired := s.expired ++ [id] }
  | .check id =>
    if s.halted ∧ C.haltCheck then s
    else match itemOf s id with
      | none => s
      | some it => if Valid h cls C s it then { s with checked := id :: s.checked } else s
  | .fire id =>
    if s.halted ∧ C.haltCheck then s
    else match itemOf s id with
      | none => s
      | some it =>
        if id ∈ s.checked ∧ id ∉ s.executed.map Exec.id ∧ (C.atomic = true → Valid h cls C s it) then
          { s with executed := s.executed ++ [⟨id, it.content, it.submitter, s.verdicts.length, s.approvals.length⟩] }
        else s
  | .crash => { s with checked := [] }
  | .halt c => if c ∈ R.admins then { s with halted := true } else s

def run (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (C : Checks) (s : St) (ops : List Op) : St :=
  ops.foldl (step R h cls C) s

theorem run_cons (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run R h cls C s (o :: ops) = run R h cls C (step R h cls C s o) ops := rfl

/-! ## Invariant and safety -/

/-- an execution backed, at its moment, by an auditor's pass of exactly its content and, if irreversible, by an
independent approval of exactly that content -/
def ExecOk (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (e : Exec) : Prop :=
  (∃ v ∈ s.verdicts.take e.vlen, v.id = e.id ∧ v.pass = true ∧ v.d = h e.content ∧ ∃ a, v.by_ = some a ∧ a ∈ R.auditors) ∧
  (cls e.content = true → ∃ ap ∈ s.approvals.take e.alen, ap.id = e.id ∧ ap.d = h e.content ∧
    ap.approver ∈ R.approvers ∧ ap.approver ≠ e.submitter)

def Good (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) : Prop :=
  (∀ e ∈ s.executed, ExecOk R h cls s e) ∧ (s.executed.map Exec.id).Nodup

structure Inv (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) : Prop where
  v_ok : ∀ v ∈ s.verdicts, ∃ a, v.by_ = some a ∧ a ∈ R.auditors
  a_ok : ∀ ap ∈ s.approvals, ap.approver ∈ R.approvers
  e_ok : ∀ e ∈ s.executed, e.vlen ≤ s.verdicts.length ∧ e.alen ≤ s.approvals.length ∧
    (∃ v ∈ s.verdicts.take e.vlen, v.id = e.id ∧ v.pass = true ∧ v.d = h e.content) ∧
    (cls e.content = true → ∃ ap ∈ s.approvals.take e.alen, ap.id = e.id ∧ ap.d = h e.content ∧
      ap.approver ≠ e.submitter)
  nodup : (s.executed.map Exec.id).Nodup

theorem inv_init (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) : Inv R h cls init :=
  ⟨by simp [init], by simp [init], by simp [init], by simp [init]⟩

theorem Inv.good {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s : St} (hi : Inv R h cls s) : Good R h cls s := by
  refine ⟨fun e he => ?_, hi.nodup⟩
  obtain ⟨_, _, ⟨v, hv, h1, h2, h3⟩, hap⟩ := hi.e_ok e he
  refine ⟨⟨v, hv, h1, h2, h3, hi.v_ok v (List.mem_of_mem_take hv)⟩, fun hc => ?_⟩
  obtain ⟨ap, hap, h4, h5, h6⟩ := hap hc
  exact ⟨ap, hap, h4, h5, hi.a_ok ap (List.mem_of_mem_take hap), h6⟩

theorem take_prefix {α : Type} {l m : List α} (hp : l <+: m) {n : ℕ} (hn : n ≤ l.length) : m.take n = l.take n := by
  obtain ⟨t, rfl⟩ := hp
  exact List.take_append_of_le_length hn

/-- a step that leaves executions alone and only appends (validly) to the verdict and approval logs -/
theorem inv_of_mono {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s t : St} (hi : Inv R h cls s)
    (hv : s.verdicts <+: t.verdicts) (ha : s.approvals <+: t.approvals)
    (hvn : ∀ v ∈ t.verdicts, v ∉ s.verdicts → ∃ a, v.by_ = some a ∧ a ∈ R.auditors)
    (han : ∀ ap ∈ t.approvals, ap ∉ s.approvals → ap.approver ∈ R.approvers) (he : t.executed = s.executed) :
    Inv R h cls t := by
  refine ⟨fun v hm => ?_, fun ap hm => ?_, fun e hm => ?_, he ▸ hi.nodup⟩
  · by_cases hs : v ∈ s.verdicts
    · exact hi.v_ok v hs
    · exact hvn v hm hs
  · by_cases hs : ap ∈ s.approvals
    · exact hi.a_ok ap hs
    · exact han ap hm hs
  · rw [he] at hm
    obtain ⟨h1, h2, h3, h4⟩ := hi.e_ok e hm
    refine ⟨h1.trans hv.length_le, h2.trans ha.length_le, ?_, ?_⟩
    · rw [take_prefix hv h1]; exact h3
    · rw [take_prefix ha h2]; exact h4

theorem mono_same {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s t : St} (hi : Inv R h cls s)
    (hv : t.verdicts = s.verdicts) (ha : t.approvals = s.approvals) (he : t.executed = s.executed) :
    Inv R h cls t :=
  inv_of_mono hi (hv ▸ List.prefix_refl _) (ha ▸ List.prefix_refl _) (fun _ hm hn => absurd (hv ▸ hm) hn)
    (fun _ hm hn => absurd (ha ▸ hm) hn) he

theorem audit_inv {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s : St} (hi : Inv R h cls s) (v : Verdict)
    (hv : ∃ a, v.by_ = some a ∧ a ∈ R.auditors) : Inv R h cls { s with verdicts := s.verdicts ++ [v] } := by
  refine inv_of_mono hi (List.prefix_append _ _) (List.prefix_refl _) ?_ (fun _ hm hn => absurd hm hn) rfl
  intro w hm hn
  rcases List.mem_append.1 hm with hm | hm
  · exact absurd hm hn
  · simp at hm; subst hm; exact hv

theorem approve_inv {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s : St} (hi : Inv R h cls s) (ap : Appr)
    (ha : ap.approver ∈ R.approvers) : Inv R h cls { s with approvals := s.approvals ++ [ap] } := by
  refine inv_of_mono hi (List.prefix_refl _) (List.prefix_append _ _) (fun _ hm hn => absurd hm hn) ?_ rfl
  intro w hm hn
  rcases List.mem_append.1 hm with hm | hm
  · exact absurd hm hn
  · simp at hm; subst hm; exact ha

theorem itemOf_id {s : St} {id : ℕ} {it : Item} (h : itemOf s id = some it) : it.id = id := by
  simpa using List.find?_some h

theorem fire_inv {R : Roles} {h : ℕ → ℕ} {cls : ℕ → Bool} {s : St} (hi : Inv R h cls s) (id : ℕ) (it : Item)
    (hit : itemOf s id = some it) (hn : id ∉ s.executed.map Exec.id) (hval : Valid h cls full s it) :
    Inv R h cls { s with executed := s.executed ++
      [⟨id, it.content, it.submitter, s.verdicts.length, s.approvals.length⟩] } := by
  have hid := itemOf_id hit
  obtain ⟨_, ⟨v, hv, h1, h2, h3⟩, hap⟩ := hval
  simp only [full, forall_const, irrevOf, ite_true] at h3 hap
  refine ⟨hi.v_ok, hi.a_ok, fun e hm => ?_, ?_⟩
  · rcases List.mem_append.1 hm with hm | hm
    · exact hi.e_ok e hm
    · simp at hm
      subst hm
      refine ⟨le_rfl, le_rfl, ?_, fun hc => ?_⟩
      · rw [List.take_length]
        exact ⟨v, hv, h1.trans hid, h2, h3⟩
      · rw [List.take_length]
        obtain ⟨ap, ha, h4, h5, h6⟩ := hap hc
        exact ⟨ap, ha, h4.trans hid, h5, h6⟩
  · simp only [List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.2 ⟨hi.nodup, List.nodup_singleton _, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb
    subst hb
    rintro rfl
    exact hn ha

theorem step_inv (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) (hi : Inv R h cls s) :
    Inv R h cls (step R h cls full s o) := by
  cases o with
  | fire id =>
    simp only [step]
    split_ifs
    · exact hi
    · split
      · exact hi
      · rename_i it hit
        split_ifs with hc
        · obtain ⟨_, hn, hval⟩ := hc
          exact fire_inv hi id it hit hn (hval rfl)
        · exact hi
  | crash => exact mono_same hi rfl rfl rfl
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first
      | exact hi
      | exact mono_same hi rfl rfl rfl
      | exact audit_inv hi _ ⟨_, rfl, by assumption⟩
      | exact approve_inv hi _ (by assumption)
      | simp_all [full]

theorem run_inv (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List Op) (hi : Inv R h cls s) :
    Inv R h cls (run R h cls full s ops) := by
  induction ops generalizing s with
  | nil => exact hi
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv R h cls s o hi)

/-- **SC-25 safety.** After any trace from `init`, every executed operation had, at the moment it executed, an
auditor's pass verdict for exactly the executed content's digest and, if that content is irreversible, an approval
of exactly that digest by an approver other than the submitter; no operation executes twice. Adversary:
TRACE_ARBITRARY (any interleaving of submissions, amendments, audits, approvals, timeouts, checks, fires, crashes). -/
theorem sc25_safe (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) :
    Good R h cls (run R h cls full init ops) :=
  (run_inv R h cls init ops (inv_init R h cls)).good

/-! ## Fail closed, halt -/

theorem step_expired (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) (id : ℕ) (hx : id ∈ s.expired)
    (hn : id ∉ s.executed.map Exec.id) :
    id ∈ (step R h cls full s o).expired ∧ id ∉ (step R h cls full s o).executed.map Exec.id := by
  cases o with
  | fire i =>
    simp only [step]
    split_ifs
    · exact ⟨hx, hn⟩
    · split
      · exact ⟨hx, hn⟩
      · rename_i it hit
        split_ifs with hc
        · obtain ⟨_, _, hval⟩ := hc
          have hv := (hval rfl).1
          have hid := itemOf_id hit
          refine ⟨hx, ?_⟩
          simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton, not_or]
          exact ⟨hn, fun he => hv (by rw [hid, ← he]; exact hx)⟩
        · exact ⟨hx, hn⟩
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact ⟨hx, hn⟩ | exact ⟨List.mem_append_left _ hx, hn⟩

/-- **Fail closed**: an operation that timed out without a verdict (and had not executed) never executes. -/
theorem expired_never_executes (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List Op) (id : ℕ)
    (hx : id ∈ s.expired) (hn : id ∉ s.executed.map Exec.id) :
    id ∉ (run R h cls full s ops).executed.map Exec.id := by
  induction ops generalizing s with
  | nil => exact hn
  | cons o ops ih =>
    rw [run_cons]
    obtain ⟨h1, h2⟩ := step_expired R h cls s o id hx hn
    exact ih _ h1 h2

theorem step_halted (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) (hh : s.halted = true) :
    (step R h cls full s o).executed = s.executed ∧ (step R h cls full s o).halted = true := by
  cases o with
  | crash => simp [step, hh]
  | halt c => simp only [step]; split_ifs <;> simp [hh]
  | _ => simp [step, full, hh]

/-- **Halt freezes execution**: once halted, no trace executes anything. -/
theorem halt_freezes (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List Op) (hh : s.halted = true) :
    (run R h cls full s ops).executed = s.executed := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    rw [run_cons]
    obtain ⟨h1, h2⟩ := step_halted R h cls s o hh
    rw [ih _ h2, h1]

/-! ## Client of the shared gate interface -/

theorem executed_prefix (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (C : Checks) (s : St) (o : Op) :
    s.executed <+: (step R h cls C s o).executed := by
  cases o with
  | fire i =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | crash => exact List.prefix_refl _
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals exact List.prefix_refl _

/-- the SC-25 gate as a `Gate.System`; its effect log is the execution log (acceptability uses the logs cut at each execution, so it is stable as they grow) -/
def sys (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) : System St Op Exec where
  step := step R h cls full
  effects := St.executed

def spec (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) : Spec (sys R h cls) where
  Inv := Inv R h cls
  ok := ExecOk R h cls
  step_inv := fun s o hi => step_inv R h cls s o hi
  log_prefix := fun s o => executed_prefix R h cls full s o
  inv_ok := fun _ hi e he => hi.good.1 e he

/-! ## Non-vacuity and necessity witnesses

Agent 1, auditor 2, approver 3, admin 4; digest `id`; contents ≥ 100 are irreversible. -/

def R0 : Roles := ⟨[1], [2], [3], [4]⟩
def cls0 : ℕ → Bool := fun x => decide (100 ≤ x)

/-- **Non-vacuity (reversible)**: submit, audit, check, fire executes the operation. -/
theorem honest_reversible :
    ((run R0 id cls0 full init [.submit 1 0 7 false, .audit 2 0 true, .check 0, .fire 0]).executed.map Exec.content)
      = [7] := by
  decide

/-- **Non-vacuity (irreversible, with a crash)**: the crash erases the executor's check, so the first `fire` is refused;
after a re-check the operation executes exactly once. -/
theorem honest_irreversible_with_crash :
    ((run R0 id cls0 full init [.submit 1 0 100 true, .audit 2 0 true, .approve 3 0, .check 0, .crash, .fire 0,
      .check 0, .fire 0, .fire 0]).executed.map Exec.content) = [100] := by
  decide

/-- a failing audit blocks execution -/
theorem audit_fail_blocks :
    (run R0 id cls0 full init [.submit 1 0 7 false, .audit 2 0 false, .check 0, .fire 0]).executed = [] := by
  decide

/-- **fail-open timeout breaks**: an operation nobody audited executes on a system-generated pass; fail-closed (the
deployed configuration) expires it instead -/
theorem fail_open_timeout_breaks :
    let s := run R0 id cls0 { full with failOpen := true } init [.submit 1 0 7 false, .timeout 0, .check 0, .fire 0]
    s.executed.map Exec.content = [7] ∧ s.verdicts.map Verdict.by_ = [none] ∧
    (run R0 id cls0 full init [.submit 1 0 7 false, .timeout 0, .check 0, .fire 0]).executed = [] := by
  decide

/-- **audit of different content breaks**: without the digest check, content amended after the audit executes -/
theorem digest_unchecked_breaks :
    let s := run R0 id cls0 { full with digest := false } init
      [.submit 1 0 7 false, .audit 2 0 true, .amend 1 0 66, .check 0, .fire 0]
    s.executed.map Exec.content = [66] ∧ s.verdicts.map Verdict.d = [7] := by
  decide

/-- **non-atomic check-then-fire race breaks**: the check passes on the audited content, the agent amends, the
executor fires the amended content; the deployed (atomic re-validating) executor refuses -/
theorem nonatomic_check_race_breaks :
    (run R0 id cls0 { full with atomic := false } init
      [.submit 1 0 7 false, .audit 2 0 true, .check 0, .amend 1 0 66, .fire 0]).executed.map Exec.content = [66] ∧
    (run R0 id cls0 full init
      [.submit 1 0 7 false, .audit 2 0 true, .check 0, .amend 1 0 66, .fire 0]).executed = [] := by
  decide

/-- **agent-declared class breaks**: an irreversible operation the agent labels reversible executes without an
approval; with the trusted classifier it needs one -/
theorem agent_declared_class_breaks :
    let s := run R0 id cls0 { full with trustedClass := false } init
      [.submit 1 0 100 false, .audit 2 0 true, .check 0, .fire 0]
    s.executed.map Exec.content = [100] ∧ s.approvals = [] ∧
    (run R0 id cls0 full init [.submit 1 0 100 false, .audit 2 0 true, .check 0, .fire 0]).executed = [] := by
  decide

/-- without the halt check, a checked operation still fires after the halt -/
theorem no_halt_check_breaks :
    (run R0 id cls0 { full with haltCheck := false } init
      [.submit 1 0 7 false, .audit 2 0 true, .check 0, .halt 4, .fire 0]).executed.map Exec.content = [7] ∧
    (run R0 id cls0 full init [.submit 1 0 7 false, .audit 2 0 true, .check 0, .halt 4, .fire 0]).executed = [] := by
  decide

end ControlStack.SC25

#print axioms ControlStack.SC25.sc25_safe
#print axioms ControlStack.SC25.expired_never_executes
#print axioms ControlStack.SC25.halt_freezes
#print axioms ControlStack.SC25.spec
#print axioms ControlStack.SC25.honest_reversible
#print axioms ControlStack.SC25.honest_irreversible_with_crash
#print axioms ControlStack.SC25.audit_fail_blocks
#print axioms ControlStack.SC25.fail_open_timeout_breaks
#print axioms ControlStack.SC25.digest_unchecked_breaks
#print axioms ControlStack.SC25.nonatomic_check_race_breaks
#print axioms ControlStack.SC25.agent_declared_class_breaks
#print axioms ControlStack.SC25.no_halt_check_breaks
