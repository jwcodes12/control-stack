-- EXCERPT of ControlStack/Scenarios/SC25Audit.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

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



def R0 : Roles := ⟨[1], [2], [3], [4]⟩
def cls0 : ℕ → Bool := fun x => decide (100 ≤ x)

end ControlStack.SC25

