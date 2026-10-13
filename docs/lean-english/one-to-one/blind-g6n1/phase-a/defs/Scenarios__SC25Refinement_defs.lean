-- EXCERPT of ControlStack/Scenarios/SC25Refinement.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC25Refinement

open ControlStack.SC25

structure CItem where
  id : ℕ
  content : ℕ
  declared : Bool
  submitter : ℕ
  cached : ℕ
deriving DecidableEq, Repr

/-- an auditor log row (principal.py): id, digest, verdict, auditor, content seen -/
structure ARow where
  id : ℕ
  d : ℕ
  pass : Bool
  by_ : ℕ
  content : ℕ
deriving DecidableEq, Repr

/-- an approver log row -/
structure PRow where
  id : ℕ
  d : ℕ
  approver : ℕ
  content : ℕ
deriving DecidableEq, Repr

/-- an effect log record -/
structure ERow where
  id : ℕ
  content : ℕ
  submitter : ℕ
  d : ℕ
  vlen : ℕ
  alen : ℕ
deriving DecidableEq, Repr

structure CSt where
  items : List CItem
  auditLog : List ARow
  apprLog : List PRow
  expired : List ℕ
  checked : List ℕ
  effects : List ERow
  halted : Bool
deriving DecidableEq, Repr

inductive COp where
  | submit (caller id content : ℕ) (declared : Bool)
  | amend (caller id content : ℕ)
  | audit (caller id : ℕ) (pass : Bool)
  | approve (caller id : ℕ)
  | expire (id : ℕ)
  | check (id : ℕ)
  | fire (id : ℕ)
  | crash
  | restart
  | halt (caller : ℕ)
deriving DecidableEq, Repr

def cinit : CSt := ⟨[], [], [], [], [], [], false⟩

def toItem (c : CItem) : Item := ⟨c.id, c.content, c.declared, c.submitter⟩
def toVerdict (a : ARow) : Verdict := ⟨a.id, a.d, a.pass, some a.by_⟩
def toAppr (p : PRow) : Appr := ⟨p.id, p.d, p.approver⟩
def toExec (e : ERow) : Exec := ⟨e.id, e.content, e.submitter, e.vlen, e.alen⟩

/-- the abstraction: drop the content fields of the logs and the cached digests -/
def α (s : CSt) : St :=
  ⟨s.items.map toItem, s.auditLog.map toVerdict, s.apprLog.map toAppr, s.expired, s.checked, s.effects.map toExec,
    s.halted⟩

def citemOf (s : CSt) (id : ℕ) : Option CItem := s.items.find? (fun it => it.id = id)

/-- the executor's fire-time validation, with the digest it checks (`dd`) -/
abbrev ValidC (_h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (it : CItem) (dd : ℕ) : Prop :=
  it.id ∉ s.expired ∧ (∃ v ∈ s.auditLog, v.id = it.id ∧ v.pass = true ∧ v.d = dd) ∧
    (cls it.content = true → ∃ ap ∈ s.apprLog, ap.id = it.id ∧ ap.d = dd ∧ ap.approver ≠ it.submitter)

/-- the digest the executor checks at fire time -/
def fireDigest (h : ℕ → ℕ) (cachedDigest : Bool) (it : CItem) : ℕ := if cachedDigest then it.cached else h it.content

def stepC (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (cachedDigest : Bool) (s : CSt) : COp → CSt
  | .submit c id x decl =>
    if s.halted then s
    else if c ∈ R.agents ∧ citemOf s id = none then { s with items := ⟨id, x, decl, c, h x⟩ :: s.items } else s
  | .amend c id x =>
    if s.halted then s
    else match citemOf s id with
      | none => s
      | some it =>
        if c ∈ R.agents ∧ id ∉ s.effects.map ERow.id then { s with items := { it with content := x } :: s.items }
        else s
  | .audit c id pass =>
    if s.halted then s
    else match citemOf s id with
      | none => s
      | some it =>
        if c ∈ R.auditors then { s with auditLog := s.auditLog ++ [⟨id, h it.content, pass, c, it.content⟩] } else s
  | .approve c id =>
    if s.halted then s
    else match citemOf s id with
      | none => s
      | some it =>
        if c ∈ R.approvers then { s with apprLog := s.apprLog ++ [⟨id, h it.content, c, it.content⟩] } else s
  | .expire id =>
    if s.halted then s
    else match citemOf s id with
      | none => s
      | some _ => if ∃ v ∈ s.auditLog, v.id = id then s else { s with expired := s.expired ++ [id] }
  | .check id =>
    if s.halted then s
    else match citemOf s id with
      | none => s
      | some it => if ValidC h cls s it (h it.content) then { s with checked := id :: s.checked } else s
  | .fire id =>
    if s.halted then s
    else match citemOf s id with
      | none => s
      | some it =>
        if id ∉ s.effects.map ERow.id ∧ ValidC h cls s it (fireDigest h cachedDigest it) then
          { s with checked := id :: s.checked,
                   effects := s.effects ++ [⟨id, it.content, it.submitter, fireDigest h cachedDigest it,
                     s.auditLog.length, s.apprLog.length⟩] }
        else s
  | .crash => { s with checked := [] }
  | .restart => s
  | .halt c => if c ∈ R.admins then { s with halted := true } else s

def runC (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (cd : Bool) (s : CSt) (ops : List COp) : CSt :=
  ops.foldl (stepC R h cls cd) s

/-- the model operations matching one concrete step (deployed executor) -/
def opsOf (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) : COp → List Op
  | .submit c id x d => [.submit c id x d]
  | .amend c id x => [.amend c id x]
  | .audit c id p => [.audit c id p]
  | .approve c id => [.approve c id]
  | .expire id => [.timeout id]
  | .check id => [.check id]
  | .fire id =>
    if s.halted then []
    else match citemOf s id with
      | none => []
      | some it => if id ∉ s.effects.map ERow.id ∧ ValidC h cls s it (h it.content) then [.check id, .fire id] else []
  | .crash => [.crash]
  | .restart => []
  | .halt c => [.halt c]



def absTrace (h : ℕ → ℕ) (cls : ℕ → Bool) (R : Roles) : CSt → List COp → List Op
  | _, [] => []
  | s, o :: ops => opsOf h cls s o ++ absTrace h cls R (stepC R h cls false s o) ops

/-- the concrete invariant: audit rows record the digest of the content they saw, and every audited or executed
content is in the items journal -/
structure CInv (h : ℕ → ℕ) (s : CSt) : Prop where
  arow : ∀ a ∈ s.auditLog, h a.content = a.d ∧ ∃ it ∈ s.items, it.content = a.content
  erow : ∀ e ∈ s.effects, ∃ it ∈ s.items, it.content = e.content

end ControlStack.SC25Refinement

