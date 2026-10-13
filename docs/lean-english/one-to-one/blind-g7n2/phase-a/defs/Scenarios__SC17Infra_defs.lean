-- EXCERPT of ControlStack/Scenarios/SC17Infra.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC17

open ControlStack.Gate

/-- a grant: (subject, verb, resource) -/
abbrev G := ℕ × ℕ × ℕ

structure Diff where
  adds : List G
  dels : List G
deriving DecidableEq, Repr

def applyDiff (st : List G) (d : Diff) : List G := st.filter (fun g => g ∉ d.dels) ++ d.adds

structure Env where
  reviewers : List ℕ
  admins : List ℕ
  allowed : List G → Bool

structure Pr where
  id : ℕ
  author : ℕ
  diff : Diff
deriving DecidableEq, Repr

structure Ap where
  id : ℕ
  reviewer : ℕ
  author : ℕ
  diff : Diff
deriving DecidableEq, Repr

/-- an apply: proposal, author, diff applied, live and desired state right after -/
structure AppRec where
  id : ℕ
  author : ℕ
  diff : Diff
  live : List G
  desired : List G
deriving DecidableEq, Repr

structure St where
  desired : List G
  live : List G
  /-- newest version first -/
  props : List Pr
  approvals : List Ap
  applied : List AppRec
  done : List ℕ
  flags : List ℕ
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | propose (caller id : ℕ) (d : Diff)
  | amend (caller id : ℕ) (d : Diff)
  | approve (caller id : ℕ)
  | oob (g : G)
  | reconcile
  | apply (id : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  exact : Bool
  resultCheck : Bool
  drift : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init (g0 : List G) : St := ⟨g0, g0, [], [], [], [], [], false⟩

def propOf (s : St) (id : ℕ) : Option Pr := s.props.find? (fun p => p.id = id)

/-- the live state an apply produces: from the desired state (drift reverted) or, without drift handling, from live -/
def newLive (C : Checks) (s : St) (d : Diff) : List G := applyDiff (if C.drift then s.desired else s.live) d

def ceilingOk (E : Env) (C : Checks) (s : St) (d : Diff) : Bool :=
  if C.resultCheck then E.allowed (newLive C s d) else E.allowed d.adds

/-- drift seen at an apply is flagged -/
def flagUpd (C : Checks) (s : St) (id : ℕ) : List ℕ := if C.drift ∧ s.live ≠ s.desired then s.flags ++ [id] else s.flags

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .propose c id d =>
    if s.halted ∧ C.haltCheck then s
    else if propOf s id = none then { s with props := ⟨id, c, d⟩ :: s.props } else s
  | .amend c id d =>
    if s.halted ∧ C.haltCheck then s
    else match propOf s id with
      | none => s
      | some p => if p.author = c then { s with props := ⟨id, c, d⟩ :: s.props } else s
  | .approve c id =>
    if s.halted ∧ C.haltCheck then s
    else match propOf s id with
      | none => s
      | some p =>
        if c ∈ E.reviewers ∧ c ≠ p.author then { s with approvals := s.approvals ++ [⟨id, c, p.author, p.diff⟩] }
        else s
  | .oob g => { s with live := g :: s.live }
  | .reconcile =>
    if s.halted ∧ C.haltCheck then s
    else if C.drift ∧ s.live ≠ s.desired then { s with live := s.desired, flags := s.flags ++ [0] } else s
  | .apply id =>
    if s.halted ∧ C.haltCheck then s
    else match propOf s id with
      | none => s
      | some p =>
        if id ∉ s.done ∧ (∃ a ∈ s.approvals, a.id = id ∧ a.author = p.author ∧ (C.exact = true → a.diff = p.diff)) ∧
            ceilingOk E C s p.diff = true then
          { s with desired := applyDiff s.desired p.diff, live := newLive C s p.diff,
                   applied := s.applied ++ [⟨id, p.author, p.diff, newLive C s p.diff, applyDiff s.desired p.diff⟩],
                   done := s.done ++ [id],
                   flags := flagUpd C s id }
        else s
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

/-- at the apply: live equals desired, within the ceiling, and the diff is exactly one an independent reviewer approved -/
def AppOk (E : Env) (s : St) (e : AppRec) : Prop :=
  E.allowed e.live = true ∧ e.live = e.desired ∧
    ∃ a ∈ s.approvals, a.id = e.id ∧ a.diff = e.diff ∧ a.reviewer ∈ E.reviewers ∧ a.reviewer ≠ e.author

def Good (E : Env) (s : St) : Prop := (∀ e ∈ s.applied, AppOk E s e) ∧ (s.applied.map AppRec.id).Nodup

structure Inv (E : Env) (s : St) : Prop where
  appr : ∀ a ∈ s.approvals, a.reviewer ∈ E.reviewers ∧ a.reviewer ≠ a.author
  apps : ∀ e ∈ s.applied, E.allowed e.live = true ∧ e.live = e.desired ∧
    ∃ a ∈ s.approvals, a.id = e.id ∧ a.diff = e.diff ∧ a.author = e.author
  done_ok : ∀ e ∈ s.applied, e.id ∈ s.done
  nodup : (s.applied.map AppRec.id).Nodup

def sys (E : Env) : System St Op AppRec where
  step := step E full
  effects := St.applied

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := AppOk E
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => applied_prefix E full s o
  inv_ok := fun _ h e he => h.good.1 e he



def E0 : Env := ⟨[2], [9], fun st => !(decide ((1, 1, 1) ∈ st) && decide ((1, 2, 1) ∈ st))⟩

def dA : Diff := ⟨[(1, 1, 1)], []⟩
def dB : Diff := ⟨[(1, 2, 1)], []⟩
def dC : Diff := ⟨[(3, 3, 3)], []⟩

end ControlStack.SC17

