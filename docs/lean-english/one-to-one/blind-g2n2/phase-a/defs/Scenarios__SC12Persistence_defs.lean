-- EXCERPT of ControlStack/Scenarios/SC12Persistence.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC12

open ControlStack.Gate

/-- a live entity: id, registered session label, ghost true lineage, whether it is a scheduled job, registered -/
structure Ent where
  id : ℕ
  sess : ℕ
  origin : ℕ
  job : Bool
  reg : Bool
deriving DecidableEq, Repr

structure St where
  active : List ℕ
  ended : List ℕ
  live : List Ent
  /-- job firings: (job id, its true lineage, length of the ended-session log at that moment) -/
  fired : List (ℕ × ℕ × ℕ)
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | start (caller sess : ℕ)
  /-- `parent` creates `child` through the registry; `claim` is a session label the creator asks for -/
  | spawn (parent child : ℕ) (job : Bool) (claim : ℕ)
  /-- `parent` creates `child` outside the registry -/
  | bypass (parent child : ℕ) (job : Bool)
  | endSession (caller sess : ℕ)
  | fire (j : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  registryOnly : Bool
  lineage : Bool
  revokeLineage : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], [], [], false⟩

def entOf (s : St) (id : ℕ) : Option Ent := s.live.find? (fun e => e.id = id)

def step (admins : List ℕ) (C : Checks) (s : St) : Op → St
  | .start c sess =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ admins ∧ sess ∉ s.active ∧ sess ∉ s.ended ∧ entOf s sess = none then
      { s with active := s.active ++ [sess], live := s.live ++ [⟨sess, sess, sess, false, true⟩] }
    else s
  | .spawn p ch job claim =>
    if s.halted ∧ C.haltCheck then s
    else match entOf s p with
      | none => s
      | some e =>
        if entOf s ch = none then
          { s with live := s.live ++ [⟨ch, if C.lineage then e.sess else claim, e.origin, job, true⟩] }
        else s
  | .bypass p ch job =>
    if s.halted ∧ C.haltCheck then s
    else if C.registryOnly then s
    else match entOf s p with
      | none => s
      | some e => if entOf s ch = none then { s with live := s.live ++ [⟨ch, e.sess, e.origin, job, false⟩] } else s
  | .endSession c sess =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ admins then
      { s with ended := s.ended ++ [sess], active := s.active.filter (fun x => x ≠ sess),
               live := if C.revokeLineage then s.live.filter (fun e => ¬ (e.reg = true ∧ e.sess = sess))
                       else s.live.filter (fun e => ¬ (e.reg = true ∧ e.id = sess)) }
    else s
  | .fire j =>
    if s.halted ∧ C.haltCheck then s
    else match entOf s j with
      | none => s
      | some e => if e.job then { s with fired := s.fired ++ [(j, e.origin, s.ended.length)] } else s
  | .halt c =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ admins then
      { s with halted := true, ended := s.ended ++ s.active, active := [],
               live := s.live.filter (fun e => e.reg = false) }
    else s

def run (admins : List ℕ) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step admins C) s

def Good (s : St) : Prop := ∀ e ∈ s.live, e.reg = true ∧ e.origin ∈ s.active ∧ e.origin ∉ s.ended

/-- a firing whose lineage had not ended when it fired (the ended log cut at that moment) -/
def FireOk (s : St) (f : ℕ × ℕ × ℕ) : Prop := f.2.2 ≤ s.ended.length ∧ f.2.1 ∉ s.ended.take f.2.2

structure Inv (s : St) : Prop where
  ent : ∀ e ∈ s.live, e.reg = true ∧ e.sess = e.origin ∧ e.origin ∈ s.active
  disj : ∀ x ∈ s.active, x ∉ s.ended
  fired_ok : ∀ f ∈ s.fired, FireOk s f

def sys (admins : List ℕ) : System St Op (ℕ × ℕ × ℕ) where
  step := step admins full
  effects := St.fired

/-- the gate spec: every firing's lineage had not ended when it fired -/
def spec (admins : List ℕ) : Spec (sys admins) where
  Inv := Inv
  ok := FireOk
  step_inv := fun s o h => step_inv admins s o h
  log_prefix := fun s o => fired_prefix admins full s o
  inv_ok := fun _ h f hf => h.fired_ok f hf



end ControlStack.SC12

