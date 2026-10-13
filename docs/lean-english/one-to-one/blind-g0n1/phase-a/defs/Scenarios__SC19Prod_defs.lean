-- EXCERPT of ControlStack/Scenarios/SC19Prod.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC19

open ControlStack.Gate

structure Env where
  approvers : List ℕ
  verifiers : List ℕ
  admins : List ℕ
  R : ℕ

structure Obj where
  t : ℕ
  ver : ℕ
  size : ℕ
deriving DecidableEq, Repr

structure Pend where
  id : ℕ
  author : ℕ
  t : ℕ
  count : ℕ
deriving DecidableEq, Repr

/-- a committed destructive operation: id, author, target, version destroyed, objects actually affected, snapshot -/
structure Destroy where
  id : ℕ
  author : ℕ
  t : ℕ
  ver : ℕ
  actual : ℕ
  snap : ℕ
deriving DecidableEq, Repr

structure St where
  /-- newest first -/
  objs : List Obj
  snaps : List Obj
  verified : List ℕ
  pending : List Pend
  /-- (operation id, approver, author) -/
  approvals : List (ℕ × ℕ × ℕ)
  destroyed : List Destroy
  done : List ℕ
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | write (t n : ℕ)
  | snapshot (t : ℕ)
  | verify (caller i : ℕ)
  | prepare (caller id t : ℕ)
  | approve (caller id : ℕ)
  | commit (id i : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  fresh : Bool
  verified : Bool
  atomicCount : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], [], [], [], [], [], false⟩

def objOf (s : St) (t : ℕ) : Obj := (s.objs.find? (fun o => o.t = t)).getD ⟨t, 0, 0⟩

def pendOf (s : St) (id : ℕ) : Option Pend := s.pending.find? (fun p => p.id = id)

/-- objects affected, as the gate counts them: atomically at commit, or (unsafe) as recorded at prepare -/
def countOf (C : Checks) (s : St) (p : Pend) : ℕ := if C.atomicCount then (objOf s p.t).size else p.count

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .write t n =>
    if s.halted ∧ C.haltCheck then s
    else { s with objs := ⟨t, (objOf s t).ver + 1, (objOf s t).size + n⟩ :: s.objs }
  | .snapshot t => if s.halted ∧ C.haltCheck then s else { s with snaps := s.snaps ++ [objOf s t] }
  | .verify c i =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ E.verifiers ∧ i < s.snaps.length then { s with verified := s.verified ++ [i] } else s
  | .prepare c id t =>
    if s.halted ∧ C.haltCheck then s
    else if pendOf s id = none then { s with pending := s.pending ++ [⟨id, c, t, (objOf s t).size⟩] } else s
  | .approve c id =>
    if s.halted ∧ C.haltCheck then s
    else match pendOf s id with
      | none => s
      | some p => if c ∈ E.approvers ∧ c ≠ p.author then { s with approvals := s.approvals ++ [(id, c, p.author)] }
                  else s
  | .commit id i =>
    if s.halted ∧ C.haltCheck then s
    else match pendOf s id with
      | none => s
      | some p =>
        match s.snaps[i]? with
        | none => s
        | some sn =>
          if id ∉ s.done ∧ (∃ a ∈ s.approvals, a.1 = id ∧ a.2.2 = p.author) ∧ sn.t = p.t ∧
              (C.verified = true → i ∈ s.verified) ∧ (C.fresh = true → sn.ver = (objOf s p.t).ver) ∧
              countOf C s p ≤ E.R then
            { s with destroyed := s.destroyed ++ [⟨id, p.author, p.t, (objOf s p.t).ver, (objOf s p.t).size, i⟩],
                     done := s.done ++ [id],
                     objs := ⟨p.t, (objOf s p.t).ver + 1, 0⟩ :: s.objs }
          else s
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

def DestroyOk (E : Env) (s : St) (d : Destroy) : Prop :=
  d.actual ≤ E.R ∧ (∃ sn, s.snaps[d.snap]? = some sn ∧ sn.t = d.t ∧ sn.ver = d.ver) ∧ d.snap ∈ s.verified ∧
    ∃ a ∈ s.approvals, a.1 = d.id ∧ a.2.1 ∈ E.approvers ∧ a.2.1 ≠ d.author

def Good (E : Env) (s : St) : Prop := (∀ d ∈ s.destroyed, DestroyOk E s d) ∧ (s.destroyed.map Destroy.id).Nodup

structure Inv (E : Env) (s : St) : Prop where
  appr : ∀ a ∈ s.approvals, a.2.1 ∈ E.approvers ∧ a.2.1 ≠ a.2.2
  dest : ∀ d ∈ s.destroyed, d.actual ≤ E.R ∧ (∃ sn, s.snaps[d.snap]? = some sn ∧ sn.t = d.t ∧ sn.ver = d.ver) ∧
    d.snap ∈ s.verified ∧ ∃ a ∈ s.approvals, a.1 = d.id ∧ a.2.2 = d.author
  done_ok : ∀ d ∈ s.destroyed, d.id ∈ s.done
  nodup : (s.destroyed.map Destroy.id).Nodup

def sys (E : Env) : System St Op Destroy where
  step := step E full
  effects := St.destroyed

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := DestroyOk E
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => destroyed_prefix E full s o
  inv_ok := fun _ h d hd => h.good.1 d hd



def E0 : Env := ⟨[2], [3], [9], 10⟩

end ControlStack.SC19

