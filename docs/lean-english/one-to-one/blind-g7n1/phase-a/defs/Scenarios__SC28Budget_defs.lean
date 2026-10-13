-- EXCERPT of ControlStack/Scenarios/SC28Budget.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC28

open ControlStack.Gate

structure St where
  /-- (lease id, budget) -/
  leases : List (ℕ × ℕ)
  /-- (worker, lease id), newest assignment first -/
  assign : List (ℕ × ℕ)
  revoked : List ℕ
  /-- the gate's durable counters: (lease id, charge) -/
  ledger : List (ℕ × ℕ)
  /-- the external effect log of actual consumption: (worker, lease id, units) -/
  usage : List (ℕ × ℕ × ℕ)
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | issue (caller lid budget : ℕ)
  | assignTo (caller worker lid : ℕ)
  /-- `parent` forks `child`; `newLid` is used only by the unsafe fresh-lease design -/
  | fork (caller parent child newLid : ℕ)
  | revoke (caller lid : ℕ)
  /-- worker `w` consumes `actual` units and reports `reported` -/
  | work (w actual reported : ℕ)
  /-- a crash/restart: volatile state is lost, durable counters are re-read (a no-op on the durable state) -/
  | restart
  /-- restore a stale snapshot of the counters (privileged storage rollback; excluded by `legal`) -/
  | rollback (n : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

/-- implementation checks; `full` is the deployed configuration -/
structure Checks where
  share : Bool
  meter : Bool
  global : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], [], [], [], false⟩

def budgetOf (s : St) (lid : ℕ) : Option ℕ := (s.leases.find? (fun e => e.1 = lid)).map Prod.snd

def leaseOf (s : St) (w : ℕ) : Option ℕ := (s.assign.find? (fun e => e.1 = w)).map Prod.snd

def spentL (s : St) (lid : ℕ) : ℕ := ((s.ledger.filter (fun e => e.1 = lid)).map Prod.snd).sum
def spentT (s : St) : ℕ := (s.ledger.map Prod.snd).sum
def usedL (s : St) (lid : ℕ) : ℕ := ((s.usage.filter (fun e => e.2.1 = lid)).map (fun e => e.2.2)).sum
def usedT (s : St) : ℕ := (s.usage.map (fun e => e.2.2)).sum

/-- the charge for one work step -/
def charge (C : Checks) (actual reported : ℕ) : ℕ := if C.meter then max actual 1 else reported

/-- the (leases, assignments) after `p` forks `ch`: with `share`, the child joins its parent's lease; without it, the
child gets a FRESH lease `nl` with a copy of the parent's budget (the unsafe design) -/
def forkUpd (C : Checks) (s : St) (p ch nl : ℕ) : List (ℕ × ℕ) × List (ℕ × ℕ) :=
  match leaseOf s p with
  | none => (s.leases, s.assign)
  | some lid =>
    if ch ∈ s.assign.map Prod.fst then (s.leases, s.assign)
    else if C.share then (s.leases, (ch, lid) :: s.assign)
    else if budgetOf s nl = none then (s.leases ++ [(nl, (budgetOf s lid).getD 0)], (ch, nl) :: s.assign)
    else (s.leases, s.assign)

def step (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) : Op → St
  | .issue c lid b =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ admins ∧ budgetOf s lid = none then { s with leases := s.leases ++ [(lid, b)] } else s
  | .assignTo c w lid =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ admins ∧ budgetOf s lid ≠ none then { s with assign := (w, lid) :: s.assign } else s
  | .fork _ p ch nl =>
    if s.halted ∧ C.haltCheck then s
    else { s with leases := (forkUpd C s p ch nl).1, assign := (forkUpd C s p ch nl).2 }
  | .revoke c lid => if c ∈ admins then { s with revoked := s.revoked ++ [lid] } else s
  | .work w a r =>
    if s.halted ∧ C.haltCheck then s
    else match leaseOf s w with
      | none => s
      | some lid =>
        match budgetOf s lid with
        | none => s
        | some b =>
          if lid ∉ s.revoked ∧ spentL s lid + charge C a r ≤ b ∧ (C.global → spentT s + charge C a r ≤ G) then
            { s with ledger := s.ledger ++ [(lid, charge C a r)], usage := s.usage ++ [(w, lid, a)] }
          else s
  | .restart => s
  | .rollback n => { s with ledger := s.ledger.take n }
  | .halt c => if c ∈ admins then { s with halted := true } else s

def run (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step admins G C) s

/-- anti-rollback premise: no storage rollback of the counters -/
def legal : Op → Prop
  | .rollback _ => False
  | _ => True



structure Inv (G : ℕ) (s : St) : Prop where
  tot : usedT s ≤ spentT s
  cap : spentT s ≤ G
  per : ∀ lid, usedL s lid ≤ spentL s lid
  budget : ∀ lid, spentL s lid ≤ (budgetOf s lid).getD 0
  count : s.usage.length ≤ spentT s

/-- the safety property: total actual usage within G, per-lease usage within its budget, at most G work steps -/
def Good (G : ℕ) (s : St) : Prop :=
  usedT s ≤ G ∧ (∀ lid, usedL s lid ≤ (budgetOf s lid).getD 0) ∧ s.usage.length ≤ G

/-- one usage entry is within its lease's budget -/
def EntryOk (s : St) (e : ℕ × ℕ × ℕ) : Prop := e.2.2 ≤ (budgetOf s e.2.1).getD 0

def sys (admins : List ℕ) (G : ℕ) : System St {o : Op // legal o} (ℕ × ℕ × ℕ) where
  step := fun s o => step admins G full s o.1
  effects := St.usage

def spec (admins : List ℕ) (G : ℕ) : Spec (sys admins G) where
  Inv := Inv G
  ok := EntryOk
  step_inv := fun s o h => step_inv admins G s o.1 o.2 h
  log_prefix := fun s o => usage_prefix admins G full s o.1
  inv_ok := fun _ h e he => h.good.entry e he



end ControlStack.SC28

