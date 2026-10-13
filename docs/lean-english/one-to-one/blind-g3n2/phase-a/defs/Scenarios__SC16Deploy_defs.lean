-- EXCERPT of ControlStack/Scenarios/SC16Deploy.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC16

open ControlStack.Gate

structure Roles where
  agents : List ℕ
  reviewers : List ℕ
  approvers : List ℕ
  admins : List ℕ

/-- a review of digest `d` by `reviewer`, who saw `content`, staged by `stager` -/
structure Review where
  d : ℕ
  reviewer : ℕ
  content : ℕ
  stager : ℕ
deriving DecidableEq, Repr

/-- a one-use approval: nonce, digest, target environment, the staging slot it names, approver -/
structure Appr where
  n : ℕ
  d : ℕ
  target : ℕ
  slot : ℕ
  approver : ℕ
deriving DecidableEq, Repr

/-- a deployment: the approval nonce consumed, the target, the content deployed -/
structure Dep where
  n : ℕ
  target : ℕ
  content : ℕ
deriving DecidableEq, Repr

structure St where
  /-- append-only content store: (content, stager) -/
  cas : List (ℕ × ℕ)
  /-- mutable staging slots, newest write first: (slot, content) -/
  slots : List (ℕ × ℕ)
  reviews : List Review
  approvals : List Appr
  used : List ℕ
  deployed : List Dep
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | stage (caller content : ℕ)
  | writeSlot (caller slot content : ℕ)
  | review (caller d : ℕ)
  | approve (caller n d target slot : ℕ)
  /-- deploy approval `n` to `target` with `content` supplied at deploy time -/
  | deploy (caller n target content : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

/-- implementation checks; `full` is the deployed configuration. `verify = false` is the TOCTOU design: the hash is
checked on the named slot at approval time and the slot is re-read at deploy time without a check. -/
structure Checks where
  distinct : Bool
  target : Bool
  nonce : Bool
  verify : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true, true⟩

def init : St := ⟨[], [], [], [], [], [], false⟩

def casLookup (h : ℕ → ℕ) (s : St) (d : ℕ) : Option (ℕ × ℕ) := s.cas.find? (fun e => h e.1 = d)

def slotContent (s : St) (slot : ℕ) : Option ℕ := (s.slots.find? (fun e => e.1 = slot)).map Prod.snd

def apprOf (s : St) (n : ℕ) : Option Appr := s.approvals.find? (fun a => a.n = n)

def doDeploy (s : St) (n t x : ℕ) : St := { s with deployed := s.deployed ++ [⟨n, t, x⟩], used := s.used ++ [n] }

def step (R : Roles) (h : ℕ → ℕ) (C : Checks) (s : St) : Op → St
  | .stage c x =>
    if s.halted ∧ C.haltCheck then s else if c ∈ R.agents then { s with cas := s.cas ++ [(x, c)] } else s
  | .writeSlot c slot x =>
    if s.halted ∧ C.haltCheck then s else if c ∈ R.agents then { s with slots := (slot, x) :: s.slots } else s
  | .review c d =>
    if s.halted ∧ C.haltCheck then s
    else match casLookup h s d with
      | none => s
      | some e =>
        if c ∈ R.reviewers ∧ (C.distinct → c ≠ e.2) then { s with reviews := s.reviews ++ [⟨d, c, e.1, e.2⟩] }
        else s
  | .approve c n d t slot =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ R.approvers ∧ (C.verify ∨ (slotContent s slot).map h = some d) then
      { s with approvals := s.approvals ++ [⟨n, d, t, slot, c⟩] }
    else s
  | .deploy _ n t x =>
    if s.halted ∧ C.haltCheck then s
    else match apprOf s n with
      | none => s
      | some ap =>
        if (∃ rv ∈ s.reviews, rv.d = ap.d) ∧ (C.nonce → n ∉ s.used) ∧ (C.target → t = ap.target) then
          if C.verify then (if h x = ap.d then doDeploy s n t x else s)
          else match slotContent s ap.slot with
            | none => s
            | some y => doDeploy s n t y
        else s
  | .halt c => if c ∈ R.admins then { s with halted := true } else s

def run (R : Roles) (h : ℕ → ℕ) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step R h C) s

/-- a review that recorded what the reviewer actually saw, by a reviewer who did not stage it -/
def ReviewOk (R : Roles) (h : ℕ → ℕ) (rv : Review) : Prop :=
  h rv.content = rv.d ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager

/-- a deployment backed by an approval for exactly its target and digest, whose digest was reviewed -/
def DepOk (R : Roles) (h : ℕ → ℕ) (s : St) (e : Dep) : Prop :=
  ∃ ap ∈ s.approvals, ap.n = e.n ∧ ap.target = e.target ∧ ap.approver ∈ R.approvers ∧ h e.content = ap.d ∧
    ∃ rv ∈ s.reviews, rv.d = ap.d ∧ ReviewOk R h rv

structure Inv (R : Roles) (h : ℕ → ℕ) (s : St) : Prop where
  rev_ok : ∀ rv ∈ s.reviews, ReviewOk R h rv
  appr_ok : ∀ ap ∈ s.approvals, ap.approver ∈ R.approvers
  dep_ok : ∀ e ∈ s.deployed, e.n ∈ s.used ∧
    ∃ ap ∈ s.approvals, ap.n = e.n ∧ ap.target = e.target ∧ h e.content = ap.d ∧ ∃ rv ∈ s.reviews, rv.d = ap.d
  dep_nodup : (s.deployed.map Dep.n).Nodup

def Good (R : Roles) (h : ℕ → ℕ) (s : St) : Prop :=
  (∀ e ∈ s.deployed, DepOk R h s e) ∧ (s.deployed.map Dep.n).Nodup

def sys (R : Roles) (h : ℕ → ℕ) : System St Op Dep where
  step := step R h full
  effects := St.deployed

def spec (R : Roles) (h : ℕ → ℕ) : Spec (sys R h) where
  Inv := Inv R h
  ok := DepOk R h
  step_inv := fun s o hi => step_inv R h s o hi
  log_prefix := fun s o => deployed_prefix R h full s o
  inv_ok := fun _ hi e he => hi.good.1 e he



def R0 : Roles := ⟨[1], [2], [3], [4]⟩

def R1 : Roles := ⟨[1], [1, 2], [3], [4]⟩

end ControlStack.SC16

