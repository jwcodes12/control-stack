-- EXCERPT of ControlStack/Scenarios/SC16Refinement.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC16Refinement

open ControlStack.SC16

/-- a signed review row: digest, target, reviewer, content seen, its stager -/
structure RRow where
  d : ℕ
  target : ℕ
  reviewer : ℕ
  content : ℕ
  stager : ℕ
deriving DecidableEq, Repr

/-- a signed approval row: nonce, digest, target, tag, approver -/
structure ARow where
  n : ℕ
  d : ℕ
  target : ℕ
  tag : ℕ
  approver : ℕ
deriving DecidableEq, Repr

/-- a deploy record: nonce, target, content deployed, approved digest -/
structure DRow where
  n : ℕ
  target : ℕ
  content : ℕ
  d : ℕ
deriving DecidableEq, Repr

structure CSt where
  cas : List (ℕ × ℕ)
  /-- tag ↦ digest, newest first -/
  tags : List (ℕ × ℕ)
  revLog : List RRow
  apprLog : List ARow
  used : List ℕ
  depLog : List DRow
  halted : Bool
deriving DecidableEq, Repr

inductive COp where
  | put (caller content : ℕ)
  | tagSet (caller tag d : ℕ)
  | review (caller d target : ℕ)
  | approve (caller n d target tag : ℕ)
  | deploy (caller n target : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

def cinit : CSt := ⟨[], [], [], [], [], [], false⟩

def toRev (r : RRow) : Review := ⟨r.d, r.reviewer, r.content, r.stager⟩
def toAppr (a : ARow) : Appr := ⟨a.n, a.d, a.target, a.tag, a.approver⟩
def toDep (e : DRow) : Dep := ⟨e.n, e.target, e.content⟩

def α (s : CSt) : St :=
  ⟨s.cas, [], s.revLog.map toRev, s.apprLog.map toAppr, s.used, s.depLog.map toDep, s.halted⟩

def ccas (h : ℕ → ℕ) (s : CSt) (d : ℕ) : Option (ℕ × ℕ) := s.cas.find? (fun e => h e.1 = d)
def capprOf (s : CSt) (n : ℕ) : Option ARow := s.apprLog.find? (fun a => a.n = n)
def tagOf (s : CSt) (tag : ℕ) : Option ℕ := (s.tags.find? (fun e => e.1 = tag)).map Prod.snd

/-- the content admission fetches: by the approved digest (deployed), or via the mutable tag (`byTag`) -/
def fetch (h : ℕ → ℕ) (byTag : Bool) (s : CSt) (ap : ARow) : Option ℕ :=
  if byTag then (tagOf s ap.tag).bind (fun d => (ccas h s d).map Prod.fst) else (ccas h s ap.d).map Prod.fst

/-- the admission controller's decision: the approval and the content to deploy, if every check passes -/
def depRes (h : ℕ → ℕ) (byTag : Bool) (s : CSt) (n t : ℕ) : Option (ARow × ℕ) :=
  if s.halted then none
  else match capprOf s n with
    | none => none
    | some ap =>
      if n ∉ s.used ∧ t = ap.target ∧ (∃ r ∈ s.revLog, r.d = ap.d ∧ r.target = ap.target) then
        (fetch h byTag s ap).bind (fun x => if byTag ∨ h x = ap.d then some (ap, x) else none)
      else none

def putOk (R : Roles) (h : ℕ → ℕ) (s : CSt) (c x : ℕ) : Prop := s.halted = false ∧ c ∈ R.agents ∧ ccas h s (h x) = none

def apprOk (R : Roles) (s : CSt) (c n d t : ℕ) : Prop :=
  s.halted = false ∧ c ∈ R.approvers ∧ capprOf s n = none ∧ ∃ r ∈ s.revLog, r.d = d ∧ r.target = t

def stepC (R : Roles) (h : ℕ → ℕ) (byTag : Bool) (s : CSt) : COp → CSt
  | .put c x => if putOk R h s c x then { s with cas := s.cas ++ [(x, c)] } else s
  | .tagSet _ tag d => if s.halted then s else { s with tags := (tag, d) :: s.tags }
  | .review c d t =>
    if s.halted then s
    else match ccas h s d with
      | none => s
      | some e => if c ∈ R.reviewers ∧ c ≠ e.2 then { s with revLog := s.revLog ++ [⟨d, t, c, e.1, e.2⟩] } else s
  | .approve c n d t tag => if apprOk R s c n d t then { s with apprLog := s.apprLog ++ [⟨n, d, t, tag, c⟩] } else s
  | .deploy _ n t =>
    match depRes h byTag s n t with
    | none => s
    | some (ap, x) => { s with depLog := s.depLog ++ [⟨n, t, x, ap.d⟩], used := s.used ++ [n] }
  | .halt c => if c ∈ R.admins then { s with halted := true } else s

def runC (R : Roles) (h : ℕ → ℕ) (byTag : Bool) (s : CSt) (ops : List COp) : CSt := ops.foldl (stepC R h byTag) s

/-- the model operations matching one concrete step (deployed admission) -/
def opsOf (R : Roles) (h : ℕ → ℕ) (s : CSt) : COp → List Op
  | .put c x => if putOk R h s c x then [.stage c x] else []
  | .tagSet _ _ _ => []
  | .review c d _ => [.review c d]
  | .approve c n d t tag => if apprOk R s c n d t then [.approve c n d t tag] else []
  | .deploy c n t =>
    match depRes h false s n t with
    | none => []
    | some (_, x) => [.deploy c n t x]
  | .halt c => [.halt c]



def absTrace (R : Roles) (h : ℕ → ℕ) : CSt → List COp → List Op
  | _, [] => []
  | s, o :: ops => opsOf R h s o ++ absTrace R h (stepC R h false s o) ops

/-- the attack: stage 7 and tag it, get 7 reviewed and approved (approval names tag 0), stage 666 and re-point tag 0
to it, then request the deploy -/
def tagTrace : List COp :=
  [.put 1 7, .tagSet 1 0 7, .review 2 7 5, .approve 3 9 7 5 0, .put 1 666, .tagSet 1 0 666, .deploy 1 9 5]

end ControlStack.SC16Refinement

