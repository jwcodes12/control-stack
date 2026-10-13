-- EXCERPT of ControlStack/Scenarios/SC15Review.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC15

open ControlStack.Gate

structure Env where
  reviewers : List ℕ
  security : List ℕ
  admins : List ℕ
  sensitive : List ℕ
  testsPass : ℕ → Bool

structure Change where
  id : ℕ
  author : ℕ
  content : ℕ
  paths : List ℕ
  declared : List ℕ
deriving DecidableEq, Repr

/-- a review: change id, reviewer, author, content reviewed, security review? -/
structure Rev where
  id : ℕ
  reviewer : ℕ
  author : ℕ
  content : ℕ
  sec : Bool
deriving DecidableEq, Repr

structure St where
  /-- newest version first -/
  changes : List Change
  reviews : List Rev
  /-- trusted CI results: (change id, content, pass) -/
  ci : List (ℕ × ℕ × Bool)
  merged : List Change
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | propose (caller id content : ℕ) (paths declared : List ℕ)
  | amend (caller id content : ℕ) (paths : List ℕ)
  | review (caller id : ℕ) (sec : Bool)
  | runCI (id : ℕ)
  | merge (id : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  exact : Bool
  trustedPaths : Bool
  ciExact : Bool
  distinct : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true, true⟩

def init : St := ⟨[], [], [], [], false⟩

def chOf (s : St) (id : ℕ) : Option Change := s.changes.find? (fun c => c.id = id)

def touchesSensitive (E : Env) (C : Checks) (c : Change) : Bool :=
  (if C.trustedPaths then c.paths else c.declared).any (fun p => p ∈ E.sensitive)

/-- the merge gate's review test for change `c` (`sec`: security review) -/
abbrev Reviewed (C : Checks) (s : St) (c : Change) (sec : Bool) : Prop :=
  ∃ r ∈ s.reviews, r.id = c.id ∧ r.author = c.author ∧ (sec = true → r.sec = true) ∧
    (C.exact = true → r.content = c.content)

/-- the role a review needs: security reviewer for a security review, reviewer otherwise -/
def roleOk (E : Env) (sec : Bool) (r : ℕ) : Bool := if sec then decide (r ∈ E.security) else decide (r ∈ E.reviewers)

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .propose a id x ps ds =>
    if s.halted ∧ C.haltCheck then s
    else if chOf s id = none then { s with changes := ⟨id, a, x, ps, ds⟩ :: s.changes } else s
  | .amend a id x ps =>
    if s.halted ∧ C.haltCheck then s
    else match chOf s id with
      | none => s
      | some c => if c.author = a then { s with changes := { c with content := x, paths := ps } :: s.changes } else s
  | .review r id sec =>
    if s.halted ∧ C.haltCheck then s
    else match chOf s id with
      | none => s
      | some c =>
        if roleOk E sec r = true ∧ (C.distinct = true → r ≠ c.author) then
          { s with reviews := s.reviews ++ [⟨id, r, c.author, c.content, sec⟩] }
        else s
  | .runCI id =>
    if s.halted ∧ C.haltCheck then s
    else match chOf s id with
      | none => s
      | some c => { s with ci := s.ci ++ [(id, c.content, E.testsPass c.content)] }
  | .merge id =>
    if s.halted ∧ C.haltCheck then s
    else match chOf s id with
      | none => s
      | some c =>
        if Reviewed C s c false ∧ (touchesSensitive E C c = true → Reviewed C s c true) ∧
            (∃ x ∈ s.ci, x.1 = id ∧ (C.ciExact = true → x.2.1 = c.content) ∧ x.2.2 = true) then
          { s with merged := s.merged ++ [c] }
        else s
  | .halt a => if a ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

/-- an exact-content review of `c` by a non-author holding the role it reviewed in (a security review when `sec`) -/
def RevOk (E : Env) (s : St) (c : Change) (sec : Bool) : Prop :=
  ∃ r ∈ s.reviews, r.id = c.id ∧ r.content = c.content ∧ r.reviewer ≠ c.author ∧ (sec = true → r.sec = true) ∧
    roleOk E r.sec r.reviewer = true

def MergeOk (E : Env) (s : St) (c : Change) : Prop :=
  RevOk E s c false ∧ ((c.paths.any (fun p => p ∈ E.sensitive)) = true → RevOk E s c true) ∧
    ∃ x ∈ s.ci, x.1 = c.id ∧ x.2.1 = c.content ∧ x.2.2 = true

structure Inv (E : Env) (s : St) : Prop where
  revs : ∀ r ∈ s.reviews, r.reviewer ≠ r.author ∧ roleOk E r.sec r.reviewer = true
  merged : ∀ c ∈ s.merged, MergeOk E s c

def sys (E : Env) : System St Op Change where
  step := step E full
  effects := St.merged

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := MergeOk E
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => merged_prefix E full s o
  inv_ok := fun _ h c hc => h.merged c hc



def E0 : Env := ⟨[2], [3], [9], [100], fun x => x != 13⟩

end ControlStack.SC15

