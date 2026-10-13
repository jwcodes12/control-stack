-- EXCERPT of ControlStack/Scenarios/SC08Exec.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC08

open ControlStack.Gate

/-- trusted configuration -/
structure Env where
  h : ℕ → ℕ
  writable : ℕ → Bool
  noexecMount : ℕ → Bool
  allow : List ℕ
  interp : List ℕ
  scripts : List ℕ
  pathAllow : List ℕ
  admins : List ℕ

structure St where
  /-- (path, content), newest write first -/
  files : List (ℕ × ℕ)
  /-- runs: (program content, script content) -/
  ran : List (ℕ × Option ℕ)
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | write (path content : ℕ)
  | exec (path : ℕ) (script : Option ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  byDigest : Bool
  noexec : Bool
  scriptCheck : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def fileAt (s : St) (p : ℕ) : Option ℕ := (s.files.find? (fun e => e.1 = p)).map Prod.snd

/-- the exec decision on the CURRENT contents: the run it produces, or none if refused -/
def execResult (E : Env) (C : Checks) (s : St) (path : ℕ) (script : Option ℕ) : Option (ℕ × Option ℕ) :=
  match fileAt s path with
  | none => none
  | some c =>
    if (C.noexec = true → E.noexecMount path = false) ∧ (if C.byDigest then E.h c ∈ E.allow else path ∈ E.pathAllow)
    then
      if E.h c ∈ E.interp then
        match script with
        | none => if C.scriptCheck then none else some (c, none)
        | some sp =>
          match fileAt s sp with
          | none => none
          | some sc => if C.scriptCheck = true → E.h sc ∈ E.scripts then some (c, some sc) else none
      else some (c, none)
    else none

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .write p x =>
    if s.halted ∧ C.haltCheck then s else if E.writable p then { s with files := (p, x) :: s.files } else s
  | .exec p sc =>
    if s.halted ∧ C.haltCheck then s
    else match execResult E C s p sc with
      | none => s
      | some r => { s with ran := s.ran ++ [r] }
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

/-- an allowlisted program, and for an interpreter an allowlisted script -/
def RunOk (E : Env) (r : ℕ × Option ℕ) : Prop :=
  E.h r.1 ∈ E.allow ∧ (E.h r.1 ∈ E.interp → ∃ sc, r.2 = some sc ∧ E.h sc ∈ E.scripts)

def Good (E : Env) (s : St) : Prop := ∀ r ∈ s.ran, RunOk E r

/-- configurations that check digests of programs and scripts -/
structure Sound (C : Checks) : Prop where
  byDigest : C.byDigest = true
  scriptCheck : C.scriptCheck = true

def sys (E : Env) : System St Op (ℕ × Option ℕ) where
  step := step E full
  effects := St.ran

def spec (E : Env) : Spec (sys E) where
  Inv := Good E
  ok := fun _ r => RunOk E r
  step_inv := fun s o h => step_good E sound_full s o h
  log_prefix := fun s o => ran_prefix E full s o
  inv_ok := fun _ h r hr => h r hr



def E0 : Env where
  h := id
  writable := fun p => p = 2 ∨ p = 3
  noexecMount := fun p => p = 2
  allow := [10, 20]
  interp := [20]
  scripts := [30]
  pathAllow := [1, 2, 3, 4]
  admins := [9]

def s0 : St := ⟨[(1, 10), (4, 20), (5, 30)], [], false⟩

end ControlStack.SC08

