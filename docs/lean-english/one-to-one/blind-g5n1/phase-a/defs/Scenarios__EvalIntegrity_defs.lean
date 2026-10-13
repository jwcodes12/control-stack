-- EXCERPT of ControlStack/Scenarios/EvalIntegrity.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.EvalIntegrity

open ControlStack.Gate ControlStack.AuditBudget Finset



structure Env where
  tasks : List ℕ
  truth : ℕ → ℕ
  frozen : ℕ
  admins : List ℕ

/-- a reported result: (task, value, evaluator digest) -/
abbrev Res := ℕ × ℕ × ℕ

structure St where
  /-- newest first -/
  results : List Res
  reexecuted : List ℕ
  flags : List ℕ
  /-- published records: (results snapshot, tasks re-executed by then) -/
  published : List (List Res × List ℕ)
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | report (t r d : ℕ)
  | reexec (t : ℕ)
  | publish
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  appendOnly : Bool
  complete : Bool
  frozenEval : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], [], [], false⟩

def resultOf (s : St) (t : ℕ) : Option Res := s.results.find? (fun e => e.1 = t)

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .report t r d =>
    if s.halted ∧ C.haltCheck then s
    else if C.appendOnly = true → resultOf s t = none then { s with results := (t, r, d) :: s.results } else s
  | .reexec t =>
    if s.halted ∧ C.haltCheck then s
    else match resultOf s t with
      | none => s
      | some e =>
        { s with reexecuted := s.reexecuted ++ [t],
                 flags := if e.2.1 = E.truth t then s.flags else s.flags ++ [t] }
  | .publish =>
    if s.halted ∧ C.haltCheck then s
    else if (C.complete = true → ∀ t ∈ E.tasks, resultOf s t ≠ none) ∧
        (C.frozenEval = true → ∀ e ∈ s.results, e.2.2 = E.frozen) ∧ s.flags = [] then
      { s with published := s.published ++ [(s.results, s.reexecuted)] }
    else s
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

/-- a published record: complete, frozen evaluator only, and true values for every re-executed task -/
def PubOk (E : Env) (p : List Res × List ℕ) : Prop :=
  (∀ t ∈ E.tasks, ∃ e ∈ p.1, e.1 = t) ∧ (∀ e ∈ p.1, e.2.2 = E.frozen) ∧
    (∀ e ∈ p.1, e.1 ∈ p.2 → e.2.1 = E.truth e.1)

structure Inv (E : Env) (s : St) : Prop where
  nodup : (s.results.map Prod.fst).Nodup
  checked : ∀ t ∈ s.reexecuted, t ∈ s.flags ∨ ∀ e ∈ s.results, e.1 = t → e.2.1 = E.truth t
  rx_has : ∀ t ∈ s.reexecuted, ∃ e ∈ s.results, e.1 = t
  pub : ∀ p ∈ s.published, PubOk E p

def sys (E : Env) : System St Op (List Res × List ℕ) where
  step := step E full
  effects := St.published

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := fun _ p => PubOk E p
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => published_prefix E full s o
  inv_ok := fun _ h p hp => h.pub p hp



def E0 : Env := ⟨[0, 1], fun t => if t = 1 then 0 else 1, 5, [9]⟩

variable {N : ℕ}

/-- the corrupted results: reported value differs from the true (re-executed) value -/
def corrupt (rep truth : Fin N → ℕ) : Finset (Fin N) := univ.filter (fun i => rep i ≠ truth i)

end ControlStack.EvalIntegrity

