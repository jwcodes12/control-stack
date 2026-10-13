-- EXCERPT of ControlStack/Scenarios/SC05Signal.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC05

open ControlStack.Gate ControlStack.Covert ControlStack.CovertNoGo Finset

/-- executed actions; `act a` asks for action `a` (whatever signal led to the request) -/
inductive Op where
  | act (a : ℕ)
deriving DecidableEq, Repr

def step (forbidden : List ℕ) (gate : Bool) (s : List ℕ) : Op → List ℕ
  | .act a => if gate ∧ a ∈ forbidden then s else s ++ [a]

def sys (forbidden : List ℕ) : System (List ℕ) Op ℕ where
  step := step forbidden true
  effects := id

def spec (forbidden : List ℕ) : Spec (sys forbidden) where
  Inv := fun s => ∀ a ∈ s, a ∉ forbidden
  ok := fun _ a => a ∉ forbidden
  step_inv := by
    intro s o h
    cases o with
    | act a =>
      simp only [sys, step, true_and]
      split_ifs with ha
      · exact h
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact h x hx
        · simp at hx; subst hx; exact ha
  log_prefix := by
    intro s o
    cases o with
    | act a => simp only [sys, step, true_and]; split_ifs <;> simp
  inv_ok := fun _ h a ha => h a ha

end ControlStack.SC05

