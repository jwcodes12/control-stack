-- EXCERPT of ControlStack/Core/AuthenticatedAdv.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.AuthenticatedAdv

open ControlStack.Gate ControlStack.Authenticated

/-- order-preserving interleaving of two lists -/
inductive Shuffle {α : Type} : List α → List α → List α → Prop where
  | nil : Shuffle [] [] []
  | left (a : α) {l r m : List α} : Shuffle l r m → Shuffle (a :: l) r (a :: m)
  | right (a : α) {l r m : List α} : Shuffle l r m → Shuffle l (a :: r) (a :: m)

/-- **The adversary class**: the trace interleaves the honest script with an adversary script issued only from `U` -/
def AdvTrace {Op : Type} (U : List ℕ) (hon ops : List (ℕ × Op)) : Prop :=
  ∃ adv : List (ℕ × Op), (∀ io ∈ adv, io.1 ∈ U) ∧ Shuffle hon adv ops

open ControlStack.SC26 ControlStack.SC26Authenticated

/-- the honest approver's script -/
def honScript : List (ℕ × SC26.Op) := [(2, .approve 2 0 tx1)]

/-- the adversary's script: request, execute, deliver, arrive, all issued by agent 1 -/
def advScript : List (ℕ × SC26.Op) := [(1, .request 1 tx1), (1, .execute 1 0), (1, .deliver 0), (1, .arrive 0)]

def honestTrace : List (ℕ × SC26.Op) :=
  [(1, .request 1 tx1), (2, .approve 2 0 tx1), (1, .execute 1 0), (1, .deliver 0), (1, .arrive 0)]

end ControlStack.AuthenticatedAdv

