namespace PL_bg1a_5
open ControlStack.SC05

def Back_forbidden_never_executes : Prop :=
  ∀ (forbidden : List ℕ) (ops : List Op),
    ∀ a ∈ ControlStack.Gate.System.run (sys forbidden) [] ops,
      a ∉ forbidden


def BackAt (forbidden : List ℕ) (ops : List Op) : Prop :=
  ∀ a ∈ ControlStack.Gate.System.run (sys forbidden) [] ops, a ∉ forbidden
def OrigAt (forbidden : List ℕ) (ops : List Op) : Prop :=
  ∀ a ∈ ControlStack.Gate.System.run (sys forbidden) [] ops, a ∉ forbidden

def Claim : Prop :=
  (Back_forbidden_never_executes = (∀ (forbidden : List ℕ) (ops : List Op), BackAt forbidden ops)) ∧
  (∀ (forbidden : List ℕ) (ops : List Op), BackAt forbidden ops ↔ OrigAt forbidden ops)

def Witness : Prop :=
  ControlStack.Gate.System.run (sys [7]) [] [.act 3, .act 7] = [3] ∧
  ([Op.act 7].foldl (step [7] false) []) = [7]
end PL_bg1a_5
