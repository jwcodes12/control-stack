namespace PL_bg7n1_3
open ControlStack.SC27Chain


def FrozenBack : Prop :=
  (run E0 full init
    [.append 5, .anchor, .rewrite [7], .verify [7]]).accepted = [] ∧
  (run E0 full init
    [.append 5, .append 6, .anchor, .rewrite [6, 5], .verify [6, 5]]).accepted = []

def BackAt  : Prop :=
  (run E0 full init [.append 5, .anchor, .rewrite [7], .verify [7]]).accepted = [] ∧
  (run E0 full init [.append 5, .append 6, .anchor, .rewrite [6, 5], .verify [6, 5]]).accepted = []

def OrigAt  : Prop :=
  (run E0 full init [.append 5, .anchor, .rewrite [7], .verify [7]]).accepted = [] ∧
  (run E0 full init [.append 5, .append 6, .anchor, .rewrite [6, 5], .verify [6, 5]]).accepted = []

def Claim : Prop :=
  (FrozenBack ↔ (BackAt )) ∧
  ((BackAt  ↔ OrigAt ))

def Witness : Prop :=
  (run E0 full init [.append 5, .anchor, .rewrite [7], .verify [7]]).log = [7] ∧
  (run E0 full init [.append 5, .append 6, .anchor, .rewrite [6, 5], .verify [6, 5]]).log = [6, 5] ∧
  (run E0 full init [.append 5, .append 6, .anchor, .verify [5, 6]]).accepted = [[5, 6]] ∧
  BackAt

end PL_bg7n1_3
