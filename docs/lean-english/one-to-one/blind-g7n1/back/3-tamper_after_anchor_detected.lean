namespace ControlStack.SC27Chain

def Back_tamper_after_anchor_detected : Prop :=
  (run E0 full init
    [.append 5, .anchor, .rewrite [7], .verify [7]]).accepted = [] ∧
  (run E0 full init
    [.append 5, .append 6, .anchor, .rewrite [6, 5], .verify [6, 5]]).accepted = []

end ControlStack.SC27Chain
