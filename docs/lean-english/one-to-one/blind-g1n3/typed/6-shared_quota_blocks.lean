import ControlStack.Scenarios.SC07Liveness

namespace ControlStack.SC07Liveness

def Back_shared_quota_blocks : Prop :=
  (run E0 full init [Op.send 10 6, Op.send 10 4]).log =
      [⟨10, 6, 0⟩] ∧
  (run E0 full init [Op.send 10 6, Op.tick, Op.send 10 4]).log =
      [⟨10, 6, 0⟩, ⟨10, 4, 1⟩]

end ControlStack.SC07Liveness
