import ControlStack.Scenarios.SC18Liveness

namespace ControlStack.SC18Liveness

def Back_silent_ticks_halt : Prop :=
  ∀ (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (n : ℕ),
    (s.halted = false → s.clock ≤ s.lastAck + T) →
    s.lastAck + T < s.clock + n →
    (ControlStack.SC18.run admins trusted T ControlStack.SC18.full s
      (List.replicate n ControlStack.SC18.Op.tick)).halted = true

end ControlStack.SC18Liveness
