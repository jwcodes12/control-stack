import ControlStack.Scenarios.SC12Persistence

namespace ControlStack.SC12

def Back_no_fire_after_end : Prop :=
  ∀ (admins : List ℕ) (s : St) (sess : ℕ) (ops : List Op),
    Inv s → sess ∈ s.ended →
      ((run admins full s ops).fired.filter (fun f => decide (f.2.1 = sess))) =
        (s.fired.filter (fun f => decide (f.2.1 = sess)))

end ControlStack.SC12
