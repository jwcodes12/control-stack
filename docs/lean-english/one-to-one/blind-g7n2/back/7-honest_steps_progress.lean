import ControlStack.Scenarios.SC28Liveness

namespace ControlStack.SC28Liveness

open ControlStack.SC28

def Back_honest_steps_progress : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St)
    (w lid b : ℕ) (units : List ℕ),
    s.halted = false →
    leaseOf s w = some lid →
    budgetOf s lid = some b →
    lid ∉ s.revoked →
    spentL s lid + charges units ≤ b →
    spentT s + charges units ≤ G →
    (run admins G full s (units.map (fun a => Op.work w a a))).usage =
      s.usage ++ units.map (fun a => (w, lid, a))

end ControlStack.SC28Liveness
