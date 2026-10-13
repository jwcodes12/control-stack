import ControlStack.Scenarios.SC28Liveness

namespace ControlStack.SC28Liveness

open ControlStack.SC28

-- NOTE
-- AMBIGUOUS: "would be admissible" can mean all acceptance conditions,
-- including not halted and not revoked, or just the assignment, lease, and
-- capacity hypotheses explicitly listed in the specification. This uses
-- the explicitly listed hypotheses, without adding initial halt/revoke tests.
-- The reported cost is universally quantified: full ignores it, and the
-- same actual/reported pair is used before and after the interleaving.
def Back_progress_interleaved : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St)
    (w lid b a reported : ℕ) (p : List Op),
    leaseOf s w = some lid →
    budgetOf s lid = some b →
    spentL s lid + charge full a reported ≤ b →
    spentT s + charge full a reported ≤ G →
    let t := run admins G full s p
    (step admins G full t (.work w a reported)).usage =
        t.usage ++ [(w, lid, a)] ∨
      t.halted = true ∨
      lid ∈ t.revoked ∨
      leaseOf t w ≠ some lid ∨
      spentL s lid < spentL t lid ∨
      spentT s < spentT t

end ControlStack.SC28Liveness
