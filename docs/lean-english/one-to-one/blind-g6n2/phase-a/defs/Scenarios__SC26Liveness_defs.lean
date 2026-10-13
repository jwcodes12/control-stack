-- EXCERPT of ControlStack/Scenarios/SC26Liveness.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC26Liveness

open ControlStack.SC26



/-- `t` extends `s`: tables only grow, spending never decreases, halting is sticky -/
structure Mono (s t : St) : Prop where
  reqs : s.reqs <+: t.reqs
  appr : s.approvals <+: t.approvals
  res : s.reserved <+: t.reserved
  spent : s.spent ≤ t.spent
  net : s.net <+: t.net
  bank : s.bank <+: t.bank
  halt : s.halted = true → t.halted = true

namespace Concrete

open ControlStack.SC26Refinement

/-- concrete progress-relevant monotonicity: delivery rows persist (by id and payload), the wire and the bank's keys
only grow, halting is sticky -/
structure CMono (s t : CSt) : Prop where
  rows : ∀ d ∈ s.delivery, ∃ d' ∈ t.delivery, d'.id = d.id ∧ d'.tx = d.tx
  wire : s.wire <+: t.wire
  bank : ∀ x ∈ s.bank.map Prod.fst, x ∈ t.bank.map Prod.fst
  halt : s.halted = true → t.halted = true

/-- the ack invariant: an acknowledged row's key is in the bank -/
def AckInv (s : CSt) : Prop := ∀ d ∈ s.delivery, d.acked = true → d.id ∈ s.bank.map Prod.fst

/-- a gate (not halted) with one logged intent that is not on the wire -/
def loggedState : CSt := ⟨1, [⟨0, 1, wTx⟩], [(0, 2, wTx)], [0], 10, false, [⟨0, wTx, false⟩], none, [], []⟩

end Concrete

end ControlStack.SC26Liveness

