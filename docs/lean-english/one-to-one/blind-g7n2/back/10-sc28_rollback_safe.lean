import ControlStack.Core.AntiRollback

namespace ControlStack.AntiRollback

-- NOTE
-- The anchor, record-integrity, and protocol premises are represented by
-- runR with check = true, starting at rinit. Legal SC-28 writes are enforced
-- by the operation subtype. The conclusion concerns released effects and
-- the plain committed run, not the uncommitted store or physical consumption.
def Back_sc28_rollback_safe : Prop :=
  ∀ (admins : List ℕ) (G : ℕ)
    (ops : List (ROp {o : SC28.Op // SC28.legal o})),
    let system := SC28.sys admins G
    let s := runR system true (rinit system SC28.init) ops
    let plain := system.run SC28.init s.committed
    s.released = plain.usage ∧ SC28.Good G plain

end ControlStack.AntiRollback
