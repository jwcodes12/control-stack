import ControlStack.Scenarios.SC16Disjoint

namespace ControlStack.SC16Disjoint

open ControlStack.SC16

-- NOTE
-- AMBIGUOUS: The English calls this one concrete trace but omits the approval
-- nonce, approval slot, and deploy caller. Best effort uses nonce 0, slot 0,
-- and deploy caller 1. Approver 3 is the only approver in Rov; the review and
-- approval digest is 7 under the specified identity hash.
def Back_overlap_reviewer_is_agent : Prop :=
  let ops : List Op :=
    [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]
  let s := run Rov (fun x => x) full init ops
  (∃ e ∈ s.deployed, e.content = 7 ∧ e.target = 5) ∧
  s.reviews ≠ [] ∧ (∀ rv ∈ s.reviews, rv.reviewer ∈ Rov.agents)

end ControlStack.SC16Disjoint
