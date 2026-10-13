import ControlStack.Scenarios.SC26Authenticated

namespace ControlStack.SC26Authenticated

open ControlStack.SC26 ControlStack.Authenticated ControlStack.Gate

-- forged fixes all five issuers to 1; R0 fixes the roles to 1, 2, 3, 9.
def Back_forged_approval_pays_without_auth : Prop :=
  (0, tx1) ∈ ((raw R0 20).run init (forged.map Prod.snd)).bank ∧
  (∀ io ∈ forged, io.1 ∉ R0.approvers) ∧
  ((authed (raw R0 20) claim).run init forged).bank = []

end ControlStack.SC26Authenticated
