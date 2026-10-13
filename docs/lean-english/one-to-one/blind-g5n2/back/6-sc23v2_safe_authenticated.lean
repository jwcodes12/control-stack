import ControlStack.Scenarios.SC23IsolationV2

namespace ControlStack.SC23IsolationV2

open ControlStack.Authenticated ControlStack.Gate

-- The conclusion extracts an actual issued confirmation with the exact tool
-- and values. It asserts neither trace order nor single use of its nonce.
def Back_sc23v2_safe_authenticated : Prop :=
  ∀ (E : Env) (U : List ℕ),
    (∀ u ∈ U, u ∉ E.users) →
      ∀ (ops : List (ℕ × Op)),
        let s := (authed (raw E) claim).run init ops
        ∀ x ∈ s.executed, x.tool ∈ E.sensitive → x.tainted = true →
          ∃ (c n : ℕ), c ∈ E.users ∧ c ∉ U ∧
            (c, Op.confirm c n x.tool x.vals) ∈ ops

end ControlStack.SC23IsolationV2
