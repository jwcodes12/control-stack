import ControlStack.Scenarios.AuthInstancesB

namespace ControlStack.AuthInstances

open ControlStack.AuthenticatedLog

-- Good includes exact user confirmation for provenance-tainted sensitive
-- actions and no repeated recorded action-confirmation nonce.
def Back_sc23_safe_authenticated : Prop :=
  ∀ (P : SC23.Policy) (U : List ℕ),
    (∀ u ∈ U, u ∉ P.users) →
      ∀ (ops : List (ℕ × SC23.Op)),
        let s := authRun (SC23.step P SC23.full) claim23 SC23.init ops
        SC23.Good P s ∧
          ∀ cf ∈ s.confs,
            ∃ c : ℕ, c ∈ P.users ∧ c ∉ U ∧ c = cf.by_ ∧
              (c, SC23.Op.confirm c cf.n cf.tool cf.vals) ∈ ops

end ControlStack.AuthInstances
