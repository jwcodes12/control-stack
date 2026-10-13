import ControlStack.Scenarios.EvalIntegrity

namespace ControlStack.EvalIntegrity

open ControlStack.AuditBudget

def Back_observable_sample_nogo : Prop :=
  ∀ (N B k : ℕ) (S : Finset (Fin N)),
    S.card = B → k ≤ N - B →
    ∃ A : Finset (Fin N),
      A.card = k ∧ Disjoint S A ∧ survival {S} A = 1

end ControlStack.EvalIntegrity
