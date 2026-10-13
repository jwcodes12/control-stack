namespace PL_bg5n1_4
open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
open scoped BigOperators

def Back_observable_sample_nogo : Prop :=
  ∀ (N B k : ℕ) (S : Finset (Fin N)),
    S.card = B → k ≤ N - B →
    ∃ A : Finset (Fin N),
      A.card = k ∧ Disjoint S A ∧ survival {S} A = 1

def HBack (N B k : ℕ) (S : Finset (Fin N)) : Prop :=
  (S.card = B) ∧
  (k ≤ N - B)
def HOrig (N B k : ℕ) (S : Finset (Fin N)) : Prop :=
  (S.card = B) ∧
  (k ≤ N - B)
noncomputable def BackAt (N B k : ℕ) (S : Finset (Fin N)) : Prop :=
  ∃ A : Finset (Fin N), A.card = k ∧ Disjoint S A ∧ survival {S} A = 1
noncomputable def OrigAt (N B k : ℕ) (S : Finset (Fin N)) : Prop :=
  ∃ A : Finset (Fin N), A.card = k ∧ Disjoint S A ∧ survival {S} A = 1

def Witness : Prop := ({0} : Finset (Fin 2)).card = 1 ∧ 1 ≤ 2 - (1 : ℕ) ∧ ∃ A : Finset (Fin 2), A.card = 1 ∧ Disjoint ({0} : Finset (Fin 2)) A

def Claim : Prop :=
  (Back_observable_sample_nogo ↔ ∀ (N B k : ℕ) (S : Finset (Fin N)), HBack N B k S → BackAt N B k S) ∧
  (∀ (N B k : ℕ) (S : Finset (Fin N)), HBack N B k S ↔ HOrig N B k S) ∧
  (∀ (N B k : ℕ) (S : Finset (Fin N)), HBack N B k S → (BackAt N B k S ↔ OrigAt N B k S))
end PL_bg5n1_4
