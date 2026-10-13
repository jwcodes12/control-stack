namespace PL_bg5n1_3
open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
open scoped BigOperators

def Back_sc21_undetected_le_pow : Prop :=
  ∀ (N B k : ℕ) (rep truth : Fin N → ℕ),
    0 < N → B ≤ N → (corrupt rep truth).card = k →
    survival (randomSchedules N B) (corrupt rep truth) ≤
      (((N - B : ℕ) : ℝ) / (N : ℝ)) ^ k

def HBack (N B k : ℕ) (rep truth : Fin N → ℕ) : Prop :=
  (0 < N) ∧
  (B ≤ N) ∧
  ((corrupt rep truth).card = k)
def HOrig (N B k : ℕ) (rep truth : Fin N → ℕ) : Prop :=
  (0 < N) ∧
  (B ≤ N) ∧
  ((corrupt rep truth).card = k)
noncomputable def BackAt (N B k : ℕ) (rep truth : Fin N → ℕ) : Prop :=
  survival (randomSchedules N B) (corrupt rep truth) ≤ (((N - B : ℕ) : ℝ) / (N : ℝ)) ^ k
noncomputable def OrigAt (N B k : ℕ) (rep truth : Fin N → ℕ) : Prop :=
  survival (randomSchedules N B) (corrupt rep truth) ≤ (((N : ℝ) - B) / N) ^ k

def wRep (i : Fin 2) : ℕ := if i = 0 then 1 else 0
def Witness : Prop := 0 < (2 : ℕ) ∧ 1 ≤ (2 : ℕ) ∧ (corrupt wRep (fun _ => 0)).card = 1 ∧ (randomSchedules 2 1).Nonempty

def Claim : Prop :=
  (Back_sc21_undetected_le_pow ↔ ∀ (N B k : ℕ) (rep truth : Fin N → ℕ), HBack N B k rep truth → BackAt N B k rep truth) ∧
  (∀ (N B k : ℕ) (rep truth : Fin N → ℕ), HBack N B k rep truth ↔ HOrig N B k rep truth) ∧
  (∀ (N B k : ℕ) (rep truth : Fin N → ℕ), HBack N B k rep truth → (BackAt N B k rep truth ↔ OrigAt N B k rep truth))
end PL_bg5n1_3
