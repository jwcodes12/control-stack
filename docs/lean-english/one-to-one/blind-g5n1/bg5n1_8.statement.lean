namespace PL_bg5n1_8
open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall
open scoped BigOperators

def Back_sc22_unreplicated_misreport : Prop :=
  ∀ (N B k : ℕ) (rep truth : Fin N → ℕ),
    (corrupt rep truth).card = k →
    survival (randomSchedules N B) (corrupt rep truth) =
      (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)

def HBack (N B k : ℕ) (rep truth : Fin N → ℕ) : Prop :=
  ((corrupt rep truth).card = k)
def HOrig (N B k : ℕ) (rep truth : Fin N → ℕ) : Prop :=
  ((corrupt rep truth).card = k)
noncomputable def BackAt (N B k : ℕ) (rep truth : Fin N → ℕ) : Prop :=
  survival (randomSchedules N B) (corrupt rep truth) = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
noncomputable def OrigAt (N B k : ℕ) (rep truth : Fin N → ℕ) : Prop :=
  survival (randomSchedules N B) (corrupt rep truth) = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)

def wRep (i : Fin 2) : ℕ := if i = 0 then 1 else 0
def Witness : Prop := (corrupt wRep (fun _ => 0)).card = 1 ∧ 1 ≤ (2 : ℕ) ∧ (randomSchedules 2 1).Nonempty

def Claim : Prop :=
  (Back_sc22_unreplicated_misreport ↔ ∀ (N B k : ℕ) (rep truth : Fin N → ℕ), HBack N B k rep truth → BackAt N B k rep truth) ∧
  (∀ (N B k : ℕ) (rep truth : Fin N → ℕ), HBack N B k rep truth ↔ HOrig N B k rep truth) ∧
  (∀ (N B k : ℕ) (rep truth : Fin N → ℕ), HBack N B k rep truth → (BackAt N B k rep truth ↔ OrigAt N B k rep truth))
end PL_bg5n1_8
