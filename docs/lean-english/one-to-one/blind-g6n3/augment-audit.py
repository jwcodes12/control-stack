from pathlib import Path
P=Path(__file__).resolve().parent
f=P/'bg6n3_6.statement.lean'
s=f.read_text().replace('def Witness : Prop :=','def Nonvacuity : Prop :=')
extra='''def ackOps : List LOp := setupOps ++ [.base .recover, .base (.bankProcess 0), .base (.ack 0)]
def ackStart : TSt := runT R0 10 tinit ackOps
def oldRound : List LOp × List LOp := ([], [.base (.bankProcess 0)])
def FairnessAudit : Prop :=
  ¬ Delivers 0 pcRound ∧
  (∀ o ∈ ackOps, legalL R0 o) ∧ ackStart.c.halted = false ∧
  Delivers 0 oldRound ∧ ¬ DeliversT R0 10 0 ackStart oldRound

def Witness : Prop := Nonvacuity ∧ FairnessAudit
'''
s=s.replace('\nend PL_bg6n3_6', '\n'+extra+'\nend PL_bg6n3_6')
f.write_text(s)
f=P/'bg6n3_6.proof.lean'; s=f.read_text().replace('theorem witness : Witness :=','theorem nonvacuity : Nonvacuity :=')
s+='''
theorem fairness_audit : FairnessAudit := by
  refine ⟨per_copy_weaker.1, ?_, by decide, ?_, ?_⟩
  · simp [ackOps, setupOps, legalL, legalC]
  · refine ⟨[], [], rfl, ?_⟩
    simp [DropFree]
  · have hb : batch R0 10 ackStart (.base .recover) = [] := by decide
    unfold DeliversT
    change ¬ ∃ e ∈ batch R0 10 ackStart (.base .recover), e.2.1 = 0 ∧ _
    rw [hb]
    simp

theorem witness : Witness := ⟨nonvacuity, fairness_audit⟩
'''
f.write_text(s)
(P/'audit-fairness.lean').unlink(missing_ok=True)
