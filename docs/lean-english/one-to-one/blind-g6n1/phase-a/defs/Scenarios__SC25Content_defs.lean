-- EXCERPT of ControlStack/Scenarios/SC25Content.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC25Content

open ControlStack.SC25

/-- a ghost audit record: (operation id, content the auditor saw, verdict, auditor) -/
abbrev ARec := ℕ × ℕ × Bool × ℕ

/-- the ghost record of one step: mirrors the `audit` branch of `SC25.step` under `full` -/
def auditRec (R : Roles) (s : St) : Op → List ARec
  | .audit c id p =>
    if s.halted = true ∧ full.haltCheck = true then []
    else match itemOf s id with
      | none => []
      | some it => if c ∈ R.auditors then [(id, it.content, p, c)] else []
  | _ => []

def gstep (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (sg : St × List ARec) (o : Op) : St × List ARec :=
  (step R h cls full sg.1 o, sg.2 ++ auditRec R sg.1 o)

/-- the model's run paired with the ghost audit records -/
def grun (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) : St × List ARec :=
  ops.foldl (gstep R h cls) (init, [])

/-- the ghost invariant: verdicts are ghost-recorded audits; ghost and executed contents are queue contents -/
structure J (h : ℕ → ℕ) (s : St) (g : List ARec) : Prop where
  verd : ∀ v ∈ s.verdicts, ∃ x ∈ g, x.1 = v.id ∧ h x.2.1 = v.d ∧ x.2.2.1 = v.pass ∧ v.by_ = some x.2.2.2
  gq : ∀ x ∈ g, ∃ it ∈ s.queue, it.content = x.2.1
  eq : ∀ e ∈ s.executed, ∃ it ∈ s.queue, it.content = e.content

end ControlStack.SC25Content

