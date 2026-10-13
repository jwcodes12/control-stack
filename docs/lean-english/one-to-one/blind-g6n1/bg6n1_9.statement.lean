namespace PL_bg6n1_9

open ControlStack.SC25Refinement ControlStack.SC25

def FrozenBack : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp),
    let s := runC R h cls false cinit ops
    Set.InjOn h {x | ∃ it ∈ s.items, it.content = x} →
    ∀ e ∈ s.effects,
      ∃ a ∈ s.auditLog,
        a.id = e.id ∧ a.content = e.content ∧ a.pass = true ∧ a.by_ ∈ R.auditors

def Back (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp) : Prop := ∀ e ∈ (runC R h cls false cinit ops).effects, ∃ a ∈ (runC R h cls false cinit ops).auditLog, a.id = e.id ∧ a.content = e.content ∧ a.pass = true ∧ a.by_ ∈ R.auditors
def Orig (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp) : Prop := ∀ e ∈ (runC R h cls false cinit ops).effects, ∃ a ∈ (runC R h cls false cinit ops).auditLog, a.id = e.id ∧ a.content = e.content ∧ a.pass = true ∧ a.by_ ∈ R.auditors

def Claim : Prop :=
  (FrozenBack = (∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp), Set.InjOn h {x | ∃ it ∈ (runC R h cls false cinit ops).items, it.content = x} → Back R h cls ops)) ∧
    (∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp), Set.InjOn h {x | ∃ it ∈ (runC R h cls false cinit ops).items, it.content = x} → (Back R h cls ops ↔ Orig R h cls ops))

def Witness : Prop :=
  let ops : List COp := [.submit 1 0 7 false, .audit 2 0 true, .fire 0, .submit 1 1 100 true, .audit 2 1 true, .approve 3 1, .crash, .restart, .fire 1]
  Set.InjOn (id : ℕ → ℕ) {x | ∃ it ∈ (runC R0 id cls0 false cinit ops).items, it.content = x} ∧
    (runC R0 id cls0 false cinit ops).effects.map ERow.content = [7, 100] ∧
    (runC R0 id cls0 false cinit ops).auditLog.map ARow.content = [7, 100]

end PL_bg6n1_9
