import ControlStack.Scenarios.SC25Refinement

namespace ControlStack.SC25Refinement

open ControlStack.SC25

def Back_concrete_content_safe : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp),
    let s := runC R h cls false cinit ops
    Set.InjOn h {x | ∃ it ∈ s.items, it.content = x} →
    ∀ e ∈ s.effects,
      ∃ a ∈ s.auditLog,
        a.id = e.id ∧ a.content = e.content ∧ a.pass = true ∧ a.by_ ∈ R.auditors

end ControlStack.SC25Refinement
