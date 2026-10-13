import ControlStack.Scenarios.SC25Content

namespace ControlStack.SC25Content

open ControlStack.SC25

def Back_sc25_content_safe : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op),
    let sg := grun R h cls ops
    Set.InjOn h {x | ∃ it ∈ sg.1.queue, it.content = x} →
    ∀ e ∈ sg.1.executed,
      ∃ a ∈ R.auditors, (e.id, e.content, true, a) ∈ sg.2

end ControlStack.SC25Content
