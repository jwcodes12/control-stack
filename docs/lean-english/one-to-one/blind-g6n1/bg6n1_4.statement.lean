namespace PL_bg6n1_4

open ControlStack.SC25Content ControlStack.SC25

def FrozenBack : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op),
    let sg := grun R h cls ops
    Set.InjOn h {x | ∃ it ∈ sg.1.queue, it.content = x} →
    ∀ e ∈ sg.1.executed,
      ∃ a ∈ R.auditors, (e.id, e.content, true, a) ∈ sg.2

def BackRow (R : Roles) (g : List ARec) (e : Exec) : Prop :=
  ∃ a ∈ R.auditors, (e.id, e.content, true, a) ∈ g

def OrigRow (R : Roles) (g : List ARec) (e : Exec) : Prop :=
  ∃ x ∈ g, x.1 = e.id ∧ x.2.1 = e.content ∧ x.2.2.1 = true ∧ x.2.2.2 ∈ R.auditors

def Back (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) : Prop :=
  ∀ e ∈ (grun R h cls ops).1.executed, BackRow R (grun R h cls ops).2 e

def Orig (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) : Prop :=
  ∀ e ∈ (run R h cls full init ops).executed, OrigRow R (grun R h cls ops).2 e

def Claim : Prop :=
  (FrozenBack = (∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op),
      Set.InjOn h {x | ∃ it ∈ (grun R h cls ops).1.queue, it.content = x} → Back R h cls ops)) ∧
  (∀ (R : Roles) (g : List ARec) (e : Exec), BackRow R g e ↔ OrigRow R g e) ∧
  (∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op),
    Set.InjOn h {x | ∃ it ∈ (run R h cls full init ops).queue, it.content = x} →
    (Back R h cls ops ↔ Orig R h cls ops))

def Witness : Prop :=
  let ops : List Op := [.submit 1 0 100 true, .audit 2 0 true, .approve 3 0, .check 0, .crash, .check 0, .fire 0]
  Set.InjOn (id : ℕ → ℕ) {x | ∃ it ∈ (grun R0 id cls0 ops).1.queue, it.content = x} ∧
    (grun R0 id cls0 ops).1.executed.map Exec.content = [100] ∧ (0, 100, true, 2) ∈ (grun R0 id cls0 ops).2

end PL_bg6n1_4
