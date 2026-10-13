namespace PL_bg6n1_2

open ControlStack.SC25

def FrozenBack : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St)
    (id : ℕ) (ops : List Op),
    id ∈ s.expired →
    id ∉ s.executed.map Exec.id →
    id ∉ (run R h cls full s ops).executed.map Exec.id

def Back (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (id : ℕ) (ops : List Op) : Prop := id ∉ (run R h cls full s ops).executed.map Exec.id
def Orig (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (id : ℕ) (ops : List Op) : Prop := id ∉ (run R h cls full s ops).executed.map Exec.id

def Claim : Prop :=
  (FrozenBack = (∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (id : ℕ) (ops : List Op), id ∈ s.expired → id ∉ s.executed.map Exec.id → Back R h cls s id ops)) ∧
    (∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (id : ℕ) (ops : List Op), id ∈ s.expired → id ∉ s.executed.map Exec.id → (Back R h cls s id ops ↔ Orig R h cls s id ops))

def Witness : Prop :=
  let s := run R0 id cls0 full init [.submit 1 0 7 false, .timeout 0]
  0 ∈ s.expired ∧ 0 ∉ s.executed.map Exec.id ∧
    (run R0 id cls0 full s [.audit 2 0 true, .check 0, .fire 0]).executed = [] ∧
    (run R0 id cls0 full s [.audit 2 0 true]).verdicts ≠ []

end PL_bg6n1_2
