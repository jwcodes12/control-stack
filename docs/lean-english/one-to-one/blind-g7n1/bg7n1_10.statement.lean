namespace PL_bg7n1_10
open ControlStack.SC27Refinement
open ControlStack.SC27ExtensionOnly (Env)

def FrozenBack : Prop :=
  ∀ (E : Env) (first second : List COp) (l : List ℕ),
    TraceInj E cinit (first ++ second) →
    let middle := runC E false cinit first
    let final := runC E false cinit (first ++ second)
    (∃ a ∈ ancs middle.wlog, a.2 = l) →
    ∀ a ∈ ancs final.wlog,
      a ∈ ancs middle.wlog ∨ l <+: a.2

def BackAt (E : Env) (first second : List COp) (l : List ℕ) : Prop :=
  let middle := runC E false cinit first
  let final := runC E false cinit (first ++ second)
  ∀ a ∈ ancs final.wlog, a ∈ ancs middle.wlog ∨ l <+: a.2

def OrigAt (E : Env) (first second : List COp) (l : List ℕ) : Prop :=
  ∀ a ∈ ancs (runC E false cinit (first ++ second)).wlog,
  a ∈ ancs (runC E false cinit first).wlog ∨ l <+: a.2

def Claim : Prop :=
  (FrozenBack ↔ (∀ (E : Env) (first second : List COp) (l : List ℕ), TraceInj E cinit (first ++ second) → (∃ a ∈ ancs (runC E false cinit first).wlog, a.2 = l) → BackAt E first second l)) ∧
  (∀ (E : Env) (first second : List COp) (l : List ℕ), TraceInj E cinit (first ++ second) → (∃ a ∈ ancs (runC E false cinit first).wlog, a.2 = l) → (BackAt E first second l ↔ OrigAt E first second l))

def Witness : Prop :=
  let first : List COp := [.append 5, .examine]
  let second : List COp := [.append 6, .examine]
  TraceInj E0 cinit (first ++ second) ∧
  (∃ a ∈ ancs (runC E0 false cinit first).wlog, a.2 = [5]) ∧
  ancs (runC E0 false cinit (first ++ second)).wlog = [(6, [5]), (607, [5, 6])]

end PL_bg7n1_10
