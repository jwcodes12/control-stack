namespace PL_bg7n1_9
open ControlStack.SC27Refinement
open ControlStack.SC27Chain (chainHead)
open ControlStack.SC27ExtensionOnly (Env)

def FrozenBack : Prop :=
  ∀ (E : Env) (ops : List COp),
    TraceInj E cinit ops →
    let final := runC E false cinit ops
    Set.InjOn (chainHead E.H E.h0)
      {l | l ∈ final.accepted ∨ ∃ a ∈ ancs final.wlog, a.2 = l} →
    ∀ m ∈ final.accepted,
      (∃ a ∈ ancs final.wlog, a.2 = m) ∧
      (∃ latest, final.ghostLast = some latest ∧ m <+: latest)

def BackAt (E : Env) (ops : List COp) : Prop :=
  let final := runC E false cinit ops
  ∀ m ∈ final.accepted, (∃ a ∈ ancs final.wlog, a.2 = m) ∧
    (∃ latest, final.ghostLast = some latest ∧ m <+: latest)

def OrigAt (E : Env) (ops : List COp) : Prop :=
  ∀ m ∈ (runC E false cinit ops).accepted,
  (∃ a ∈ ancs (runC E false cinit ops).wlog, a.2 = m) ∧
    ∃ l, (runC E false cinit ops).ghostLast = some l ∧ m <+: l

def Claim : Prop :=
  (FrozenBack ↔ (∀ (E : Env) (ops : List COp), TraceInj E cinit ops → Set.InjOn (chainHead E.H E.h0) {l | l ∈ (runC E false cinit ops).accepted ∨ ∃ a ∈ ancs (runC E false cinit ops).wlog, a.2 = l} → BackAt E ops)) ∧
  (∀ (E : Env) (ops : List COp), TraceInj E cinit ops → Set.InjOn (chainHead E.H E.h0) {l | l ∈ (runC E false cinit ops).accepted ∨ ∃ a ∈ ancs (runC E false cinit ops).wlog, a.2 = l} → (BackAt E ops ↔ OrigAt E ops))

def Witness : Prop :=
  let ops : List COp := [.append 5, .examine, .verify [5]]
  let t := runC E0 false cinit ops
  TraceInj E0 cinit ops ∧ t.accepted = [[5]] ∧ ancs t.wlog = [(6, [5])] ∧
  t.ghostLast = some [5] ∧
  Set.InjOn (chainHead E0.H E0.h0) {l | l ∈ t.accepted ∨ ∃ a ∈ ancs t.wlog, a.2 = l} ∧
  (let u := runC E0 false cinit [.append 5, .examine, .rewrite [], .examine]
   forks u.wlog = [] ∧ ancs u.wlog = [(6, [5])] ∧ u.accepted = [])

end PL_bg7n1_9
