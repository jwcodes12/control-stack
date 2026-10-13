namespace PL_bg5n2_6
open ControlStack.SC23IsolationV2 ControlStack.Authenticated ControlStack.Gate
def Back_sc23v2_safe_authenticated : Prop :=
  ∀ (E : Env) (U : List ℕ),
    (∀ u ∈ U, u ∉ E.users) →
      ∀ (ops : List (ℕ × Op)),
        let s := (authed (raw E) claim).run init ops
        ∀ x ∈ s.executed, x.tool ∈ E.sensitive → x.tainted = true →
          ∃ (c n : ℕ), c ∈ E.users ∧ c ∉ U ∧
            (c, Op.confirm c n x.tool x.vals) ∈ ops

def Claim : Prop :=
  (Back_sc23v2_safe_authenticated = (∀ (E : Env) (U : List ℕ),
    (∀ u ∈ U, u ∉ E.users) → ∀ (ops : List (ℕ × Op)),
    ∀ x ∈ ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops).executed,
    x.tool ∈ E.sensitive → x.tainted = true →
      ∃ c n, c ∈ E.users ∧ c ∉ U ∧ (c, Op.confirm c n x.tool x.vals) ∈ ops)) ∧
  (∀ (E : Env) (U : List ℕ), (∀ u ∈ U, u ∉ E.users) →
    ∀ (ops : List (ℕ × Op)) (x : Act),
      x ∈ ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops).executed →
      x.tool ∈ E.sensitive → x.tainted = true →
      ((∃ (c n : ℕ), c ∈ E.users ∧ c ∉ U ∧ (c, Op.confirm c n x.tool x.vals) ∈ ops) ↔
       (∃ c n, c ∈ E.users ∧ c ∉ U ∧ (c, Op.confirm c n x.tool x.vals) ∈ ops)))
def Witness : Prop :=
  (∀ u ∈ ([7] : List ℕ), u ∉ E0.users) ∧
  ((authed (raw E0) ControlStack.SC23IsolationV2.claim).run init
    [(7,.toolResult 66),(1,.confirm 1 7 5 [66]),(7,.act 5 [0] 7)]).executed = [⟨5,[66],true,some 7⟩]
end PL_bg5n2_6
