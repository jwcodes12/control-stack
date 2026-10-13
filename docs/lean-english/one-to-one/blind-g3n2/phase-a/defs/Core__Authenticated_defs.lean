-- EXCERPT of ControlStack/Core/Authenticated.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.Authenticated

open ControlStack.Gate

variable {St Op Eff : Type}

/-- the authentication guard: an operation claiming identity `x` is applied only if its true issuer is `x` -/
def Authentic (claim : Op → Option ℕ) (io : ℕ × Op) : Prop := claim io.2 = none ∨ claim io.2 = some io.1

/-- the gate with authenticated issuers -/
def authed (G : System St Op Eff) (claim : Op → Option ℕ) : System St (ℕ × Op) Eff where
  step s io := if Authentic claim io then G.step s io.2 else s
  effects := G.effects

/-- the operations actually applied: the authentic ones, without their issuers -/
def applied (claim : Op → Option ℕ) (ops : List (ℕ × Op)) : List Op :=
  (ops.filter (fun io => decide (Authentic claim io))).map Prod.snd

/-- **Lifting.** Any spec of `G` is a spec of `authed G claim`: rejected operations change nothing, accepted ones are
steps of `G`, and the effect log is `G`'s. -/
def authedSpec (G : System St Op Eff) (claim : Op → Option ℕ) (S : Spec G) : Spec (authed G claim) where
  Inv := S.Inv
  ok := S.ok
  step_inv s io h := by
    by_cases ha : Authentic claim io
    · simpa [authed, ha] using S.step_inv s io.2 h
    · simpa [authed, ha] using h
  log_prefix s io := by
    by_cases ha : Authentic claim io
    · simpa [authed, ha] using S.log_prefix s io.2
    · simp [authed, ha]
  inv_ok := S.inv_ok

end ControlStack.Authenticated

