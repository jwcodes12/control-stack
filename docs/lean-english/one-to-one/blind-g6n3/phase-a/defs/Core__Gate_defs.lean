-- EXCERPT of ControlStack/Core/Gate.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.Gate

/-- a reference-monitor transition system with an effect log -/
structure System (St Op Eff : Type) where
  step : St → Op → St
  effects : St → List Eff

def System.run {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List Op) : St := ops.foldl G.step s

/-- a gate specification: an inductive invariant, an append-only effect log, and acceptability of logged effects -/
structure Spec {St Op Eff : Type} (G : System St Op Eff) where
  Inv : St → Prop
  ok : St → Eff → Prop
  step_inv : ∀ s o, Inv s → Inv (G.step s o)
  log_prefix : ∀ s o, G.effects s <+: G.effects (G.step s o)
  inv_ok : ∀ s, Inv s → ∀ e ∈ G.effects s, ok s e

/-- operations the agent can issue never append effects -/
structure NoAgentEffects {St Op Eff : Type} (G : System St Op Eff) (agent : Op → Prop) : Prop where
  inert : ∀ s o, agent o → G.effects (G.step s o) = G.effects s

/-- operations of the halted system: an operation of the gate, or the trusted halt -/
inductive HOp (Op : Type) where
  | op (o : Op)
  | halt

/-- `withHalt G`: the gate with a halted flag; once halted, every operation is a no-op -/
def withHalt {St Op Eff : Type} (G : System St Op Eff) : System (St × Bool) (HOp Op) Eff where
  step := fun sh o =>
    if sh.2 then sh else
      match o with
      | .op o => (G.step sh.1 o, false)
      | .halt => (sh.1, true)
  effects := fun sh => G.effects sh.1

/-- the spec of any gate lifts to the halted gate unchanged -/
def withHalt_spec {St Op Eff : Type} {G : System St Op Eff} (S : Spec G) : Spec (withHalt G) where
  Inv := fun sh => S.Inv sh.1
  ok := fun sh e => S.ok sh.1 e
  step_inv := by
    intro sh o h
    rcases sh with ⟨s, b⟩
    cases b <;> cases o <;> simp [withHalt] <;> first | exact h | exact S.step_inv s _ h
  log_prefix := by
    intro sh o
    rcases sh with ⟨s, b⟩
    cases b <;> cases o <;> simp [withHalt]
    exact S.log_prefix s _
  inv_ok := fun sh h e he => S.inv_ok sh.1 h e he

end ControlStack.Gate

