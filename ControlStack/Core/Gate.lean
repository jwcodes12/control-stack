/-
Shared reference-monitor interface (families F1/F3 of SCENARIO-CATALOG.md §3).

A gate is a transition system whose state exposes an append-only EFFECT LOG. A gate spec supplies an inductive
invariant that makes every logged effect acceptable (`ok`). From this:

- `Spec.trace_safe`: after any finite interleaving of operations from an invariant state, the invariant holds, the
  old effect log is a prefix of the new one, and every effect is acceptable;
- `NoAgentEffects.agent_trace_inert`: if operations the agent can issue never append effects, any agent-only trace
  leaves the effect log unchanged;
- `withHalt`: adds a trusted HALT to any gate. Halting is absorbing: after it, no operation changes the state, so no
  further effect occurs (`halt_absorbing`). The spec lifts unchanged (`withHalt_spec`). This is the generic
  "absorbing shutdown" obligation (scaffold assumption A11; SC-13, SC-25).

The interface adds no new mathematics: each generic theorem is an induction over the trace. Its job is reuse. Five
clients import it (`GateClients.lean`): the three existing gates (AuditDispatch, AuditGate, EgressGate) and two new
primitives (F4 content-addressed artefact gate, F7 exact-payload approval).

Limits (adversarial review D10):
- A `Spec` has no content by itself: `ok := True` satisfies it for any append-only log. The content is each client's
  `ok` and `Inv`.
- `Spec` has no initial-state field; each client must show that its initial state satisfies `Inv`.
- `withHalt` is absorbing BY CONSTRUCTION (a sticky bit). It shows that a halt bit composes with any gate's spec,
  not that a deployed component has one.
- Nothing here is about liveness (that a halt is ever processed).

Scope: like every model here, a gate spec is about the transition system. That the deployed component implements it,
and that no effect bypasses it, are correspondence obligations recorded per client.
-/
import Mathlib.Tactic

namespace ControlStack.Gate

/-- a reference-monitor transition system with an effect log -/
structure System (St Op Eff : Type) where
  step : St → Op → St
  effects : St → List Eff

def System.run {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List Op) : St := ops.foldl G.step s

@[simp] theorem System.run_nil {St Op Eff : Type} (G : System St Op Eff) (s : St) : G.run s [] = s := rfl

@[simp] theorem System.run_cons {St Op Eff : Type} (G : System St Op Eff) (s : St) (o : Op) (ops : List Op) :
    G.run s (o :: ops) = G.run (G.step s o) ops := rfl

/-- a gate specification: an inductive invariant, an append-only effect log, and acceptability of logged effects -/
structure Spec {St Op Eff : Type} (G : System St Op Eff) where
  Inv : St → Prop
  ok : St → Eff → Prop
  step_inv : ∀ s o, Inv s → Inv (G.step s o)
  log_prefix : ∀ s o, G.effects s <+: G.effects (G.step s o)
  inv_ok : ∀ s, Inv s → ∀ e ∈ G.effects s, ok s e

/-- **Trace safety for any gate.** -/
theorem Spec.trace_safe {St Op Eff : Type} {G : System St Op Eff} (S : Spec G) (s : St) (ops : List Op)
    (h : S.Inv s) :
    S.Inv (G.run s ops) ∧ G.effects s <+: G.effects (G.run s ops) ∧
      ∀ e ∈ G.effects (G.run s ops), S.ok (G.run s ops) e := by
  induction ops generalizing s with
  | nil => exact ⟨h, List.prefix_refl _, S.inv_ok s h⟩
  | cons o ops ih =>
    obtain ⟨h1, h2, h3⟩ := ih (G.step s o) (S.step_inv s o h)
    exact ⟨h1, (S.log_prefix s o).trans h2, h3⟩

/-- operations the agent can issue never append effects -/
structure NoAgentEffects {St Op Eff : Type} (G : System St Op Eff) (agent : Op → Prop) : Prop where
  inert : ∀ s o, agent o → G.effects (G.step s o) = G.effects s

/-- an agent-only trace leaves the effect log unchanged -/
theorem NoAgentEffects.agent_trace_inert {St Op Eff : Type} {G : System St Op Eff} {agent : Op → Prop}
    (H : NoAgentEffects G agent) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, agent o) :
    G.effects (G.run s ops) = G.effects s := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    simp only [System.run_cons]
    rw [ih (G.step s o) (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')),
      H.inert s o (hops o List.mem_cons_self)]

/-! ## Absorbing halt for any gate -/

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

/-- **Halting is absorbing.** After a halt, no trace changes the state (in particular, no new effect). -/
theorem halt_absorbing {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List (HOp Op)) :
    (withHalt G).run (s, true) ops = (s, true) := by
  induction ops with
  | nil => rfl
  | cons o ops ih => simpa [System.run_cons, withHalt] using ih

/-- halting from any running state: the effect log is frozen at its value when the halt was processed -/
theorem halt_freezes {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List (HOp Op)) :
    (withHalt G).effects ((withHalt G).run (s, false) (.halt :: ops)) = G.effects s := by
  rw [System.run_cons]
  have h1 : (withHalt G).step (s, false) .halt = (s, true) := by simp [withHalt]
  rw [h1, halt_absorbing]
  rfl

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

#print axioms ControlStack.Gate.Spec.trace_safe
#print axioms ControlStack.Gate.NoAgentEffects.agent_trace_inert
#print axioms ControlStack.Gate.halt_absorbing
#print axioms ControlStack.Gate.halt_freezes
#print axioms ControlStack.Gate.withHalt_spec
