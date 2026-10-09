/-
F8 composition over the shared gate interface (`Core/Gate.lean`).

- `prod G₁ G₂`: two gates side by side. An operation is `Sum.inl o₁` or `Sum.inr o₂` and touches only its own
  component. The joint state carries ONE merged effect log, tagged by side, in the order the effects happened: a step
  of G₁ appends G₁'s NEW effects (the suffix its own append-only log gained) tagged `inl`. `Coherent` says the merged
  log projects onto each component's log.
- `prodSpec`: the two specs lift to the product (`Inv₁ ∧ Inv₂ ∧ Coherent`, `ok` by tag). `prod_trace_safe` is the
  trace-level corollary from `prodInit`.
- `withSharedHalt`: ONE halt bit for both components; `prod_halt_freezes` (both components and the merged log are
  frozen). `separate_halt_leaves_other_running`: halting only G₁ does not stop G₂.
- `withBridge G₁ G₂ b`: adds a deputy operation that READS G₁'s state and ACTS on G₂'s state (`b : St₁ → St₂ → St₂`).
  Negative: `bridge_breaks_joint` — both specs hold alone, yet a bridge produces an effect G₂'s spec forbids (the
  confused-deputy shape of `GateComposition.confused_deputy_counterexample`, made a statement about specs; a concrete
  SC-26 × SC-16 instance is `Witnesses/DeputyBridge.lean`). Positive: `bridgeSpec` — the joint spec survives when the
  bridge is ADMISSIBLE: from states satisfying both invariants it preserves `Inv₂` and only appends to G₂'s log.
  `admissible_of_step`: a bridge that acts only by issuing one of G₂'s own operations (chosen from both states) is
  admissible — the deputy must go through G₂'s gate.

Limits: composition is by interleaving; there is no shared state between G₁ and G₂ other than what a bridge reads.
A real F8 claim also needs the runtime to map onto this product (no third path) and, for budgets, a shared counter
(that is `Scenarios/SC28Budget.lean`, not this file). No new mathematics: inductions over traces.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.Compose

open ControlStack.Gate

variable {St₁ St₂ Op₁ Op₂ Eff₁ Eff₂ : Type}

/-- the left-tagged entries of a merged log -/
def lefts (l : List (Eff₁ ⊕ Eff₂)) : List Eff₁ := l.filterMap Sum.getLeft?

/-- the right-tagged entries of a merged log -/
def rights (l : List (Eff₁ ⊕ Eff₂)) : List Eff₂ := l.filterMap Sum.getRight?

@[simp] theorem lefts_append (l m : List (Eff₁ ⊕ Eff₂)) : lefts (l ++ m) = lefts l ++ lefts m := by
  simp [lefts, List.filterMap_append]

@[simp] theorem rights_append (l m : List (Eff₁ ⊕ Eff₂)) : rights (l ++ m) = rights l ++ rights m := by
  simp [rights, List.filterMap_append]

@[simp] theorem lefts_inl (l : List Eff₁) : lefts (l.map (Sum.inl : Eff₁ → Eff₁ ⊕ Eff₂)) = l := by
  simp [lefts, List.filterMap_map, Function.comp_def]

@[simp] theorem rights_inl (l : List Eff₁) : rights (l.map (Sum.inl : Eff₁ → Eff₁ ⊕ Eff₂)) = [] := by
  simp [rights, List.filterMap_map, Function.comp_def]

@[simp] theorem lefts_inr (l : List Eff₂) : lefts (l.map (Sum.inr : Eff₂ → Eff₁ ⊕ Eff₂)) = [] := by
  simp [lefts, List.filterMap_map, Function.comp_def]

@[simp] theorem rights_inr (l : List Eff₂) : rights (l.map (Sum.inr : Eff₂ → Eff₁ ⊕ Eff₂)) = l := by
  simp [rights, List.filterMap_map, Function.comp_def]

/-- the effects a component gained in one step (its log is append-only under a spec) -/
def newEffects {St Op Eff : Type} (G : System St Op Eff) (s s' : St) : List Eff :=
  (G.effects s').drop (G.effects s).length

theorem append_newEffects {St Op Eff : Type} (G : System St Op Eff) (s s' : St) (h : G.effects s <+: G.effects s') :
    G.effects s ++ newEffects G s s' = G.effects s' :=
  List.prefix_iff_eq_append.1 h

/-- joint state: both components and the merged, side-tagged effect log -/
structure PSt (St₁ St₂ Eff₁ Eff₂ : Type) where
  s₁ : St₁
  s₂ : St₂
  log : List (Eff₁ ⊕ Eff₂)

/-- replace the left component by `s'`, appending its new effects to the merged log -/
def stepL (G₁ : System St₁ Op₁ Eff₁) (p : PSt St₁ St₂ Eff₁ Eff₂) (s' : St₁) : PSt St₁ St₂ Eff₁ Eff₂ :=
  ⟨s', p.s₂, p.log ++ (newEffects G₁ p.s₁ s').map Sum.inl⟩

/-- replace the right component by `s'`, appending its new effects to the merged log -/
def stepR (G₂ : System St₂ Op₂ Eff₂) (p : PSt St₁ St₂ Eff₁ Eff₂) (s' : St₂) : PSt St₁ St₂ Eff₁ Eff₂ :=
  ⟨p.s₁, s', p.log ++ (newEffects G₂ p.s₂ s').map Sum.inr⟩

/-- two gates side by side; each operation touches only its own component -/
def prod (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) :
    System (PSt St₁ St₂ Eff₁ Eff₂) (Op₁ ⊕ Op₂) (Eff₁ ⊕ Eff₂) where
  step := fun p o => match o with
    | .inl o => stepL G₁ p (G₁.step p.s₁ o)
    | .inr o => stepR G₂ p (G₂.step p.s₂ o)
  effects := PSt.log

/-- the merged log projects onto each component's own log -/
def Coherent (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (p : PSt St₁ St₂ Eff₁ Eff₂) : Prop :=
  lefts p.log = G₁.effects p.s₁ ∧ rights p.log = G₂.effects p.s₂

/-- the joint initial state built from two component states -/
def prodInit (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (s₁ : St₁) (s₂ : St₂) :
    PSt St₁ St₂ Eff₁ Eff₂ :=
  ⟨s₁, s₂, (G₁.effects s₁).map Sum.inl ++ (G₂.effects s₂).map Sum.inr⟩

theorem prodInit_coherent (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (s₁ : St₁) (s₂ : St₂) :
    Coherent G₁ G₂ (prodInit G₁ G₂ s₁ s₂) := by
  simp [Coherent, prodInit]

theorem stepL_coherent (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (p : PSt St₁ St₂ Eff₁ Eff₂) (s' : St₁)
    (hc : Coherent G₁ G₂ p) (hpre : G₁.effects p.s₁ <+: G₁.effects s') : Coherent G₁ G₂ (stepL G₁ p s') := by
  obtain ⟨h1, h2⟩ := hc
  refine ⟨?_, ?_⟩
  · simp only [stepL, lefts_append, lefts_inl, h1]
    exact append_newEffects G₁ _ _ hpre
  · simp [stepL, h2]

theorem stepR_coherent (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (p : PSt St₁ St₂ Eff₁ Eff₂) (s' : St₂)
    (hc : Coherent G₁ G₂ p) (hpre : G₂.effects p.s₂ <+: G₂.effects s') : Coherent G₁ G₂ (stepR G₂ p s') := by
  obtain ⟨h1, h2⟩ := hc
  refine ⟨?_, ?_⟩
  · simp [stepR, h1]
  · simp only [stepR, rights_append, rights_inr, h2]
    exact append_newEffects G₂ _ _ hpre

/-- acceptability by tag -/
def tagOk {G₁ : System St₁ Op₁ Eff₁} {G₂ : System St₂ Op₂ Eff₂} (S₁ : Spec G₁) (S₂ : Spec G₂)
    (p : PSt St₁ St₂ Eff₁ Eff₂) : Eff₁ ⊕ Eff₂ → Prop :=
  Sum.elim (S₁.ok p.s₁) (S₂.ok p.s₂)

theorem tagOk_of_coherent {G₁ : System St₁ Op₁ Eff₁} {G₂ : System St₂ Op₂ Eff₂} (S₁ : Spec G₁) (S₂ : Spec G₂)
    (p : PSt St₁ St₂ Eff₁ Eff₂) (h1 : S₁.Inv p.s₁) (h2 : S₂.Inv p.s₂) (hc : Coherent G₁ G₂ p) :
    ∀ e ∈ p.log, tagOk S₁ S₂ p e := by
  intro e he
  cases e with
  | inl e =>
    apply S₁.inv_ok p.s₁ h1 e
    rw [← hc.1]
    exact List.mem_filterMap.2 ⟨_, he, rfl⟩
  | inr e =>
    apply S₂.inv_ok p.s₂ h2 e
    rw [← hc.2]
    exact List.mem_filterMap.2 ⟨_, he, rfl⟩

/-- **Specs lift to the product.** -/
def prodSpec {G₁ : System St₁ Op₁ Eff₁} {G₂ : System St₂ Op₂ Eff₂} (S₁ : Spec G₁) (S₂ : Spec G₂) :
    Spec (prod G₁ G₂) where
  Inv := fun p => S₁.Inv p.s₁ ∧ S₂.Inv p.s₂ ∧ Coherent G₁ G₂ p
  ok := tagOk S₁ S₂
  step_inv := by
    intro p o h
    obtain ⟨h1, h2, hc⟩ := h
    cases o with
    | inl o => exact ⟨S₁.step_inv _ o h1, h2, stepL_coherent G₁ G₂ p _ hc (S₁.log_prefix _ o)⟩
    | inr o => exact ⟨h1, S₂.step_inv _ o h2, stepR_coherent G₁ G₂ p _ hc (S₂.log_prefix _ o)⟩
  log_prefix := by
    intro p o
    cases o <;> exact List.prefix_append _ _
  inv_ok := fun p h => tagOk_of_coherent S₁ S₂ p h.1 h.2.1 h.2.2

/-- **Joint trace safety**: from two invariant states, after any interleaving, both invariants hold, the merged log
projects onto each component's log, and every merged effect is acceptable to its own component. -/
theorem prod_trace_safe {G₁ : System St₁ Op₁ Eff₁} {G₂ : System St₂ Op₂ Eff₂} (S₁ : Spec G₁) (S₂ : Spec G₂)
    (s₁ : St₁) (s₂ : St₂) (h1 : S₁.Inv s₁) (h2 : S₂.Inv s₂) (ops : List (Op₁ ⊕ Op₂)) :
    let p := (prod G₁ G₂).run (prodInit G₁ G₂ s₁ s₂) ops
    S₁.Inv p.s₁ ∧ S₂.Inv p.s₂ ∧ Coherent G₁ G₂ p ∧ ∀ e ∈ p.log, tagOk S₁ S₂ p e := by
  have h := (prodSpec S₁ S₂).trace_safe (prodInit G₁ G₂ s₁ s₂) ops ⟨h1, h2, prodInit_coherent G₁ G₂ s₁ s₂⟩
  exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.2⟩

/-! ## One shared halt -/

/-- both gates under ONE halt bit -/
def withSharedHalt (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) :
    System (PSt St₁ St₂ Eff₁ Eff₂ × Bool) (HOp (Op₁ ⊕ Op₂)) (Eff₁ ⊕ Eff₂) :=
  withHalt (prod G₁ G₂)

def sharedHaltSpec {G₁ : System St₁ Op₁ Eff₁} {G₂ : System St₂ Op₂ Eff₂} (S₁ : Spec G₁) (S₂ : Spec G₂) :
    Spec (withSharedHalt G₁ G₂) :=
  withHalt_spec (prodSpec S₁ S₂)

/-- **One halt freezes both components** and the merged log, whatever operations follow. -/
theorem prod_halt_freezes (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (p : PSt St₁ St₂ Eff₁ Eff₂)
    (ops : List (HOp (Op₁ ⊕ Op₂))) :
    let q := (withSharedHalt G₁ G₂).run (p, false) (.halt :: ops)
    q.1.s₁ = p.s₁ ∧ q.1.s₂ = p.s₂ ∧ q.1.log = p.log ∧ q.2 = true := by
  have h : (withSharedHalt G₁ G₂).run (p, false) (.halt :: ops) = (p, true) := by
    rw [System.run_cons]
    have h1 : (withSharedHalt G₁ G₂).step (p, false) .halt = (p, true) := by simp [withSharedHalt, withHalt]
    rw [h1]
    exact halt_absorbing _ p ops
  simp [h]

/-- a counter: each operation appends one effect -/
def counter : System ℕ Unit ℕ where
  step := fun n _ => n + 1
  effects := List.range

/-- **Separate halts do not compose into a shared one**: halting G₁ alone leaves G₂ producing effects. -/
theorem separate_halt_leaves_other_running :
    let q := (prod (withHalt counter) counter).run ⟨(0, false), 0, []⟩ [.inl .halt, .inr (), .inr ()]
    q.s₁.2 = true ∧ q.s₂ = 2 ∧ q.log = [.inr 0, .inr 1] := by
  decide

/-! ## Bridges (deputies) -/

inductive BOp (Op₁ Op₂ : Type) where
  | left (o : Op₁)
  | right (o : Op₂)
  /-- the deputy: reads G₁'s state, acts on G₂'s state -/
  | bridge

/-- the product with a deputy `b` that reads G₁'s state and rewrites G₂'s -/
def withBridge (G₁ : System St₁ Op₁ Eff₁) (G₂ : System St₂ Op₂ Eff₂) (b : St₁ → St₂ → St₂) :
    System (PSt St₁ St₂ Eff₁ Eff₂) (BOp Op₁ Op₂) (Eff₁ ⊕ Eff₂) where
  step := fun p o => match o with
    | .left o => stepL G₁ p (G₁.step p.s₁ o)
    | .right o => stepR G₂ p (G₂.step p.s₂ o)
    | .bridge => stepR G₂ p (b p.s₁ p.s₂)
  effects := PSt.log

/-- the sufficient condition: from states satisfying both invariants, the bridge preserves G₂'s invariant and only
appends to G₂'s effect log -/
def BridgeAdmissible {G₁ : System St₁ Op₁ Eff₁} {G₂ : System St₂ Op₂ Eff₂} (S₁ : Spec G₁) (S₂ : Spec G₂)
    (b : St₁ → St₂ → St₂) : Prop :=
  ∀ s₁ s₂, S₁.Inv s₁ → S₂.Inv s₂ → S₂.Inv (b s₁ s₂) ∧ G₂.effects s₂ <+: G₂.effects (b s₁ s₂)

/-- **Positive**: with an admissible bridge, the joint spec still holds. -/
def bridgeSpec {G₁ : System St₁ Op₁ Eff₁} {G₂ : System St₂ Op₂ Eff₂} (S₁ : Spec G₁) (S₂ : Spec G₂)
    (b : St₁ → St₂ → St₂) (hb : BridgeAdmissible S₁ S₂ b) : Spec (withBridge G₁ G₂ b) where
  Inv := fun p => S₁.Inv p.s₁ ∧ S₂.Inv p.s₂ ∧ Coherent G₁ G₂ p
  ok := tagOk S₁ S₂
  step_inv := by
    intro p o h
    obtain ⟨h1, h2, hc⟩ := h
    cases o with
    | left o => exact ⟨S₁.step_inv _ o h1, h2, stepL_coherent G₁ G₂ p _ hc (S₁.log_prefix _ o)⟩
    | right o => exact ⟨h1, S₂.step_inv _ o h2, stepR_coherent G₁ G₂ p _ hc (S₂.log_prefix _ o)⟩
    | bridge =>
      obtain ⟨hi, hp⟩ := hb p.s₁ p.s₂ h1 h2
      exact ⟨h1, hi, stepR_coherent G₁ G₂ p _ hc hp⟩
  log_prefix := by
    intro p o
    cases o <;> exact List.prefix_append _ _
  inv_ok := fun p h => tagOk_of_coherent S₁ S₂ p h.1 h.2.1 h.2.2

/-- **A deputy that goes through G₂'s gate is admissible**: if the bridge only issues one of G₂'s own operations
(chosen from both states), the joint spec holds. -/
theorem admissible_of_step {G₁ : System St₁ Op₁ Eff₁} {G₂ : System St₂ Op₂ Eff₂} (S₁ : Spec G₁) (S₂ : Spec G₂)
    (b : St₁ → St₂ → St₂) (f : St₁ → St₂ → Op₂) (hb : ∀ s₁ s₂, b s₁ s₂ = G₂.step s₂ (f s₁ s₂)) :
    BridgeAdmissible S₁ S₂ b := by
  intro s₁ s₂ _ h2
  rw [hb]
  exact ⟨S₂.step_inv s₂ _ h2, S₂.log_prefix s₂ _⟩

/-- G₁: an approval flag an operation can set; it has no effects -/
def flagGate : System Bool Unit Empty where
  step := fun _ _ => true
  effects := fun _ => []

def flagSpec : Spec flagGate where
  Inv := fun _ => True
  ok := fun _ _ => True
  step_inv := fun _ _ _ => trivial
  log_prefix := fun _ _ => List.prefix_refl _
  inv_ok := fun _ _ e => e.elim

/-- G₂: a gate that must never act (its own operations do nothing; acceptable effects: none) -/
def inertGate : System (List ℕ) Unit ℕ where
  step := fun s _ => s
  effects := id

def inertSpec : Spec inertGate where
  Inv := fun s => s = []
  ok := fun _ _ => False
  step_inv := fun _ _ h => h
  log_prefix := fun _ _ => List.prefix_refl _
  inv_ok := fun s h e he => by subst h; simp [inertGate] at he

/-- a deputy that acts on G₂ whenever G₁'s approval flag is set -/
def flagDeputy (s₁ : Bool) (s₂ : List ℕ) : List ℕ := if s₁ then s₂ ++ [0] else s₂

/-- **Negative (confused deputy)**: each spec holds on its own (`flagSpec`, `inertSpec`: G₂ never acts), yet with the
deputy the joint system logs an effect that G₂'s spec forbids. So two individually safe gates plus a bridge are not
safe; `BridgeAdmissible` fails for `flagDeputy`. -/
theorem bridge_breaks_joint :
    let p := (withBridge flagGate inertGate flagDeputy).run ⟨false, [], []⟩ [.left (), .bridge]
    p.log = [.inr 0] ∧ ¬ (∀ e ∈ p.log, tagOk flagSpec inertSpec p e) ∧ ¬ BridgeAdmissible flagSpec inertSpec flagDeputy := by
  refine ⟨rfl, fun h => ?_, fun h => ?_⟩
  · exact h (.inr 0) (by show (Sum.inr 0 : Empty ⊕ ℕ) ∈ [Sum.inr 0]; simp)
  · have := (h true [] trivial rfl).1
    simp [inertSpec, flagDeputy] at this

end ControlStack.Compose

#print axioms ControlStack.Compose.prodSpec
#print axioms ControlStack.Compose.prod_trace_safe
#print axioms ControlStack.Compose.prod_halt_freezes
#print axioms ControlStack.Compose.separate_halt_leaves_other_running
#print axioms ControlStack.Compose.bridgeSpec
#print axioms ControlStack.Compose.admissible_of_step
#print axioms ControlStack.Compose.bridge_breaks_joint
