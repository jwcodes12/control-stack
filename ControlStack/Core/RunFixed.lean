import Mathlib.Tactic

/-!
Generic fixed-point lemmas for `List.foldl`, the shape of every scenario `run`.
They state, once, the induction that each scenario's `halt_freezes` repeats:
if a predicate `P` makes every step the identity (or leaves one observed field
unchanged while `P` persists), then `P` freezes the whole run.
No scenario is imported and no pinned file is touched; the per-scenario bridges
are in `ControlStack/Scenarios/GateReuse.lean`.
-/
namespace ControlStack.Gate

/-- If every step from a `P`-state is the identity, a `P`-state is a fixed point of every run. -/
theorem foldl_fixed {σ α : Type} (step : σ → α → σ) (P : σ → Prop)
    (fixed : ∀ s o, P s → step s o = s) {s : σ} (hs : P s) (ops : List α) :
    ops.foldl step s = s := by
  induction ops with
  | nil => rfl
  | cons o ops ih => simp only [List.foldl_cons, fixed s o hs, ih]

/-- If steps from a `P`-state keep the observed field `f` and keep `P`, the run keeps `f`. -/
theorem foldl_field_fixed {σ α β : Type} (step : σ → α → σ) (P : σ → Prop) (f : σ → β)
    (fixed : ∀ s o, P s → f (step s o) = f s ∧ P (step s o)) {s : σ} (hs : P s)
    (ops : List α) : f (ops.foldl step s) = f s := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := fixed s o hs
    rw [ih h2, h1]

/-- A reflexive, transitive relation `Q` that every legal step from a `P`-state respects
(keeping `P`) relates the start of a run to its end. -/
theorem foldl_rel_fixed {σ α : Type} (step : σ → α → σ) (L : α → Prop) (P : σ → Prop)
    (Q : σ → σ → Prop) (hrefl : ∀ s, Q s s) (htrans : ∀ a b c, Q a b → Q b c → Q a c)
    (hstep : ∀ s o, L o → P s → Q s (step s o) ∧ P (step s o)) {s : σ} (hs : P s)
    (ops : List α) (hops : ∀ o ∈ ops, L o) : Q s (ops.foldl step s) := by
  induction ops generalizing s with
  | nil => exact hrefl s
  | cons o ops ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := hstep s o (hops o List.mem_cons_self) hs
    exact htrans _ _ _ h1 (ih h2 (fun x hx => hops x (List.mem_cons_of_mem o hx)))

/-- A list of operations that are all `legal` lifts to the subtype of legal operations
without changing the run. -/
theorem foldl_legal {σ α : Type} (step : σ → α → σ) (legal : α → Prop) (ops : List α)
    (hops : ∀ o ∈ ops, legal o) (s : σ) :
    ∃ ops' : List {o : α // legal o},
      ops'.foldl (fun s o => step s o.1) s = ops.foldl step s := by
  induction ops generalizing s with
  | nil => exact ⟨[], rfl⟩
  | cons o ops ih =>
    obtain ⟨ops', h⟩ := ih (fun x hx => hops x (List.mem_cons_of_mem o hx)) (step s o)
    exact ⟨⟨o, hops o List.mem_cons_self⟩ :: ops', by simpa using h⟩

end ControlStack.Gate

#print axioms ControlStack.Gate.foldl_fixed
#print axioms ControlStack.Gate.foldl_field_fixed
#print axioms ControlStack.Gate.foldl_legal
#print axioms ControlStack.Gate.foldl_rel_fixed
