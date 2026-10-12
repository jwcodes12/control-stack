import ControlStack.Core.RefinementTransfer

/-!
Invariant- and legality-guarded version of `RefinementTransfer.run_simulation`.
Several scenario refinements have a one-step simulation that holds only from a
concrete invariant `I` (preserved by every legal step) and only for legal
concrete operations `L`. This lemma is the induction they all repeat; the
unguarded lemma is the special case `I := True`, `L := True`. Nothing here is a
runtime statement: each client still owes the one-step simulation, invariant
preservation and complete observation correspondence.
-/
namespace ControlStack.RefinementTransferInv
open ControlStack.RefinementTransfer

variable {C O A B : Type}

theorem run_simulation_guarded (cstep : C → O → C) (astep : B → A → B)
    (abstract : C → B) (emit : C → O → List A) (I : C → Prop) (L : O → Prop)
    (hpres : ∀ s o, L o → I s → I (cstep s o))
    (hstep : ∀ s o, L o → I s → abstract (cstep s o) =
      (emit s o).foldl astep (abstract s))
    (s : C) (ops : List O) (hops : ∀ o ∈ ops, L o) (hI : I s) :
    abstract (ops.foldl cstep s) =
      (emitTrace cstep emit s ops).foldl astep (abstract s) ∧
    I (ops.foldl cstep s) := by
  induction ops generalizing s with
  | nil => exact ⟨rfl, hI⟩
  | cons o ops ih =>
    have ho : L o := hops o List.mem_cons_self
    obtain ⟨h1, h2⟩ := ih (cstep s o) (fun x hx => hops x (List.mem_cons_of_mem o hx))
      (hpres s o ho hI)
    refine ⟨?_, h2⟩
    calc
      abstract ((o :: ops).foldl cstep s) =
          abstract (ops.foldl cstep (cstep s o)) := rfl
      _ = (emitTrace cstep emit (cstep s o) ops).foldl astep
          (abstract (cstep s o)) := h1
      _ = (emitTrace cstep emit (cstep s o) ops).foldl astep
          ((emit s o).foldl astep (abstract s)) := by rw [hstep s o ho hI]
      _ = (emitTrace cstep emit s (o :: ops)).foldl astep
          (abstract s) := by simp [emitTrace, List.foldl_append]

/-- A state-dependent guard `G` that must hold at every step of a particular trace. -/
def TraceGuard (cstep : C → O → C) (G : C → O → Prop) : C → List O → Prop
  | _, [] => True
  | s, o :: ops => G s o ∧ TraceGuard cstep G (cstep s o) ops

/-- Trace-guarded form: the side condition is not a per-operation predicate but a
state-dependent condition checked along the given trace (as SC-27's `TraceInj`). -/
theorem run_simulation_traceguard (cstep : C → O → C) (astep : B → A → B)
    (abstract : C → B) (emit : C → O → List A) (I : C → Prop) (G : C → O → Prop)
    (hpres : ∀ s o, G s o → I s → I (cstep s o))
    (hstep : ∀ s o, G s o → I s → abstract (cstep s o) =
      (emit s o).foldl astep (abstract s))
    (s : C) (ops : List O) (ht : TraceGuard cstep G s ops) (hI : I s) :
    abstract (ops.foldl cstep s) =
      (emitTrace cstep emit s ops).foldl astep (abstract s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    obtain ⟨hg, ht'⟩ := ht
    calc
      abstract ((o :: ops).foldl cstep s) =
          abstract (ops.foldl cstep (cstep s o)) := rfl
      _ = (emitTrace cstep emit (cstep s o) ops).foldl astep
          (abstract (cstep s o)) := ih (cstep s o) ht' (hpres s o hg hI)
      _ = (emitTrace cstep emit (cstep s o) ops).foldl astep
          ((emit s o).foldl astep (abstract s)) := by rw [hstep s o hg hI]
      _ = (emitTrace cstep emit s (o :: ops)).foldl astep
          (abstract s) := by simp [emitTrace, List.foldl_append]

end ControlStack.RefinementTransferInv

#print axioms ControlStack.RefinementTransferInv.run_simulation_guarded
#print axioms ControlStack.RefinementTransferInv.run_simulation_traceguard
