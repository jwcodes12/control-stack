import Std

/-!
Reusable *model-to-model* trace-refinement induction. Each client still owes
the one-step simulation and complete effect-observation correspondence; this
lemma proves nothing about a deployed OS, Python process or missing events.
-/
namespace ControlStack.RefinementTransfer

variable {C O A B : Type}

def emitTrace (cstep : C → O → C) (emit : C → O → List A) : C → List O → List A
  | _, [] => []
  | s, o :: ops => emit s o ++ emitTrace cstep emit (cstep s o) ops

/-- Once one concrete step simulates a list of abstract steps, every finite trace does. -/
theorem run_simulation (cstep : C → O → C) (astep : B → A → B)
    (abstract : C → B) (emit : C → O → List A)
    (hstep : ∀ s o, abstract (cstep s o) =
      (emit s o).foldl astep (abstract s))
    (s : C) (ops : List O) :
    abstract (ops.foldl cstep s) =
      (emitTrace cstep emit s ops).foldl astep (abstract s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    calc
      abstract ((o :: ops).foldl cstep s) =
          abstract (ops.foldl cstep (cstep s o)) := rfl
      _ = (emitTrace cstep emit (cstep s o) ops).foldl astep
          (abstract (cstep s o)) := ih _
      _ = (emitTrace cstep emit (cstep s o) ops).foldl astep
          ((emit s o).foldl astep (abstract s)) := by rw [hstep]
      _ = (emitTrace cstep emit s (o :: ops)).foldl astep
          (abstract s) := by simp [emitTrace, List.foldl_append]

end ControlStack.RefinementTransfer

#print axioms ControlStack.RefinementTransfer.run_simulation
