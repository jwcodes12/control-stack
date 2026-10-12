import ControlStack.Core.RefinementTransfer
import ControlStack.Scenarios.SC16Refinement

/-!
SC-16 has an unconditional local model-to-model one-step simulation, so its
recorded simulation_run theorem is an instance of RefinementTransfer. The
pinned original stays byte-identical. This bridge does not prove runtime
equivalence of registry.py, signer.py, or admission.py to the model.
-/
namespace ControlStack.SC16Refinement
open ControlStack.SC16

theorem simulation_run_via_transfer (R : Roles) (h : ℕ → ℕ)
    (s : CSt) (ops : List COp) :
    α (runC R h false s ops) = run R h full (α s) (absTrace R h s ops) := by
  have hstep : ∀ st op, α (stepC R h false st op) =
      (opsOf R h st op).foldl (step R h full) (α st) := by
    intro st op
    simpa only [run] using (simulation R h st op)
  have htrace : ∀ st os, absTrace R h st os =
      RefinementTransfer.emitTrace (stepC R h false) (opsOf R h) st os := by
    intro st os
    induction os generalizing st with
    | nil => rfl
    | cons op tail ih =>
        change opsOf R h st op ++ absTrace R h (stepC R h false st op) tail =
          opsOf R h st op ++
            RefinementTransfer.emitTrace (stepC R h false) (opsOf R h)
              (stepC R h false st op) tail
        rw [ih]
  change α (ops.foldl (stepC R h false) s) =
    (absTrace R h s ops).foldl (step R h full) (α s)
  rw [htrace]
  exact RefinementTransfer.run_simulation
    (stepC R h false) (step R h full) α (opsOf R h) hstep s ops

/-- Agreement is proof-irrelevant equality of proofs of the identical proposition. -/
theorem simulation_run_agree (R : Roles) (h : ℕ → ℕ)
    (s : CSt) (ops : List COp) :
    simulation_run_via_transfer R h s ops = simulation_run R h s ops := rfl

end ControlStack.SC16Refinement

#print axioms ControlStack.SC16Refinement.simulation_run_via_transfer
#print axioms ControlStack.SC16Refinement.simulation_run_agree
