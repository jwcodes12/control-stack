import ControlStack.Core.RefinementTransfer
import ControlStack.Scenarios.SC25Refinement

/-!
Reuse bridge (PR #55). `SC25Refinement.simulation_run` is proved in its own file by direct induction; that file is pinned by hash in
`scenarios/SC-25/manifest.json` (recorded kernel check), so it is left byte-for-byte unchanged. This file proves the *same statement*
from the generic `RefinementTransfer.run_simulation`, showing SC-25 is an instance of the shared model-to-model simulation lemma.
Nothing here is runtime evidence.
-/
namespace ControlStack.SC25Refinement
open ControlStack.SC25

theorem simulation_run_via_transfer (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (ops : List COp) :
    α (runC R h cls false s ops) = run R h cls full (α s) (absTrace h cls R s ops) := by
  have hstep : ∀ st op, α (stepC R h cls false st op) =
      (opsOf h cls st op).foldl (step R h cls full) (α st) := by
    intro st op
    simpa only [run] using (simulation R h cls st op)
  have htrace : ∀ st os, absTrace h cls R st os =
      RefinementTransfer.emitTrace (stepC R h cls false) (opsOf h cls) st os := by
    intro st os
    induction os generalizing st with
    | nil => rfl
    | cons op tail ih =>
      change opsOf h cls st op ++ absTrace h cls R (stepC R h cls false st op) tail =
        opsOf h cls st op ++
          RefinementTransfer.emitTrace (stepC R h cls false) (opsOf h cls) (stepC R h cls false st op) tail
      rw [ih]
  change α (ops.foldl (stepC R h cls false) s) =
    (absTrace h cls R s ops).foldl (step R h cls full) (α s)
  rw [htrace]
  exact RefinementTransfer.run_simulation
    (stepC R h cls false) (step R h cls full) α (opsOf h cls) hstep s ops

/-- The bridge and the original proof state the same fact, so either may be used. -/
theorem simulation_run_agree (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (ops : List COp) :
    simulation_run_via_transfer R h cls s ops = simulation_run R h cls s ops := rfl

end ControlStack.SC25Refinement
#print axioms ControlStack.SC25Refinement.simulation_run_via_transfer
