/-!
Conditional halt liveness under *bounded delivery* by a trusted scheduler.

This separates the missing scheduling/fairness obligation from the already
proved absorbing-halt invariant. If a trusted halt operation occurs in the first
n operations, the reference gate ends halted and cannot append further effects.
Without any scheduled halt, an untrusted sequence of ordinary requests never
sets the halt bit. This is a transition-system theorem, NOT an OS/scheduler
refinement or a guarantee that a real halt is delivered.
-/
import ControlStack.Gate

namespace ControlStack.HaltLiveness

open ControlStack.Gate

theorem run_append {St Op Eff : Type} (G : System St Op Eff)
    (s : St) (before after : List Op) :
    G.run s (before ++ after) = G.run (G.run s before) after := by
  simp [System.run, List.foldl_append]

/-- Inserting a trusted halt before an arbitrary suffix makes the halt bit sticky. -/
theorem delivered_halt_absorbs {St Op Eff : Type} (G : System St Op Eff)
    (sh : St × Bool) (rest : List (HOp Op)) :
    (withHalt G).run sh (.halt :: rest) = (sh.1, true) := by
  rcases sh with ⟨s, b⟩
  cases b <;> simp [System.run_cons, withHalt, halt_absorbing]

/-- Scheduling premise: a trusted halt occurs strictly before the n-th
position. This is an external scheduler obligation, not an axiom. -/
def DeliveredWithin {Op : Type} (n : Nat) (ops : List (HOp Op)) : Prop :=
  ∃ prefix suffix, ops = prefix ++ (.halt :: suffix) ∧ prefix.length < n

/-- Bounded delivery implies the model has halted after this finite trace. -/
theorem liveness_if_delivered {St Op Eff : Type} (G : System St Op Eff)
    (s : St) (n : Nat) (ops : List (HOp Op))
    (h : DeliveredWithin n ops) :
    ((withHalt G).run (s, false) ops).2 = true := by
  rcases h with ⟨prefix, suffix, heq, _⟩
  subst ops
  simp [run_append, delivered_halt_absorbs]

/-- The effect log after a delivered trusted halt equals the log immediately
before that halt, even if arbitrarily many operations follow. -/
theorem effects_frozen_after_delivered_halt {St Op Eff : Type} (G : System St Op Eff)
    (s : St) (prefix suffix : List (HOp Op)) :
    (withHalt G).effects ((withHalt G).run (s, false) (prefix ++ (.halt :: suffix))) =
      (withHalt G).effects ((withHalt G).run (s, false) prefix) := by
  simp [run_append, delivered_halt_absorbs, withHalt]

/-- Necessity witness: an arbitrarily long trace of *only* ordinary operations
does not halt automatically, regardless of its effects. Without scheduler
fairness / delivery no bounded liveness conclusion is possible. -/
theorem ordinary_operations_never_halt {St Op Eff : Type} (G : System St Op Eff)
    (s : St) (ops : List Op) :
    ((withHalt G).run (s, false) (ops.map HOp.op)).2 = false := by
  induction ops generalizing s with
  | nil => rfl
  | cons op tail ih =>
    simpa [System.run_cons, withHalt] using ih (G.step s op)

end ControlStack.HaltLiveness

#print axioms ControlStack.HaltLiveness.delivered_halt_absorbs
#print axioms ControlStack.HaltLiveness.liveness_if_delivered
#print axioms ControlStack.HaltLiveness.effects_frozen_after_delivered_halt
#print axioms ControlStack.HaltLiveness.ordinary_operations_never_halt
