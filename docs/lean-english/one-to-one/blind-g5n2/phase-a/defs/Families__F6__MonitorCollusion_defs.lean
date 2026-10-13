-- EXCERPT of ControlStack/Families/F6/MonitorCollusion.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.MonitorCollusion

open Finset ControlStack.Covert ControlStack.Leakage



section Transfer

variable {V : Type} [Fintype V]

/-- pass rate of a randomised decision rule β (β v = probability of PASS on view v) under view law P -/
noncomputable def passRate (P β : V → ℝ) : ℝ := ∑ v, P v * β v

/-- total variation distance -/
noncomputable def tv (P Q : V → ℝ) : ℝ := (1 / 2) * ∑ v, |P v - Q v|

end Transfer



section Canon

variable {V : Type} [Fintype V]

end Canon

section Witness

/-- views: one steganographic bit. Real attacks (from the colluding generator) carry the flag; honeypots don't. -/
def stegoReal : Bool → ℝ := fun v => if v then 1 else 0
def stegoHoney : Bool → ℝ := fun v => if v then 0 else 1
/-- the colluding monitor: PASS iff the flag is present -/
def stegoMonitor : Bool → ℝ := fun v => if v then 1 else 0

end Witness



section Phase

variable {Y O : Type} [Fintype Y] [Fintype O]

/-- binary-symmetric phase leak: each item's visible bit equals the phase with probability 101/200 -/
noncomputable def bscK : Bool → List (Unit × Bool) → Unit × Bool → ℝ :=
  fun φ _ z => if z.2 = φ then 101 / 200 else 99 / 200

end Phase

end ControlStack.MonitorCollusion

