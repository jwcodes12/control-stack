import Lake
open Lake DSL

/-! Narrow CI project: compiles the covert-channel theorems (Mathlib only, no VCVio) on every push. -/
package CovertCI

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "5ed2965256430c3649e86755f9576b54eca72435"

@[default_target] lean_lib CovertCI
