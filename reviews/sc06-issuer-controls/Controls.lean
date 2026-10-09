/-
Independent SC-06 negative controls; source-only, no runtime correspondence.
Run after building ControlStack.Scenarios.SC06OneUse with pinned Lean.
-/
import ControlStack.Scenarios.SC06OneUse

open ControlStack.SC06OneUse

example :
    (run R0 init [.ingest 2 1 42, .confirm 6 3 2 7 0 42, .act 2 7 0 3]).effects = [] := by
  decide

example :
    (run R0 init [.ingest 2 2 42, .confirm 5 3 2 7 0 42, .act 2 7 0 3]).effects = [] := by
  decide

example :
    (run R0 init [
      .ingest 2 1 42, .ingest 2 3 42,
      .confirm 5 3 2 7 0 42, .act 2 7 1 3]).effects = [] := by
  decide

example : (run R0 init [.halt 6]).halted = false := by
  decide
