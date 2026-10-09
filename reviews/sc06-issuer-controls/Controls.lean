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

/- A confirmation bound to reader 2 must not authorize reader 3. -/
example :
    (run R0 init [
      .ingest 2 1 42,
      .confirm 5 3 2 7 0 42,
      .act 3 7 0 3]).effects = [] := by
  decide

/- A confirmation for sensitive tool 7 must not authorize another tool. -/
example :
    (run R0 init [
      .ingest 2 1 42,
      .confirm 5 3 2 7 0 42,
      .act 2 8 0 3]).effects = [] := by
  decide

/- An existing confirmation ID cannot be rebound to a different reader. -/
example :
    (run R0 init [
      .ingest 2 1 42,
      .ingest 3 1 42,
      .confirm 5 3 2 7 0 42,
      .confirm 5 3 3 7 1 42]).confirmations.length = 1 := by
  decide

/- A valid confirmation does not override an authorized HALT. -/
example :
    (run R0 init [
      .ingest 2 1 42,
      .confirm 5 3 2 7 0 42,
      .halt 9,
      .act 2 7 0 3]).effects = [] := by
  decide

/- Non-vacuity: the exact same trusted path succeeds without HALT. -/
example :
    (run R0 init [
      .ingest 2 1 42,
      .confirm 5 3 2 7 0 42,
      .act 2 7 0 3]).effects = [⟨3, 2, 7, 0, 42⟩] := by
  decide
