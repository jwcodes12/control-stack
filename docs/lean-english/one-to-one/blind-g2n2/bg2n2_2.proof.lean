open ControlStack ControlStack.SC12
example : FrozenBack = (∀ (admins : List ℕ) (s : St) (ops : List Op),
    s.halted = true → BackAt admins s ops) := rfl
example (admins : List ℕ) (s : St) (ops : List Op) (hh : s.halted = true) :
    OrigAt admins s ops := halt_freezes admins s ops hh

theorem claim : Claim := by
  intro admins s ops hh
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨run [9] full init [.start 9 1, .spawn 1 5 true 0, .fire 5, .halt 9],
    [.start 9 2, .spawn 1 6 true 0, .fire 5, .endSession 9 1, .halt 9], ?_⟩
  decide
