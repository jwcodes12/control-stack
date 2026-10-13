open ControlStack ControlStack.SC14
example : FrozenBack = (∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true → BackAt E s ops) := rfl
example (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) :
    OrigAt E s ops := halt_freezes E s ops hh

theorem claim : Claim := by
  intro E s ops hh
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨⟨(2, 2, 2), (2, 2, 2), 0, 100, [((2, 2, 2), 0, 100)], true⟩,
    [.rollback, .work (1, 1, 1) 0, .tick, .setExpiry 9 200, .halt 9], ?_⟩
  decide
