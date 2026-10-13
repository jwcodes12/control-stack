open ControlStack ControlStack.SC14
example : FrozenBack = (∀ (E : Env) (exp : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal o) → BackAt E exp ops) := rfl
example (E : Env) (exp : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal o) :
    OrigAt E exp ops := sc14_safe E exp ops hops

theorem claim : Claim := by
  intro E exp ops hops
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨[.work (2, 2, 2) 0, .tick, .work (3, 3, 3) 0], ?_, ?_⟩
  · simp [legal]
  · decide
