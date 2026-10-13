open ControlStack ControlStack.SC12
example : FrozenBack = (∀ (admins : List ℕ) (s : St) (sess : ℕ) (ops : List Op),
    Inv s → sess ∈ s.ended → BackAt admins s sess ops) := rfl
example (admins : List ℕ) (s : St) (sess : ℕ) (ops : List Op)
    (h : Inv s) (hs : sess ∈ s.ended) : OrigAt admins s sess ops :=
  no_fire_after_end admins s ops h sess hs

theorem claim : Claim := by
  intro admins s sess ops h hs
  exact Iff.rfl

theorem witness : Witness := by
  let prior : List Op := [.start 9 1, .spawn 1 5 true 0, .fire 5, .endSession 9 1]
  refine ⟨run [9] full init prior, [.fire 5, .start 9 2, .spawn 2 6 true 0, .fire 6], ?_, ?_⟩
  · exact run_inv [9] init prior inv_init
  · decide
