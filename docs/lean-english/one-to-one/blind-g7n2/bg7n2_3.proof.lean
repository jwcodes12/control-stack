open ControlStack
open ControlStack.SC28
#check (ControlStack.SC28.fork_shares_lease : OrigFull)

theorem claim : Claim :=
by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  constructor
  · intro s child
    simp [BackFresh, OrigFresh, leaseOf, Option.map_eq_none_iff, List.find?_eq_none,
      List.mem_map, not_exists, not_and]
    constructor
    · intro h b hb
      exact h child b hb rfl
    · intro h a b hab he
      subst a
      exact h b hab
  · intro admins G s c p ch nl lid _ _ _
    rfl

theorem witness : Witness :=
by
  unfold Witness
  decide
