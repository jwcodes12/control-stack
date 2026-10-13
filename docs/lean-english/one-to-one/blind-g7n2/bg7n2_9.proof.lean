open ControlStack
open ControlStack.SC28Liveness
open ControlStack ControlStack.SC28
#check (ControlStack.SC28Liveness.global_cap_blocks_honest : OrigFull)

theorem claim : Claim :=
by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intro s t
  constructor
  · rintro ⟨hz, he, ht⟩
    exact ⟨he, hz, he.symm.trans ht⟩
  · rintro ⟨he, hz, hs⟩
    exact ⟨hz, he, he.trans hs⟩

theorem witness : Witness :=
by
  unfold Witness
  decide
