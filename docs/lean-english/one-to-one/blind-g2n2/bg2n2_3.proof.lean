open ControlStack ControlStack.AuthInstances
example : FrozenBack = (∀ (admins U : List ℕ) (ops : List (ℕ × SC12.Op)),
    (∀ u ∈ U, u ∉ admins) → BackAt admins U ops
      (AuthenticatedLog.authRun (SC12.step admins SC12.full) claim12 SC12.init ops)) := rfl
example (admins U : List ℕ) (ops : List (ℕ × SC12.Op)) (hU : ∀ u ∈ U, u ∉ admins) :
    OrigAt admins U ops
      (AuthenticatedLog.authRun (SC12.step admins SC12.full) claim12 SC12.init ops) :=
  sc12_safe_authenticated admins U ops hU

theorem claim : Claim := by
  intro admins U ops s
  constructor
  · rintro ⟨hg, hp⟩
    refine ⟨hg, ?_⟩
    intro e he
    obtain ⟨c, hca, hcu, hco⟩ := hp e he
    exact ⟨c, SC12.Op.start c e.origin, hco, hcu, rfl, hca⟩
  · rintro ⟨hg, hp⟩
    refine ⟨hg, ?_⟩
    intro e he
    obtain ⟨c, o, hco, hcu, hoe, hca⟩ := hp e he
    subst o
    exact ⟨c, hca, hcu, hco⟩

theorem witness : Witness := by
  refine ⟨?_, ?_⟩
  · simp
  · decide
