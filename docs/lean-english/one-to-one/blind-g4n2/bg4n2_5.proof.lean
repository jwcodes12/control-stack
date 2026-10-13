open ControlStack.SC19 ControlStack.AuthInstances ControlStack.AuthenticatedLog
theorem back_shape : Back_sc19_safe_authenticated =
    (∀ E U ops, (∀ c, U c → c ∉ E.approvers) → (∀ c, U c → c ∉ E.verifiers) →
      BackPoint E U ops (authRun (step E full) claim19 init ops)) := rfl

theorem original_type (E : Env) (U : List ℕ) (ops : List (ℕ × Op))
    (ha : ∀ c ∈ U, c ∉ E.approvers) (hv : ∀ c ∈ U, c ∉ E.verifiers) :
    OrigPoint E U ops (authRun (step E full) claim19 init ops) := sc19_safe_authenticated E U ops ha hv

theorem point (E : Env) (U : ℕ → Prop) (ops : List (ℕ × Op)) (s : St) :
    BackPoint E U ops s ↔ OrigPredicatePoint E U ops s := by
  constructor
  · rintro ⟨hg, ha, hv⟩
    refine ⟨hg, ?_, ?_⟩
    · intro a ham
      obtain ⟨hm, hrole, hu⟩ := ha a ham
      exact ⟨a.2.1, .approve a.2.1 a.1, hm, hu, rfl, rfl, hrole⟩
    · intro i him
      obtain ⟨c, hm, hrole, hu⟩ := hv i him
      exact ⟨c, .verify c i, hm, hu, rfl, hrole⟩
  · rintro ⟨hg, ha, hv⟩
    refine ⟨hg, ?_, ?_⟩
    · intro a ham
      obtain ⟨c, o, hm, hu, ho, hc, hrole⟩ := ha a ham
      subst o
      subst c
      exact ⟨hm, hrole, hu⟩
    · intro i him
      obtain ⟨c, o, hm, hu, ho, hrole⟩ := hv i him
      subst o
      exact ⟨c, hm, hrole, hu⟩

theorem transport (E : Env) (U V : ℕ → Prop) (ops : List (ℕ × Op)) (s : St)
    (same : ∀ c o, (c, o) ∈ ops → (U c ↔ V c)) :
    BackPoint E U ops s ↔ BackPoint E V ops s := by
  have dir (U V : ℕ → Prop) (same : ∀ c o, (c, o) ∈ ops → (U c ↔ V c)) :
      BackPoint E U ops s → BackPoint E V ops s := by
    rintro ⟨hg, ha, hv⟩
    refine ⟨hg, ?_, ?_⟩
    · intro a ham
      obtain ⟨hm, hrole, hu⟩ := ha a ham
      exact ⟨hm, hrole, fun hvc => hu ((same _ _ hm).mpr hvc)⟩
    · intro i him
      obtain ⟨c, hm, hrole, hu⟩ := hv i him
      exact ⟨c, hm, hrole, fun hvc => hu ((same _ _ hm).mpr hvc)⟩
  exact ⟨dir U V same, dir V U (fun c o hm => (same c o hm).symm)⟩

theorem finite_representation (E : Env) (U : ℕ → Prop) (ops : List (ℕ × Op)) :
    ∃ V : List ℕ, (∀ c ∈ V, U c) ∧ (∀ s, BackPoint E U ops s ↔ OrigPoint E V ops s) := by
  classical
  let V := (ops.map Prod.fst).filter (fun c => decide (U c))
  have memV (c : ℕ) : c ∈ V ↔ c ∈ ops.map Prod.fst ∧ U c := by simp [V]
  refine ⟨V, fun c hc => ((memV c).mp hc).2, ?_⟩
  intro s
  have same : ∀ c o, (c, o) ∈ ops → (U c ↔ c ∈ V) := by
    intro c o hm
    have hc : c ∈ ops.map Prod.fst := List.mem_map.mpr ⟨(c, o), hm, rfl⟩
    exact ⟨fun hu => (memV c).mpr ⟨hc, hu⟩, fun hv => ((memV c).mp hv).2⟩
  exact (transport E U (fun c => c ∈ V) ops s same).trans (point E (fun c => c ∈ V) ops s)

theorem claim : Claim := by
  exact ⟨point, (fun E U ops s => point E (fun c => c ∈ U) ops s), finite_representation⟩
theorem witness : Witness := by simp only [Witness]; decide
