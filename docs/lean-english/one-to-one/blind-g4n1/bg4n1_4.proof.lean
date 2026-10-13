theorem claim : Claim := by
  classical
  refine ⟨Iff.rfl, ?_, ?_⟩
  · intro admins trusted T U ops hU ht
    exact Iff.rfl
  · intro admins trusted T U ops
    let V := (admins ++ ops.map Prod.fst).filter (fun a => decide (U a))
    have memV (a : ℕ) : a ∈ V ↔ a ∈ admins ++ ops.map Prod.fst ∧ U a := by
      simp [V]
      tauto
    refine ⟨V, ?_, ?_, Iff.rfl⟩
    · constructor
      · intro h a ha
        exact h a ((memV a).mp ha).2
      · intro h a hUa ha
        exact h a ((memV a).mpr ⟨List.mem_append_left _ ha, hUa⟩) ha
    · constructor
      · intro h io hio hnV
        apply h io hio
        intro hUi
        apply hnV
        exact (memV io.1).mpr ⟨List.mem_append_right _ (List.mem_map.mpr ⟨io, hio, rfl⟩), hUi⟩
      · intro h io hio hnU
        apply h io hio
        intro hV
        exact hnU ((memV io.1).mp hV).2
