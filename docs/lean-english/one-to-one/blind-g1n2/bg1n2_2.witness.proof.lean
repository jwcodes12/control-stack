lemma delta_dist {A : Type} [Fintype A] [DecidableEq A] (a : A) : IsDist (delta a) := by
  constructor
  · intro x; unfold delta; split_ifs <;> norm_num
  · simp [delta]

theorem witness : Witness := by
  unfold Witness
  classical
  let inst : Fintype (Ev 1 Unit) := ⟨{.send none (), .send (some 0) (), .other, .close}, by
    intro e
    cases e with
    | send c r =>
      cases r
      cases c with
      | none => simp
      | some c => have hc : c = 0 := Subsingleton.elim _ _; subst c; simp
    | other => simp
    | close => simp⟩
  refine ⟨inst, ?_⟩
  letI := inst
  refine ⟨delta (), (fun _ _ => delta (fun _ => Ev.close)), (fun _ _ => delta 0), ?_⟩
  exact ⟨delta_dist (), fun _ _ => delta_dist _, fun _ _ => delta_dist _⟩
