open ControlStack.Deployment

lemma start_mem (d : IR) (start : Nat) : start ∈ reachable d start := by
  unfold reachable
  have keep : ∀ (xs : List Nat) (seen : List Nat), start ∈ seen →
      start ∈ xs.foldl (fun seen _ =>
        (seen ++ d.edges.filterMap (fun e =>
          if e.source ∈ seen ∧ e.target ≠ d.broker ∧ e.target ≠ d.receiver
          then some e.target else none)).eraseDups) seen := by
    intro xs
    induction xs with
    | nil => intro seen h; exact h
    | cons x xs ih =>
      intro seen h
      apply ih
      exact List.mem_eraseDups.mpr (List.mem_append_left _ h)
  exact keep _ _ (by simp)

lemma stronger (d : IR) (h : BackAccepted d) : Accepted d := by
  rcases h with ⟨basic, roles, identities, runtime, writers, bypass⟩
  refine ⟨basic, ?_, ?_, runtime, ?_, ?_⟩
  · rcases roles with ⟨size, agents, brokers, receivers, reviewers, approvers, facts⟩
    have eqfilter : d.nodes.filter (fun n => n.agent) =
        d.nodes.filter (fun n => n.role == 0) := by
      apply List.filter_congr
      intro n hn
      have hiff := (facts n hn).1
      cases ha : n.agent <;> simp_all
    exact ⟨size, by simpa only [eqfilter] using agents,
      brokers, receivers, reviewers, approvers, facts⟩
  · intro a ha b hb ids
    exact identities a ha b hb (fun eq => ids (congrArg Node.id eq))
  · rcases writers with ⟨sink, sources, db, dbsources⟩
    have sink' : (d.edges.filter (fun e => e.target == d.sink && e.write)).map
        Edge.source = [d.receiver] := by
      simpa only [Bool.and_comm] using sources
    have dbsources' :
        (d.edges.filter (fun e => e.target == d.database && e.write)).map Edge.source =
          [d.broker, d.receiver] ∨
        (d.edges.filter (fun e => e.target == d.database && e.write)).map Edge.source =
          [d.receiver, d.broker] := by
      simpa only [Bool.and_comm] using dbsources
    have length : (d.edges.filter (fun e => e.target == d.database && e.write)).length = 2 := by
      have mapped : ((d.edges.filter (fun e => e.target == d.database && e.write)).map Edge.source).length = 2 := by
        rcases dbsources' with h | h <;> rw [h] <;> rfl
      simpa only [List.length_map] using mapped
    have present (uid : Nat) (hu : uid = d.broker ∨ uid = d.receiver) :
        ∃ e ∈ d.edges, e.target = d.database ∧ e.write = true ∧ e.source = uid := by
      have mem : uid ∈ (d.edges.filter (fun e => e.target == d.database && e.write)).map Edge.source := by
        rcases dbsources' with h | h <;> rw [h] <;> rcases hu with rfl | rfl <;> simp
      obtain ⟨e, he, source⟩ := List.mem_map.mp mem
      have eh := List.mem_filter.mp he
      have flags : e.target = d.database ∧ e.write = true := by simpa using eh.2
      exact ⟨e, eh.1, flags.1, flags.2, source⟩
    exact ⟨sink, db, sink', length, present _ (.inl rfl), present _ (.inr rfl)⟩
  · intro a ha agent
    obtain ⟨sink, db, closed⟩ := bypass a ha agent
    exact ⟨start_mem d a.id, sink, db, closed⟩

theorem claim : Claim := by
  exact ⟨stronger, by decide, by unfold BackAccepted; decide⟩

theorem witness : Witness := by
  exact ⟨by unfold BackAccepted; decide, clean_accepted⟩
