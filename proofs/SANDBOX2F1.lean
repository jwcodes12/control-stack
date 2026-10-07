open PL_SANDBOXF1

theorem fp2_split1 (W : Path) (sd : List Path) : PL_SANDBOX2F1.fixedPolicy2 W sd =
    [.bind [] [] .ro] ++
    ([.tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++
      sd.map (fun d => .bind d d .rw) ++ hiddenDirs.map .tmpfs ++
      [.bind mathlibProj mathlibProj .ro]) := by
  simp [PL_SANDBOX2F1.fixedPolicy2]

theorem fp2_split2 (W : Path) (sd : List Path) : PL_SANDBOX2F1.fixedPolicy2 W sd =
    ([.bind [] [] .ro, .tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++
      sd.map (fun d => .bind d d .rw)) ++
    (hiddenDirs.map .tmpfs ++ [.bind mathlibProj mathlibProj .ro]) := by
  simp [PL_SANDBOX2F1.fixedPolicy2]

theorem part_a : ∀ W : Path, ["var", "tmp"] <+: W →
    ReadsHost (fixedPolicy W [home ++ [".agent-b"]]) (home ++ [".agent-b", "sessions", "s.jsonl"])
      (home ++ [".agent-b", "sessions", "s.jsonl"]) := by
  intro W _
  refine ⟨home ++ [".agent-b"], home ++ [".agent-b"], .rw, ?_, ?_⟩
  · simp [effective, fixedPolicy, hiddenDirs, home, research, mathlibProj, Mount.tgt]
  · simp [home]

theorem part_b : ∀ (W : Path) (stateDirs : List Path) (canWrite : Path → Prop) (p hp : Path),
    WritesHost (PL_SANDBOX2F1.fixedPolicy2 W stateDirs) canWrite p hp →
      W <+: hp ∨ ∃ d ∈ stateDirs, d <+: hp := by
  intro W stateDirs canWrite p hp ⟨src, t, he, hhp, _⟩
  obtain ⟨hmem, _⟩ := PLDep_SANDBOXF1.eff_mem he
  simp [PL_SANDBOX2F1.fixedPolicy2] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨hd, rfl⟩
  · exact Or.inl ⟨_, hhp.symm⟩
  · exact Or.inr ⟨_, hd, _, hhp.symm⟩

theorem part_c : ∀ (W : Path) (stateDirs : List Path) (p hp H : Path), ["var", "tmp"] <+: W →
    H ∈ hiddenDirs → H <+: hp → ReadsHost (PL_SANDBOX2F1.fixedPolicy2 W stateDirs) p hp →
      mathlibProj <+: hp := by
  intro W sd p hp H hW hH hHp ⟨src, t, m, he, hhp⟩
  obtain ⟨hmem, htp⟩ := PLDep_SANDBOXF1.eff_mem he
  simp [PL_SANDBOX2F1.fixedPolicy2] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨hd, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exfalso
    simp only [List.nil_append, List.length_nil, List.drop_zero] at hhp
    subst hhp
    rw [fp2_split1] at he
    have h2 := PLDep_SANDBOXF1.eff_tail he (x := .tmpfs H) (by simp [hH]) hHp
    simp [mathlibProj, research, home] at h2
  · exfalso
    have hv : ["var", "tmp"] <+: hp := hW.trans ⟨_, hhp.symm⟩
    obtain ⟨as, has | has⟩ := PLDep_SANDBOXF1.hidden_head H hH
    · subst has
      exact absurd (PLDep_SANDBOXF1.head_eq hHp hv) (by decide)
    · subst has
      exact absurd (PLDep_SANDBOXF1.head_eq hHp hv) (by decide)
  · exfalso
    simp only [Mount.tgt] at htp
    obtain ⟨r, rfl⟩ := htp
    simp only [List.drop_left] at hhp
    subst hhp
    rw [fp2_split2] at he
    have h2 := PLDep_SANDBOXF1.eff_tail he (x := .tmpfs H) (by simp [hH]) hHp
    simp at h2
  · exact ⟨_, hhp.symm⟩

theorem claim : PL_SANDBOX2F1.Claim := ⟨part_a, part_b, part_c⟩

theorem witness : PL_SANDBOX2F1.Witness := by
  unfold PL_SANDBOX2F1.Witness
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨home ++ [".agent-b"], home ++ [".agent-b"], ?_, ?_, trivial⟩
    · simp [effective, PL_SANDBOX2F1.fixedPolicy2, hiddenDirs, home, research, mathlibProj, Mount.tgt]
    · simp [home]
  · refine ⟨["var", "tmp", "job-x"], ["var", "tmp", "work"], ?_, ?_, trivial⟩
    · simp [effective, PL_SANDBOX2F1.fixedPolicy2, hiddenDirs, home, research, mathlibProj, Mount.tgt]
    · simp
  · refine ⟨mathlibProj, mathlibProj, .ro, ?_, ?_⟩
    · simp [effective, PL_SANDBOX2F1.fixedPolicy2, hiddenDirs, home, research, mathlibProj, Mount.tgt]
    · simp
