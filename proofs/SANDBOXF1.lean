theorem eff_mem {pol : Policy} {p : Path} {m : Mount} (h : effective pol p = some m) :
    m ∈ pol ∧ m.tgt <+: p := by
  have h1 := List.mem_of_getLast? h
  simpa [List.mem_filter] using h1

theorem eff_tail {l1 l2 : Policy} {p : Path} {m x : Mount}
    (h : effective (l1 ++ l2) p = some m) (hx : x ∈ l2) (hP : x.tgt <+: p) : m ∈ l2 := by
  unfold effective at h
  rw [List.filter_append, List.getLast?_append] at h
  cases hy : (l2.filter (fun m => decide (m.tgt <+: p))).getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hy
    have hmx : x ∈ l2.filter (fun m => decide (m.tgt <+: p)) :=
      List.mem_filter.2 ⟨hx, by simpa using hP⟩
    rw [hy] at hmx
    simp at hmx
  | some y =>
    rw [hy] at h
    simp only [Option.some_or, Option.some.injEq] at h
    subst h
    exact (List.mem_filter.1 (List.mem_of_getLast? hy)).1

theorem head_eq {a b : String} {as bs l : Path} (h1 : a :: as <+: l) (h2 : b :: bs <+: l) :
    a = b := by
  obtain ⟨r1, rfl⟩ := h1
  obtain ⟨r2, h⟩ := h2
  simp only [List.cons_append, List.cons.injEq] at h
  exact h.1.symm

theorem hidden_head : ∀ H ∈ hiddenDirs, ∃ as, H = "home" :: as ∨ H = "tmp" :: as := by
  simp [hiddenDirs, home, research]

theorem cur_split (W : Path) : currentPolicy W = [.bind [] [] .rw] ++
    ([.tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++ hiddenDirs.map .tmpfs ++
      [.bind mathlibProj mathlibProj .ro]) := by
  simp [currentPolicy]

theorem claim_a : ∀ W : Path, ["var", "tmp"] <+: W →
    WritesHost (currentPolicy W) (fun hp => home <+: hp ∨ ["var", "tmp"] <+: hp)
      (home ++ [".toolchain", "bin", "lake"]) (home ++ [".toolchain", "bin", "lake"]) := by
  intro W _
  refine ⟨[], [], ?_, ?_, ?_⟩
  · simp [effective, currentPolicy, hiddenDirs, home, research, mathlibProj, Mount.tgt]
  · simp
  · exact Or.inl ⟨_, rfl⟩

theorem claim_b : ∀ (W : Path) (stateDirs : List Path) (canWrite : Path → Prop) (p hp : Path),
    WritesHost (fixedPolicy W stateDirs) canWrite p hp →
      W <+: hp ∨ ∃ d ∈ stateDirs, d <+: hp := by
  intro W stateDirs canWrite p hp ⟨src, t, he, hhp, _⟩
  obtain ⟨hmem, _⟩ := eff_mem he
  simp [fixedPolicy] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨hd, rfl⟩
  · exact Or.inl ⟨_, hhp.symm⟩
  · exact Or.inr ⟨_, hd, _, hhp.symm⟩

theorem claim_c : ∀ (W p hp H : Path), ["var", "tmp"] <+: W → H ∈ hiddenDirs → H <+: hp →
    ReadsHost (currentPolicy W) p hp → mathlibProj <+: hp := by
  intro W p hp H hW hH hHp ⟨src, t, m, he, hhp⟩
  rw [cur_split] at he
  obtain ⟨hmem, _⟩ := eff_mem he
  rw [List.mem_append] at hmem
  rcases hmem with h0 | h1
  · simp only [List.mem_singleton, Mount.bind.injEq] at h0
    obtain ⟨rfl, rfl, rfl⟩ := h0
    simp only [List.nil_append, List.length_nil, List.drop_zero] at hhp
    subst hhp
    have h2 := eff_tail he (x := .tmpfs H) (by simp [hH]) hHp
    simp at h2
  · simp at h1
    rcases h1 with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
    · exfalso
      have hv : ["var", "tmp"] <+: hp := hW.trans ⟨_, hhp.symm⟩
      obtain ⟨as, has | has⟩ := hidden_head H hH
      · subst has
        exact absurd (head_eq hHp hv) (by decide)
      · subst has
        exact absurd (head_eq hHp hv) (by decide)
    · exact ⟨_, hhp.symm⟩

theorem claim : Claim := ⟨claim_a, claim_b, claim_c⟩

theorem witness : Witness := by
  unfold Witness
  constructor
  · refine ⟨["var", "tmp", "job-x"], ["var", "tmp", "work"], ?_, ?_, trivial⟩
    · simp [effective, fixedPolicy, hiddenDirs, home, research, mathlibProj, Mount.tgt]
    · simp
  · refine ⟨mathlibProj, mathlibProj, .ro, ?_, ?_⟩
    · simp [effective, fixedPolicy, hiddenDirs, home, research, mathlibProj, Mount.tgt]
    · simp
