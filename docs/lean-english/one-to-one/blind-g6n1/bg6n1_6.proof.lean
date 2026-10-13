open ControlStack.AuthInstances ControlStack.SC25 ControlStack.AuthenticatedLog

open ControlStack.Authenticated

def guardedStep (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (io : ℕ × Op) : St :=
  if Authentic claim25 io then step R h cls full s io.2 else s

theorem auth_fold (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List (ℕ × Op)) :
    authRun (step R h cls full) claim25 s ops = ops.foldl (guardedStep R h cls) s := rfl

theorem occurrence {S I X : Type} (st : S → I → S) (rec : S → List X) (P : I → X → Prop)
    (delta : ∀ s io x, x ∈ rec (st s io) → x ∈ rec s ∨
      (P io x ∧ rec (st s io) = rec s ++ [x]))
    (ops : List I) (s : S) (x : X) (hx : x ∈ rec (ops.foldl st s)) :
    x ∈ rec s ∨ ∃ before io after,
      ops = before ++ (io :: after) ∧ P io x ∧
      rec (st (before.foldl st s) io) = rec (before.foldl st s) ++ [x] := by
  induction ops generalizing s with
  | nil => exact Or.inl hx
  | cons io ops ih =>
    rcases ih (st s io) hx with hx | ⟨before, j, after, he, hp, hd⟩
    · rcases delta s io x hx with hx | ⟨hp, hd⟩
      · exact Or.inl hx
      · exact Or.inr ⟨[], io, ops, rfl, hp, hd⟩
    · refine Or.inr ⟨io :: before, j, after, ?_, hp, hd⟩
      simp only [List.cons_append, he]

theorem verdict_delta (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool)
    (s : St) (io : ℕ × Op) (v : Verdict)
    (hv : v ∈ (guardedStep R h cls s io).verdicts) :
    v ∈ s.verdicts ∨
      ((io.2 = .audit io.1 v.id v.pass ∧ v.by_ = some io.1 ∧ io.1 ∈ R.auditors) ∧
        (guardedStep R h cls s io).verdicts = s.verdicts ++ [v]) := by
  rcases io with ⟨issuer, o⟩
  unfold guardedStep at hv ⊢
  split_ifs with ha
  · cases o <;> simp only [step] at hv ⊢ <;> (repeat' split at hv) <;> simp_all [full, Authentic, claim25]
    rcases hv with hv | rfl <;> simp_all [Authentic, claim25]
  · exact Or.inl (by simpa only [if_neg ha] using hv)

theorem approval_delta (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool)
    (s : St) (io : ℕ × Op) (ap : Appr)
    (hv : ap ∈ (guardedStep R h cls s io).approvals) :
    ap ∈ s.approvals ∨
      ((io.2 = .approve io.1 ap.id ∧ io.1 = ap.approver ∧ io.1 ∈ R.approvers) ∧
        (guardedStep R h cls s io).approvals = s.approvals ++ [ap]) := by
  rcases io with ⟨issuer, o⟩
  unfold guardedStep at hv ⊢
  split_ifs with ha
  · cases o <;> simp only [step] at hv ⊢ <;> (repeat' split at hv) <;> simp_all [full, Authentic, claim25]
    rcases hv with hv | rfl <;> simp_all [Authentic, claim25]
  · exact Or.inl (by simpa only [if_neg ha] using hv)

theorem forward (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (U : List ℕ) (ops : List (ℕ × Op)) :
    Back R h cls U ops → Orig R h cls U ops := by
  rintro ⟨hg, hv, hap⟩
  refine ⟨hg, ?_, ?_⟩
  · intro v hmem
    obtain ⟨a, before, after, hby, ha, hU, he, hd⟩ := hv v hmem
    exact ⟨a, .audit a v.id v.pass, by rw [he]; simp, hU, rfl, hby, ha⟩
  · intro ap hmem
    obtain ⟨before, after, ha, hU, he, hd⟩ := hap ap hmem
    exact ⟨ap.approver, .approve ap.approver ap.id, by rw [he]; simp, hU, rfl, rfl, ha⟩

theorem backward (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (U : List ℕ) (ops : List (ℕ × Op)) :
    Orig R h cls U ops → Back R h cls U ops := by
  rintro ⟨hg, hv, hap⟩
  refine ⟨hg, ?_, ?_⟩
  · intro v hmem
    obtain ⟨c, o, hm, hU, ho, hby, hc⟩ := hv v hmem
    rw [auth_fold] at hmem
    rcases occurrence (guardedStep R h cls) St.verdicts
        (fun io v => io.2 = .audit io.1 v.id v.pass ∧ v.by_ = some io.1 ∧ io.1 ∈ R.auditors)
        (verdict_delta R h cls) ops init v hmem with hempty | ⟨before, ⟨a, j⟩, after, he, hj, hd⟩
    · simp [init] at hempty
    · rcases hj with ⟨hj, hby', ha⟩
      dsimp only at hj hby' ha
      have hac : a = c := Option.some.inj (hby'.symm.trans hby)
      subst c
      subst j
      refine ⟨a, before, after, hby', ha, hU, he, ?_⟩
      simpa [auth_fold, guardedStep, Authentic, claim25] using hd
  · intro ap hmem
    obtain ⟨c, o, hm, hU, ho, hc, hrole⟩ := hap ap hmem
    rw [auth_fold] at hmem
    rcases occurrence (guardedStep R h cls) St.approvals
        (fun io ap => io.2 = .approve io.1 ap.id ∧ io.1 = ap.approver ∧ io.1 ∈ R.approvers)
        (approval_delta R h cls) ops init ap hmem with hempty | ⟨before, ⟨a, j⟩, after, he, hj, hd⟩
    · simp [init] at hempty
    · rcases hj with ⟨hj, ha, hrole'⟩
      dsimp only at hj ha hrole'
      subst j
      refine ⟨before, after, hc ▸ hrole, hc ▸ hU, ?_, ?_⟩
      · simpa only [ha] using he
      · simpa [auth_fold, guardedStep, Authentic, claim25, ha] using hd

theorem claim : Claim := by
  refine ⟨rfl, ?_⟩
  intro R h cls U ops hUv hUa
  exact ⟨forward R h cls U ops, backward R h cls U ops⟩

theorem witness : Witness := by
  unfold Witness
  decide
