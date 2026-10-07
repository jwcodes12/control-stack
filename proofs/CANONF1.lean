
/-! ## Renaming: composition, congruence, occurrences, evaluation -/

theorem k_aren_comp (f g : ℕ → ℕ) (a : AExp) : (a.rename f).rename g = a.rename (g ∘ f) := by
  induction a <;> simp_all [AExp.rename]

theorem k_bren_comp (f g : ℕ → ℕ) (b : BExp) : (b.rename f).rename g = b.rename (g ∘ f) := by
  induction b <;> simp_all [BExp.rename, k_aren_comp]

theorem k_sren_comp (f g : ℕ → ℕ) (s : Stmt) : (s.rename f).rename g = s.rename (g ∘ f) := by
  induction s <;> simp_all [Stmt.rename, k_bren_comp, k_aren_comp]

theorem k_pren_comp (f g : ℕ → ℕ) (p : Prog) : (p.rename f).rename g = p.rename (g ∘ f) := by
  simp [Prog.rename, k_sren_comp, k_aren_comp]

theorem k_aocc_ren (f : ℕ → ℕ) (a : AExp) : (a.rename f).occ = a.occ.map f := by
  induction a <;> simp_all [AExp.rename, AExp.occ]

theorem k_bocc_ren (f : ℕ → ℕ) (b : BExp) : (b.rename f).occ = b.occ.map f := by
  induction b <;> simp_all [BExp.rename, BExp.occ, k_aocc_ren]

theorem k_socc_ren (f : ℕ → ℕ) (s : Stmt) : (s.rename f).occ = s.occ.map f := by
  induction s <;> simp_all [Stmt.rename, Stmt.occ, k_bocc_ren, k_aocc_ren]

theorem k_pocc_ren (f : ℕ → ℕ) (p : Prog) : (p.rename f).occ = p.occ.map f := by
  simp [Prog.rename, Prog.occ, k_socc_ren, k_aocc_ren]

theorem k_aren_congr {f g : ℕ → ℕ} (a : AExp) (h : ∀ v ∈ a.occ, f v = g v) :
    a.rename f = a.rename g := by
  induction a with
  | lit n => rfl
  | var v => simp [AExp.rename, h v (by simp [AExp.occ])]
  | add a b iha ihb =>
    simp only [AExp.occ, List.mem_append] at h
    simp only [AExp.rename, iha (fun v hv => h v (Or.inl hv)), ihb (fun v hv => h v (Or.inr hv))]
  | sub a b iha ihb =>
    simp only [AExp.occ, List.mem_append] at h
    simp only [AExp.rename, iha (fun v hv => h v (Or.inl hv)), ihb (fun v hv => h v (Or.inr hv))]
  | mul a b iha ihb =>
    simp only [AExp.occ, List.mem_append] at h
    simp only [AExp.rename, iha (fun v hv => h v (Or.inl hv)), ihb (fun v hv => h v (Or.inr hv))]

theorem k_bren_congr {f g : ℕ → ℕ} (b : BExp) (h : ∀ v ∈ b.occ, f v = g v) :
    b.rename f = b.rename g := by
  induction b with
  | lt a c =>
    simp only [BExp.occ, List.mem_append] at h
    simp only [BExp.rename, k_aren_congr a (fun v hv => h v (Or.inl hv)),
      k_aren_congr c (fun v hv => h v (Or.inr hv))]
  | eq a c =>
    simp only [BExp.occ, List.mem_append] at h
    simp only [BExp.rename, k_aren_congr a (fun v hv => h v (Or.inl hv)),
      k_aren_congr c (fun v hv => h v (Or.inr hv))]
  | not b ih =>
    simp only [BExp.occ] at h
    simp only [BExp.rename, ih h]
  | and b c ihb ihc =>
    simp only [BExp.occ, List.mem_append] at h
    simp only [BExp.rename, ihb (fun v hv => h v (Or.inl hv)), ihc (fun v hv => h v (Or.inr hv))]

theorem k_sren_congr {f g : ℕ → ℕ} (s : Stmt) (h : ∀ v ∈ s.occ, f v = g v) :
    s.rename f = s.rename g := by
  induction s with
  | skip => rfl
  | assign v a =>
    simp only [Stmt.occ, List.mem_cons] at h
    simp only [Stmt.rename, h v (Or.inl rfl), k_aren_congr a (fun w hw => h w (Or.inr hw))]
  | seq s t ihs iht =>
    simp only [Stmt.occ, List.mem_append] at h
    simp only [Stmt.rename, ihs (fun v hv => h v (Or.inl hv)), iht (fun v hv => h v (Or.inr hv))]
  | ite b s t ihs iht =>
    simp only [Stmt.occ, List.mem_append] at h
    simp only [Stmt.rename, k_bren_congr b (fun v hv => h v (Or.inl (Or.inl hv))),
      ihs (fun v hv => h v (Or.inl (Or.inr hv))), iht (fun v hv => h v (Or.inr hv))]
  | «while» b s ih =>
    simp only [Stmt.occ, List.mem_append] at h
    simp only [Stmt.rename, k_bren_congr b (fun v hv => h v (Or.inl hv)),
      ih (fun v hv => h v (Or.inr hv))]
  | cfor i c st body ihi ihst ihb =>
    simp only [Stmt.occ, List.mem_append] at h
    simp only [Stmt.rename, ihi (fun v hv => h v (Or.inl (Or.inl (Or.inl hv)))),
      k_bren_congr c (fun v hv => h v (Or.inl (Or.inl (Or.inr hv)))),
      ihst (fun v hv => h v (Or.inl (Or.inr hv))), ihb (fun v hv => h v (Or.inr hv))]

theorem k_pren_congr {f g : ℕ → ℕ} (p : Prog) (h : ∀ v ∈ p.occ, f v = g v) :
    p.rename f = p.rename g := by
  simp only [Prog.occ, List.mem_append] at h
  simp only [Prog.rename, k_sren_congr p.body (fun v hv => h v (Or.inl hv)),
    k_aren_congr p.ret (fun v hv => h v (Or.inr hv))]

theorem k_pren_id (p : Prog) : p.rename id = p := by
  have ha : ∀ a : AExp, a.rename id = a := by
    intro a; induction a <;> simp_all [AExp.rename]
  have hb : ∀ b : BExp, b.rename id = b := by
    intro b; induction b <;> simp_all [BExp.rename]
  have hs : ∀ s : Stmt, s.rename id = s := by
    intro s; induction s <;> simp_all [Stmt.rename]
  cases p
  simp [Prog.rename, ha, hs]

theorem k_aeval_ren {f : ℕ → ℕ} {σ τ : State} (a : AExp) (h : ∀ v ∈ a.occ, τ (f v) = σ v) :
    (a.rename f).eval τ = a.eval σ := by
  induction a with
  | lit n => rfl
  | var v => exact h v (by simp [AExp.occ])
  | add a b iha ihb =>
    simp only [AExp.occ, List.mem_append] at h
    simp only [AExp.rename, AExp.eval, iha (fun v hv => h v (Or.inl hv)),
      ihb (fun v hv => h v (Or.inr hv))]
  | sub a b iha ihb =>
    simp only [AExp.occ, List.mem_append] at h
    simp only [AExp.rename, AExp.eval, iha (fun v hv => h v (Or.inl hv)),
      ihb (fun v hv => h v (Or.inr hv))]
  | mul a b iha ihb =>
    simp only [AExp.occ, List.mem_append] at h
    simp only [AExp.rename, AExp.eval, iha (fun v hv => h v (Or.inl hv)),
      ihb (fun v hv => h v (Or.inr hv))]

theorem k_beval_ren {f : ℕ → ℕ} {σ τ : State} (b : BExp) (h : ∀ v ∈ b.occ, τ (f v) = σ v) :
    (b.rename f).eval τ = b.eval σ := by
  induction b with
  | lt a c =>
    simp only [BExp.occ, List.mem_append] at h
    simp only [BExp.rename, BExp.eval, k_aeval_ren a (fun v hv => h v (Or.inl hv)),
      k_aeval_ren c (fun v hv => h v (Or.inr hv))]
  | eq a c =>
    simp only [BExp.occ, List.mem_append] at h
    simp only [BExp.rename, BExp.eval, k_aeval_ren a (fun v hv => h v (Or.inl hv)),
      k_aeval_ren c (fun v hv => h v (Or.inr hv))]
  | not b ih =>
    simp only [BExp.occ] at h
    simp only [BExp.rename, BExp.eval, ih h]
  | and b c ihb ihc =>
    simp only [BExp.occ, List.mem_append] at h
    simp only [BExp.rename, BExp.eval, ihb (fun v hv => h v (Or.inl hv)),
      ihc (fun v hv => h v (Or.inr hv))]

/-! ## Semantics: equivalence of statements -/

def KSEq (s t : Stmt) : Prop := ∀ σ σ', Exec s σ σ' ↔ Exec t σ σ'

theorem k_exec_seq_iff {s t : Stmt} {σ σ'' : State} :
    Exec (.seq s t) σ σ'' ↔ ∃ σ', Exec s σ σ' ∧ Exec t σ' σ'' := by
  constructor
  · intro h
    cases h with
    | seq _ _ _ σ' _ h1 h2 => exact ⟨σ', h1, h2⟩
  · rintro ⟨σ', h1, h2⟩
    exact Exec.seq _ _ _ _ _ h1 h2

theorem k_exec_ite_iff {b : BExp} {s t : Stmt} {σ σ' : State} :
    Exec (.ite b s t) σ σ' ↔ (b.eval σ = true ∧ Exec s σ σ') ∨ (b.eval σ = false ∧ Exec t σ σ') := by
  constructor
  · intro h
    cases h with
    | iteT _ _ _ _ _ hb h1 => exact Or.inl ⟨hb, h1⟩
    | iteF _ _ _ _ _ hb h1 => exact Or.inr ⟨hb, h1⟩
  · rintro (⟨hb, h1⟩ | ⟨hb, h1⟩)
    · exact Exec.iteT _ _ _ _ _ hb h1
    · exact Exec.iteF _ _ _ _ _ hb h1

theorem k_exec_cfor_iff {i : Stmt} {c : BExp} {st body : Stmt} {σ σ' : State} :
    Exec (.cfor i c st body) σ σ' ↔ Exec (.seq i (.while c (.seq body st))) σ σ' := by
  constructor
  · intro h
    cases h with
    | cfor _ _ _ _ _ _ h1 => exact h1
  · intro h
    exact Exec.cfor _ _ _ _ _ _ h

theorem k_while_mono {b : BExp} {s s' : Stmt} (h : ∀ σ σ', Exec s σ σ' → Exec s' σ σ') :
    ∀ σ σ', Exec (.while b s) σ σ' → Exec (.while b s') σ σ' := by
  intro σ σ' hw
  generalize hW : Stmt.while b s = W at hw
  induction hw with
  | whileT b0 s0 σ1 σ2 σ3 hc hs _ _ ih2 =>
    cases hW
    exact Exec.whileT _ _ _ _ _ hc (h _ _ hs) (ih2 rfl)
  | whileF b0 s0 σ1 hc =>
    cases hW
    exact Exec.whileF _ _ _ hc
  | skip => cases hW
  | assign => cases hW
  | seq => cases hW
  | iteT => cases hW
  | iteF => cases hW
  | cfor => cases hW

theorem k_seq_congr {s s' t t' : Stmt} (h1 : KSEq s s') (h2 : KSEq t t') :
    KSEq (.seq s t) (.seq s' t') := by
  unfold KSEq at *
  intro σ σ'
  simp only [k_exec_seq_iff, h1, h2]

theorem k_ite_congr {b : BExp} {s s' t t' : Stmt} (h1 : KSEq s s') (h2 : KSEq t t') :
    KSEq (.ite b s t) (.ite b s' t') := by
  unfold KSEq at *
  intro σ σ'
  simp only [k_exec_ite_iff, h1, h2]

theorem k_while_congr {b : BExp} {s s' : Stmt} (h : KSEq s s') :
    KSEq (.while b s) (.while b s') := by
  intro σ σ'
  exact ⟨k_while_mono (fun _ _ hh => (h _ _).1 hh) σ σ', k_while_mono (fun _ _ hh => (h _ _).2 hh) σ σ'⟩

theorem k_cfor_congr {i i' : Stmt} {c : BExp} {st st' b b' : Stmt} (hi : KSEq i i')
    (hst : KSEq st st') (hb : KSEq b b') : KSEq (.cfor i c st b) (.cfor i' c st' b') := by
  intro σ σ'
  rw [k_exec_cfor_iff, k_exec_cfor_iff]
  exact k_seq_congr hi (k_while_congr (k_seq_congr hb hst)) σ σ'

theorem k_sEq_refl (s : Stmt) : KSEq s s := fun _ _ => Iff.rfl

theorem k_forstep_sEq {s t : Stmt} (h : ForStep s t) : KSEq s t := by
  induction h with
  | here i c st body => intro σ σ'; exact k_exec_cfor_iff
  | assoc s t u =>
    intro σ σ'
    simp only [k_exec_seq_iff]
    constructor
    · rintro ⟨_, ⟨_, h1, h2⟩, h3⟩
      exact ⟨_, h1, _, h2, h3⟩
    · rintro ⟨_, h1, _, h2, h3⟩
      exact ⟨_, ⟨_, h1, h2⟩, h3⟩
  | seqL s s' t _ ih => exact k_seq_congr ih (k_sEq_refl _)
  | seqR s t t' _ ih => exact k_seq_congr (k_sEq_refl _) ih
  | iteL b s s' t _ ih => exact k_ite_congr ih (k_sEq_refl _)
  | iteR b s t t' _ ih => exact k_ite_congr (k_sEq_refl _) ih
  | whileB b s s' _ ih => exact k_while_congr ih
  | forI i i' c st body _ ih => exact k_cfor_congr ih (k_sEq_refl _) (k_sEq_refl _)
  | forSt i c st st' body _ ih => exact k_cfor_congr (k_sEq_refl _) ih (k_sEq_refl _)
  | forBody i c st body body' _ ih => exact k_cfor_congr (k_sEq_refl _) (k_sEq_refl _) ih

theorem k_eqv_sEq {s t : Stmt} (h : Relation.EqvGen ForStep s t) : KSEq s t := by
  induction h with
  | rel x y hxy => exact k_forstep_sEq hxy
  | refl x => exact k_sEq_refl x
  | symm x y _ ih => exact fun σ σ' => (ih σ σ').symm
  | trans x y z _ _ ih1 ih2 => exact fun σ σ' => (ih1 σ σ').trans (ih2 σ σ')

/-! ## Renaming preserves runs -/

theorem k_exec_rename {f : ℕ → ℕ} {V : Set ℕ} (hf : Set.InjOn f V) {s : Stmt} {σ σ' : State}
    (h : Exec s σ σ') : (∀ v ∈ s.occ, v ∈ V) → ∀ τ : State, (∀ v ∈ V, τ (f v) = σ v) →
    ∃ τ', Exec (s.rename f) τ τ' ∧ ∀ v ∈ V, τ' (f v) = σ' v := by
  induction h with
  | skip σ => intro _ τ hτ; exact ⟨τ, Exec.skip _, hτ⟩
  | assign v a σ =>
    intro hocc τ hτ
    refine ⟨_, Exec.assign _ _ _, ?_⟩
    intro w hw
    have hv : v ∈ V := hocc v (by simp [Stmt.occ])
    have ha : (a.rename f).eval τ = a.eval σ :=
      k_aeval_ren a (fun u hu => hτ u (hocc u (by simp [Stmt.occ, hu])))
    by_cases hwv : w = v
    · subst hwv
      simp [ha]
    · have hne : f w ≠ f v := fun e => hwv (hf hw hv e)
      simp [Function.update, hwv, hne, hτ w hw]
  | seq s t σ1 σ2 σ3 _ _ ih1 ih2 =>
    intro hocc τ hτ
    obtain ⟨τ2, e1, r1⟩ := ih1 (fun v hv => hocc v (by simp [Stmt.occ, hv])) τ hτ
    obtain ⟨τ3, e2, r2⟩ := ih2 (fun v hv => hocc v (by simp [Stmt.occ, hv])) τ2 r1
    exact ⟨τ3, Exec.seq _ _ _ _ _ e1 e2, r2⟩
  | iteT b s t σ1 σ2 hb _ ih =>
    intro hocc τ hτ
    obtain ⟨τ2, e1, r1⟩ := ih (fun v hv => hocc v (by simp [Stmt.occ, hv])) τ hτ
    refine ⟨τ2, Exec.iteT _ _ _ _ _ ?_ e1, r1⟩
    rw [k_beval_ren b (fun u hu => hτ u (hocc u (by simp [Stmt.occ, hu])))]
    exact hb
  | iteF b s t σ1 σ2 hb _ ih =>
    intro hocc τ hτ
    obtain ⟨τ2, e1, r1⟩ := ih (fun v hv => hocc v (by simp [Stmt.occ, hv])) τ hτ
    refine ⟨τ2, Exec.iteF _ _ _ _ _ ?_ e1, r1⟩
    rw [k_beval_ren b (fun u hu => hτ u (hocc u (by simp [Stmt.occ, hu])))]
    exact hb
  | whileT b s σ1 σ2 σ3 hb _ _ ih1 ih2 =>
    intro hocc τ hτ
    obtain ⟨τ2, e1, r1⟩ := ih1 (fun v hv => hocc v (by simp [Stmt.occ, hv])) τ hτ
    obtain ⟨τ3, e2, r2⟩ := ih2 hocc τ2 r1
    refine ⟨τ3, Exec.whileT _ _ _ _ _ ?_ e1 e2, r2⟩
    rw [k_beval_ren b (fun u hu => hτ u (hocc u (by simp [Stmt.occ, hu])))]
    exact hb
  | whileF b s σ hb =>
    intro hocc τ hτ
    refine ⟨τ, Exec.whileF _ _ _ ?_, hτ⟩
    rw [k_beval_ren b (fun u hu => hτ u (hocc u (by simp [Stmt.occ, hu])))]
    exact hb
  | cfor i c st body σ1 σ2 _ ih =>
    intro hocc τ hτ
    obtain ⟨τ', e, r⟩ := ih (fun v hv => hocc v (by simp [Stmt.occ] at hv ⊢; tauto)) τ hτ
    exact ⟨τ', Exec.cfor _ _ _ _ _ _ e, r⟩

theorem k_runs_rename {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) {ins : List ℤ} {out : ℤ}
    (h : Runs p ins out) : Runs (p.rename f) ins out := by
  obtain ⟨hlen, σ', hex, hret⟩ := h
  have hinj : Set.InjOn f {v | v ∈ p.occ} := fun v hv w hw e => hA.2.2 v hv w hw e
  obtain ⟨τ', e, r⟩ := k_exec_rename hinj hex (fun v hv => by simp [Prog.occ, hv])
    (initState p.nparams ins) (by
      intro v hv
      simp only [initState]
      by_cases hlt : v < p.nparams
      · rw [hA.1 v hv hlt]
      · have := hA.2.1 v hv (by omega)
        simp [hlt, show ¬ f v < p.nparams by omega])
  refine ⟨hlen, τ', e, ?_⟩
  show (p.ret.rename f).eval τ' = out
  rw [k_aeval_ren p.ret (fun v hv => r v (by simp [Prog.occ, hv]))]
  exact hret

theorem k_ren_inverse {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) :
    ∃ g, Admissible g (p.rename f) ∧ (p.rename f).rename g = p := by
  have hinj : Set.InjOn f {v | v ∈ p.occ} := fun v hv w hw e => hA.2.2 v hv w hw e
  have hg : ∀ v ∈ p.occ, Function.invFunOn f {v | v ∈ p.occ} (f v) = v :=
    fun v hv => hinj.leftInvOn_invFunOn hv
  refine ⟨Function.invFunOn f {v | v ∈ p.occ}, ?_, ?_⟩
  · have hocc : (p.rename f).occ = p.occ.map f := k_pocc_ren f p
    have hn : (p.rename f).nparams = p.nparams := rfl
    refine ⟨?_, ?_, ?_⟩
    · intro w hw hlt
      rw [hocc] at hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      rw [hn] at hlt
      have hvlt : v < p.nparams := by
        by_contra hc
        have := hA.2.1 v hv (by omega)
        omega
      rw [hg v hv, hA.1 v hv hvlt]
    · intro w hw hle
      rw [hocc] at hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      rw [hn] at hle ⊢
      rw [hg v hv]
      by_contra hc
      have := hA.1 v hv (by omega)
      omega
    · intro w hw w' hw' e
      rw [hocc] at hw hw'
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      obtain ⟨v', hv', rfl⟩ := List.mem_map.1 hw'
      rw [hg v hv, hg v' hv'] at e
      rw [e]
  · rw [k_pren_comp]
    conv_rhs => rw [← k_pren_id p]
    apply k_pren_congr
    intro v hv
    exact hg v hv

theorem k_runs_rename_iff {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) (ins : List ℤ) (out : ℤ) :
    Runs p ins out ↔ Runs (p.rename f) ins out := by
  constructor
  · exact k_runs_rename hA
  · intro h
    obtain ⟨g, hg, he⟩ := k_ren_inverse hA
    have := k_runs_rename hg h
    rwa [he] at this

/-! ## The normal-form map `FF = flatten ∘ desugar` -/

def KFF (s : Stmt) : Stmt := flatten (desugar s)

theorem k_append_assoc (a b c : Stmt) : (a.append b).append c = a.append (b.append c) := by
  induction a with
  | seq x y _ ih =>
    show Stmt.seq x ((y.append b).append c) = Stmt.seq x (y.append (b.append c))
    rw [ih]
  | _ => rfl

theorem k_FF_step {s t : Stmt} (h : ForStep s t) : KFF s = KFF t := by
  induction h with
  | here i c st body => rfl
  | assoc s t u => exact k_append_assoc _ _ _
  | seqL s s' t _ ih =>
    simp only [KFF, desugar, flatten] at ih ⊢
    rw [ih]
  | seqR s t t' _ ih =>
    simp only [KFF, desugar, flatten] at ih ⊢
    rw [ih]
  | iteL b s s' t _ ih =>
    simp only [KFF, desugar, flatten] at ih ⊢
    rw [ih]
  | iteR b s t t' _ ih =>
    simp only [KFF, desugar, flatten] at ih ⊢
    rw [ih]
  | whileB b s s' _ ih =>
    simp only [KFF, desugar, flatten] at ih ⊢
    rw [ih]
  | forI i i' c st body _ ih =>
    simp only [KFF, desugar, flatten] at ih ⊢
    rw [ih]
  | forSt i c st st' body _ ih =>
    simp only [KFF, desugar, flatten] at ih ⊢
    rw [ih]
  | forBody i c st body body' _ ih =>
    simp only [KFF, desugar, flatten] at ih ⊢
    rw [ih]

theorem k_FF_eqv {s t : Stmt} (h : Relation.EqvGen ForStep s t) : KFF s = KFF t := by
  induction h with
  | rel x y hxy => exact k_FF_step hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem k_desugar_ren (f : ℕ → ℕ) (s : Stmt) : desugar (s.rename f) = (desugar s).rename f := by
  induction s <;> simp_all [desugar, Stmt.rename]

theorem k_append_ren (f : ℕ → ℕ) (a b : Stmt) :
    (a.append b).rename f = (a.rename f).append (b.rename f) := by
  induction a with
  | seq x y _ ih =>
    show Stmt.seq (x.rename f) ((y.append b).rename f) =
      Stmt.seq (x.rename f) ((y.rename f).append (b.rename f))
    rw [ih]
  | _ => rfl

theorem k_flatten_ren (f : ℕ → ℕ) (s : Stmt) : flatten (s.rename f) = (flatten s).rename f := by
  induction s <;> simp_all [flatten, Stmt.rename, k_append_ren]

theorem k_FF_ren (f : ℕ → ℕ) (s : Stmt) : KFF (s.rename f) = (KFF s).rename f := by
  simp [KFF, k_desugar_ren, k_flatten_ren]

theorem k_occ_append (a b : Stmt) : (a.append b).occ = a.occ ++ b.occ := by
  induction a with
  | seq x y _ ih =>
    show x.occ ++ (y.append b).occ = (x.occ ++ y.occ) ++ b.occ
    rw [ih, List.append_assoc]
  | _ => rfl

theorem k_occ_flatten (s : Stmt) : (flatten s).occ = s.occ := by
  induction s <;> simp_all [flatten, Stmt.occ, k_occ_append]

theorem k_mem_occ_desugar (s : Stmt) (v : ℕ) : v ∈ (desugar s).occ ↔ v ∈ s.occ := by
  induction s with
  | skip => rfl
  | assign w a => rfl
  | seq s t ihs iht => simp only [desugar, Stmt.occ, List.mem_append, ihs, iht]
  | ite b s t ihs iht => simp only [desugar, Stmt.occ, List.mem_append, ihs, iht]
  | «while» b s ih => simp only [desugar, Stmt.occ, List.mem_append, ih]
  | cfor i c st body ihi ihc ihb =>
    simp only [desugar, Stmt.occ, List.mem_append, ihi, ihc, ihb]
    tauto

theorem k_mem_occ_FF (s : Stmt) (v : ℕ) : v ∈ (KFF s).occ ↔ v ∈ s.occ := by
  simp only [KFF, k_occ_flatten, k_mem_occ_desugar]

/-! ## firstOcc -/

def kstep (acc : List ℕ) (v : ℕ) : List ℕ := if v ∈ acc then acc else acc ++ [v]

theorem k_firstOcc_eq (l : List ℕ) : firstOcc l = l.foldl kstep [] := rfl

theorem k_mem_foldl (l acc : List ℕ) (v : ℕ) : v ∈ l.foldl kstep acc ↔ v ∈ acc ∨ v ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    unfold kstep
    by_cases h : a ∈ acc
    · simp only [h, ite_true, List.mem_cons]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | rfl | h1)
        · exact Or.inl h1
        · exact Or.inl h
        · exact Or.inr h1
    · simp only [h, ite_false, List.mem_cons, List.mem_append]
      tauto

theorem k_mem_firstOcc (l : List ℕ) (v : ℕ) : v ∈ firstOcc l ↔ v ∈ l := by
  rw [k_firstOcc_eq, k_mem_foldl]
  simp

theorem k_foldl_map {f : ℕ → ℕ} {S : Set ℕ} (hf : Set.InjOn f S) (l acc : List ℕ)
    (hl : ∀ v ∈ l, v ∈ S) (hacc : ∀ v ∈ acc, v ∈ S) :
    (l.map f).foldl kstep (acc.map f) = (l.foldl kstep acc).map f := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.foldl_cons]
    have ha : a ∈ S := hl a (by simp)
    have key : kstep (acc.map f) (f a) = (kstep acc a).map f := by
      unfold kstep
      by_cases h : a ∈ acc
      · have : f a ∈ acc.map f := List.mem_map_of_mem h
        simp [h, this]
      · have : f a ∉ acc.map f := by
          intro hm
          obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
          exact h (hf (hacc b hb) ha e ▸ hb)
        simp [h, this]
    rw [key]
    apply ih
    · intro v hv
      exact hl v (by simp [hv])
    · intro v hv
      unfold kstep at hv
      by_cases h : a ∈ acc
      · rw [ite_eq_left h] at hv
        exact hacc v hv
      · rw [ite_eq_right h] at hv
        simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact hacc v hv
        · exact ha

theorem k_firstOcc_map {f : ℕ → ℕ} {S : Set ℕ} (hf : Set.InjOn f S) (l : List ℕ)
    (hl : ∀ v ∈ l, v ∈ S) : firstOcc (l.map f) = (firstOcc l).map f := by
  rw [k_firstOcc_eq, k_firstOcc_eq]
  have := k_foldl_map hf l [] hl (by simp)
  simpa using this

theorem k_idxOf_map {f : ℕ → ℕ} {S : Set ℕ} (hf : Set.InjOn f S) (v : ℕ) (hv : v ∈ S) :
    ∀ (L : List ℕ), (∀ w ∈ L, w ∈ S) → (L.map f).idxOf (f v) = L.idxOf v
  | [], _ => rfl
  | a :: L, hL => by
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons,
      k_idxOf_map hf v hv L (fun w hw => hL w (by simp [hw]))]
    have ha : a ∈ S := hL a (by simp)
    by_cases h : a = v
    · subst h
      simp
    · have : f a ≠ f v := fun e => h (hf ha hv e)
      simp [h, this]

/-! ## canon is invariant under steps -/

def kcanon' (d : Prog) : Prog := d.rename d.canonMap

theorem k_canon_eq (p : Prog) : canon p = kcanon' (desugarProg p) := rfl

theorem k_mem_locals {d : Prog} {v : ℕ} : v ∈ d.locals ↔ v ∈ d.occ ∧ d.nparams ≤ v := by
  simp [Prog.locals, List.mem_filter, k_mem_firstOcc]

theorem k_canonMap_ren {f : ℕ → ℕ} {d : Prog} (hA : Admissible f d) (v : ℕ) (hv : v ∈ d.occ) :
    (d.rename f).canonMap (f v) = d.canonMap v := by
  have hinj : Set.InjOn f {v | v ∈ d.occ} := fun a ha b hb e => hA.2.2 a ha b hb e
  have hfo : firstOcc (d.rename f).occ = (firstOcc d.occ).map f := by
    rw [k_pocc_ren]
    exact k_firstOcc_map hinj d.occ (fun w hw => hw)
  have hloc : (d.rename f).locals = d.locals.map f := by
    unfold Prog.locals
    rw [hfo, List.filter_map]
    congr 1
    apply List.filter_congr
    intro w hw
    have hw' : w ∈ d.occ := (k_mem_firstOcc _ _).1 hw
    show decide (d.nparams ≤ f w) = decide (d.nparams ≤ w)
    by_cases hlt : w < d.nparams
    · rw [hA.1 w hw' hlt]
    · have := hA.2.1 w hw' (by omega)
      simp only [decide_eq_decide]
      omega
  unfold Prog.canonMap
  show (if f v < d.nparams then f v else d.nparams + (d.rename f).locals.idxOf (f v)) =
    (if v < d.nparams then v else d.nparams + d.locals.idxOf v)
  by_cases hlt : v < d.nparams
  · rw [hA.1 v hv hlt]
    simp [hlt]
  · have h1 := hA.2.1 v hv (by omega)
    rw [ite_eq_right (by omega), ite_eq_right hlt, hloc, k_idxOf_map hinj v hv]
    intro w hw
    exact (k_mem_locals.1 hw).1

theorem k_canon'_ren {f : ℕ → ℕ} {d : Prog} (hA : Admissible f d) :
    kcanon' (d.rename f) = kcanon' d := by
  unfold kcanon'
  rw [k_pren_comp]
  apply k_pren_congr
  intro v hv
  exact k_canonMap_ren hA v hv

theorem k_desugarProg_ren (f : ℕ → ℕ) (p : Prog) :
    desugarProg (p.rename f) = (desugarProg p).rename f := by
  show (⟨p.nparams, KFF (p.body.rename f), p.ret.rename f⟩ : Prog) =
    ⟨p.nparams, (KFF p.body).rename f, p.ret.rename f⟩
  rw [k_FF_ren]

theorem k_adm_desugar {f : ℕ → ℕ} {p : Prog} (hA : Admissible f p) :
    Admissible f (desugarProg p) := by
  have hm : ∀ v, v ∈ (desugarProg p).occ ↔ v ∈ p.occ := by
    intro v
    show v ∈ (KFF p.body).occ ++ p.ret.occ ↔ v ∈ p.body.occ ++ p.ret.occ
    simp only [List.mem_append, k_mem_occ_FF]
  refine ⟨fun v hv => hA.1 v ((hm v).1 hv), fun v hv => hA.2.1 v ((hm v).1 hv),
    fun v hv w hw => hA.2.2 v ((hm v).1 hv) w ((hm w).1 hw)⟩

theorem k_canon_step {p q : Prog} (h : Step p q) : canon p = canon q := by
  cases h with
  | loop k body body' ret hs =>
    rw [k_canon_eq, k_canon_eq]
    show kcanon' ⟨k, KFF body, ret⟩ = kcanon' ⟨k, KFF body', ret⟩
    rw [k_FF_step hs]
  | ren f p hA =>
    rw [k_canon_eq, k_canon_eq, k_desugarProg_ren, k_canon'_ren (k_adm_desugar hA)]

theorem k_canon_syn {p q : Prog} (h : SynEquiv p q) : canon p = canon q := by
  induction h with
  | rel x y hxy => exact k_canon_step hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Every program is equivalent to its canonical form -/

theorem k_eqv_map {φ : Stmt → Stmt} (hφ : ∀ a b, ForStep a b → ForStep (φ a) (φ b)) {a b : Stmt}
    (h : Relation.EqvGen ForStep a b) : Relation.EqvGen ForStep (φ a) (φ b) := by
  induction h with
  | rel x y hxy => exact .rel _ _ (hφ _ _ hxy)
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

theorem k_eqv_seq {s s' t t' : Stmt} (h1 : Relation.EqvGen ForStep s s')
    (h2 : Relation.EqvGen ForStep t t') : Relation.EqvGen ForStep (.seq s t) (.seq s' t') :=
  .trans _ _ _ (k_eqv_map (φ := fun x => Stmt.seq x t) (fun _ _ h => ForStep.seqL _ _ _ h) h1)
    (k_eqv_map (φ := fun x => Stmt.seq s' x) (fun _ _ h => ForStep.seqR _ _ _ h) h2)

theorem k_eqv_ite {b : BExp} {s s' t t' : Stmt} (h1 : Relation.EqvGen ForStep s s')
    (h2 : Relation.EqvGen ForStep t t') : Relation.EqvGen ForStep (.ite b s t) (.ite b s' t') :=
  .trans _ _ _ (k_eqv_map (φ := fun x => Stmt.ite b x t) (fun _ _ h => ForStep.iteL _ _ _ _ h) h1)
    (k_eqv_map (φ := fun x => Stmt.ite b s' x) (fun _ _ h => ForStep.iteR _ _ _ _ h) h2)

theorem k_eqv_while {b : BExp} {s s' : Stmt} (h : Relation.EqvGen ForStep s s') :
    Relation.EqvGen ForStep (.while b s) (.while b s') :=
  k_eqv_map (φ := fun x => Stmt.while b x) (fun _ _ h => ForStep.whileB _ _ _ h) h

theorem k_eqv_cfor {i i' : Stmt} {c : BExp} {st st' body body' : Stmt}
    (hi : Relation.EqvGen ForStep i i') (hst : Relation.EqvGen ForStep st st')
    (hb : Relation.EqvGen ForStep body body') :
    Relation.EqvGen ForStep (.cfor i c st body) (.cfor i' c st' body') :=
  .trans _ _ _
    (k_eqv_map (φ := fun x => Stmt.cfor x c st body) (fun _ _ h => ForStep.forI _ _ _ _ _ h) hi)
    (.trans _ _ _
      (k_eqv_map (φ := fun x => Stmt.cfor i' c x body) (fun _ _ h => ForStep.forSt _ _ _ _ _ h) hst)
      (k_eqv_map (φ := fun x => Stmt.cfor i' c st' x) (fun _ _ h => ForStep.forBody _ _ _ _ _ h) hb))

theorem k_eqv_append (a b : Stmt) : Relation.EqvGen ForStep (.seq a b) (a.append b) := by
  induction a with
  | seq x y _ ih =>
    exact .trans _ _ _ (.rel _ _ (ForStep.assoc x y b)) (k_eqv_seq (.refl x) ih)
  | _ => exact .refl _

theorem k_eqv_flatten (s : Stmt) : Relation.EqvGen ForStep s (flatten s) := by
  induction s with
  | skip => exact .refl _
  | assign v a => exact .refl _
  | seq s t ihs iht => exact .trans _ _ _ (k_eqv_seq ihs iht) (k_eqv_append _ _)
  | ite b s t ihs iht => exact k_eqv_ite ihs iht
  | «while» b s ih => exact k_eqv_while ih
  | cfor i c st body ihi ihst ihb => exact k_eqv_cfor ihi ihst ihb

theorem k_eqv_desugar (s : Stmt) : Relation.EqvGen ForStep s (desugar s) := by
  induction s with
  | skip => exact .refl _
  | assign v a => exact .refl _
  | seq s t ihs iht => exact k_eqv_seq ihs iht
  | ite b s t ihs iht => exact k_eqv_ite ihs iht
  | «while» b s ih => exact k_eqv_while ih
  | cfor i c st body ihi ihst ihb =>
    exact .trans _ _ _ (.rel _ _ (ForStep.here i c st body))
      (k_eqv_seq ihi (k_eqv_while (k_eqv_seq ihb ihst)))

theorem k_eqv_FF (s : Stmt) : Relation.EqvGen ForStep s (KFF s) :=
  .trans _ _ _ (k_eqv_desugar s) (k_eqv_flatten _)

theorem k_lift {k : ℕ} {ret : AExp} {body body' : Stmt} (h : Relation.EqvGen ForStep body body') :
    SynEquiv ⟨k, body, ret⟩ ⟨k, body', ret⟩ := by
  induction h with
  | rel x y hxy => exact .rel _ _ (Step.loop _ _ _ _ hxy)
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

theorem k_adm_canonMap (d : Prog) : Admissible d.canonMap d := by
  refine ⟨?_, ?_, ?_⟩
  · intro v _ hlt
    simp [Prog.canonMap, hlt]
  · intro v _ hle
    simp [Prog.canonMap, show ¬ v < d.nparams by omega]
  · intro v hv w hw e
    unfold Prog.canonMap at e
    by_cases hv' : v < d.nparams <;> by_cases hw' : w < d.nparams <;>
      simp only [hv', hw', ite_true, ite_false] at e
    · exact e
    · omega
    · omega
    · have hvl : v ∈ d.locals := k_mem_locals.2 ⟨hv, by omega⟩
      exact (List.idxOf_inj hvl).1 (by omega)

theorem k_syn_canon (p : Prog) : SynEquiv p (canon p) := by
  have h1 : SynEquiv p (desugarProg p) := k_lift (k := p.nparams) (ret := p.ret) (k_eqv_FF p.body)
  exact .trans _ _ _ h1 (.rel _ _ (Step.ren _ _ (k_adm_canonMap (desugarProg p))))

theorem k_part2 (p q : Prog) : canon p = canon q ↔ SynEquiv p q := by
  constructor
  · intro h
    exact .trans _ _ _ (k_syn_canon p) (h ▸ .symm _ _ (k_syn_canon q))
  · exact k_canon_syn

/-! ## Semantics preservation -/

theorem k_runs_step {p q : Prog} (h : Step p q) (ins : List ℤ) (out : ℤ) :
    Runs p ins out ↔ Runs q ins out := by
  cases h with
  | loop k body body' ret hs =>
    have hE := k_forstep_sEq hs
    unfold Runs
    exact and_congr Iff.rfl (exists_congr fun σ' => and_congr (hE _ _) Iff.rfl)
  | ren f p hA => exact k_runs_rename_iff hA ins out

theorem k_runs_syn {p q : Prog} (h : SynEquiv p q) (ins : List ℤ) (out : ℤ) :
    Runs p ins out ↔ Runs q ins out := by
  induction h with
  | rel x y hxy => exact k_runs_step hxy ins out
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem k_part1 (p : Prog) (ins : List ℤ) (out : ℤ) : Runs (canon p) ins out ↔ Runs p ins out :=
  (k_runs_syn (k_syn_canon p) ins out).symm

theorem claim : Claim := by
  refine ⟨k_part1, k_part2, ?_⟩
  intro X _ prog PA PH H z
  by_cases hz : ∃ x0, canon (prog x0) = z
  · obtain ⟨x0, rfl⟩ := hz
    have key : ∀ x, canon (prog x) = canon (prog x0) ↔ SynEquiv (prog x) (prog x0) :=
      fun x => k_part2 _ _
    have := H (prog x0)
    classical
    convert this using 2
    · exact Finset.filter_congr (fun x _ => key x)
    · exact Finset.filter_congr (fun x _ => key x)
  · simp only [not_exists] at hz
    rw [Finset.filter_false_of_mem (fun x _ => hz x)]
    simp

theorem witness : Witness := by
  unfold Witness
  dsimp only
  refine ⟨by decide, ?_, by decide, ?_⟩
  · refine ⟨rfl, _, Exec.seq _ _ _ _ _ (Exec.assign _ _ _) (Exec.cfor _ _ _ _ _ _
      (Exec.seq _ _ _ _ _ (Exec.assign _ _ _)
        (Exec.whileT _ _ _ _ _ (by decide)
          (Exec.seq _ _ _ _ _ (Exec.assign _ _ _) (Exec.assign _ _ _))
          (Exec.whileT _ _ _ _ _ (by decide)
            (Exec.seq _ _ _ _ _ (Exec.assign _ _ _) (Exec.assign _ _ _))
            (Exec.whileT _ _ _ _ _ (by decide)
              (Exec.seq _ _ _ _ _ (Exec.assign _ _ _) (Exec.assign _ _ _))
              (Exec.whileF _ _ _ (by decide))))))), by decide⟩
  · intro h
    have hne := (k_part2 _ _).2 h
    revert hne
    decide
