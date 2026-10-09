/-
SC-25, content level: closes review finding 3 (REVIEW-PACKET-2026-10-09.md §0.3).

`SC25.sc25_safe` is digest-level and holds for EVERY digest function `h`: each executed content `c` had a passing
verdict whose recorded digest equals `h c`. With a non-injective `h` that verdict may have been issued for different
content (review witness W3). The SC-25 state records only the digest an auditor saw, so this file adds a GHOST run
that also records the content the auditor saw, without changing the model:

- `auditRec`: for an `audit` operation, exactly the record the model's `audit` branch appends, plus the audited
  content (same halt check, same `itemOf` lookup, same auditor check);
- `grun`: the model's `run` from `init` with `full`, paired with the list of ghost audit records;
  `grun_fst` proves its state component IS `SC25.run … full init ops`.

Results:
- `sc25_content_safe`: if `h` is injective on the contents that ever appear in the queue (every submitted or amended
  version; audited and executed contents are among them, `ghost_in_queue`, `executed_in_queue`), then every executed
  content was itself audited PASS by an auditor: some ghost record has that operation id, EXACTLY that content,
  pass = true and an auditor. This is the content-level analogue of `SC16.sc16_reviewed_content`.
- `digest_only_executes_unaudited`: without injectivity (constant `h`), content 50 executes while the only ghost audit
  record is of content 7 (review witness W3), so the injectivity premise cannot be dropped.

Not claimed: the timing ("at the moment it executed") is carried by `sc25_safe` (digest level), not restated here;
irreversibility/approval at content level is not restated (the same argument applies to approvals); the auditor
identity is the caller id (credential separation, see `Core/Authenticated.lean`). No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC25Audit

namespace ControlStack.SC25Content

open ControlStack.SC25

/-- a ghost audit record: (operation id, content the auditor saw, verdict, auditor) -/
abbrev ARec := ℕ × ℕ × Bool × ℕ

/-- the ghost record of one step: mirrors the `audit` branch of `SC25.step` under `full` -/
def auditRec (R : Roles) (s : St) : Op → List ARec
  | .audit c id p =>
    if s.halted = true ∧ full.haltCheck = true then []
    else match itemOf s id with
      | none => []
      | some it => if c ∈ R.auditors then [(id, it.content, p, c)] else []
  | _ => []

def gstep (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (sg : St × List ARec) (o : Op) : St × List ARec :=
  (step R h cls full sg.1 o, sg.2 ++ auditRec R sg.1 o)

/-- the model's run paired with the ghost audit records -/
def grun (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) : St × List ARec :=
  ops.foldl (gstep R h cls) (init, [])

theorem gfold_fst (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) (sg : St × List ARec) :
    (ops.foldl (gstep R h cls) sg).1 = run R h cls full sg.1 ops := by
  induction ops generalizing sg with
  | nil => rfl
  | cons o ops ih => simp only [List.foldl_cons]; rw [ih]; rfl

/-- the ghost run's state IS the model's run -/
theorem grun_fst (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) :
    (grun R h cls ops).1 = run R h cls full init ops := gfold_fst R h cls ops (init, [])

theorem mem_of_itemOf {s : St} {id : ℕ} {it : Item} (hi : itemOf s id = some it) : it ∈ s.queue :=
  List.mem_of_find?_eq_some hi

/-- the queue only grows (it keeps every submitted and amended version) -/
theorem queue_mono (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) :
    ∀ it ∈ s.queue, it ∈ (step R h cls full s o).queue := by
  intro it hit
  cases o <;> simp only [step] <;> (repeat' split) <;> simp_all

/-- every new verdict is a ghost record of the same step -/
theorem verdict_step (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) :
    ∀ v ∈ (step R h cls full s o).verdicts, v ∈ s.verdicts ∨
      ∃ x ∈ auditRec R s o, x.1 = v.id ∧ h x.2.1 = v.d ∧ x.2.2.1 = v.pass ∧ v.by_ = some x.2.2.2 := by
  intro v hv
  cases o <;> simp only [step, auditRec] at hv ⊢ <;> (repeat' split at hv) <;> simp_all [full]
  rcases hv with hv | rfl <;> simp_all

/-- every ghost record names a content that is in the queue -/
theorem auditRec_in_queue (R : Roles) (s : St) (o : Op) :
    ∀ x ∈ auditRec R s o, ∃ it ∈ s.queue, it.content = x.2.1 := by
  intro x hx
  cases o <;> simp only [auditRec] at hx <;> (repeat' split at hx) <;> simp_all
  rename_i it _ hit _
  exact ⟨it, mem_of_itemOf hit, by simp⟩

/-- every new execution runs a content that is in the queue -/
theorem executed_step (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (o : Op) :
    ∀ e ∈ (step R h cls full s o).executed, e ∈ s.executed ∨ ∃ it ∈ s.queue, it.content = e.content := by
  intro e he
  cases o <;> simp only [step] at he <;> (repeat' split at he) <;> simp_all
  rename_i it _ hit _
  rcases he with he | rfl
  · exact Or.inl he
  · exact Or.inr ⟨it, mem_of_itemOf hit, rfl⟩

/-- the ghost invariant: verdicts are ghost-recorded audits; ghost and executed contents are queue contents -/
structure J (h : ℕ → ℕ) (s : St) (g : List ARec) : Prop where
  verd : ∀ v ∈ s.verdicts, ∃ x ∈ g, x.1 = v.id ∧ h x.2.1 = v.d ∧ x.2.2.1 = v.pass ∧ v.by_ = some x.2.2.2
  gq : ∀ x ∈ g, ∃ it ∈ s.queue, it.content = x.2.1
  eq : ∀ e ∈ s.executed, ∃ it ∈ s.queue, it.content = e.content

theorem J_step (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (g : List ARec) (o : Op) (hJ : J h s g) :
    J h (step R h cls full s o) (g ++ auditRec R s o) where
  verd v hv := by
    rcases verdict_step R h cls s o v hv with hv | ⟨x, hx, hxv⟩
    · obtain ⟨x, hx, hxv⟩ := hJ.verd v hv
      exact ⟨x, List.mem_append_left _ hx, hxv⟩
    · exact ⟨x, List.mem_append_right _ hx, hxv⟩
  gq x hx := by
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨it, hit, he⟩ := hJ.gq x hx
      exact ⟨it, queue_mono R h cls s o it hit, he⟩
    · obtain ⟨it, hit, he⟩ := auditRec_in_queue R s o x hx
      exact ⟨it, queue_mono R h cls s o it hit, he⟩
  eq e he := by
    rcases executed_step R h cls s o e he with he | ⟨it, hit, hc⟩
    · obtain ⟨it, hit, hc⟩ := hJ.eq e he
      exact ⟨it, queue_mono R h cls s o it hit, hc⟩
    · exact ⟨it, queue_mono R h cls s o it hit, hc⟩

theorem J_fold (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) (sg : St × List ARec)
    (hJ : J h sg.1 sg.2) : J h (ops.foldl (gstep R h cls) sg).1 (ops.foldl (gstep R h cls) sg).2 := by
  induction ops generalizing sg with
  | nil => exact hJ
  | cons o ops ih => exact ih _ (J_step R h cls sg.1 sg.2 o hJ)

theorem J_grun (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) :
    J h (grun R h cls ops).1 (grun R h cls ops).2 :=
  J_fold R h cls ops (init, []) ⟨by simp [init], by simp, by simp [init]⟩

/-- audited contents are queue contents (submitted or amended versions) -/
theorem ghost_in_queue (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) :
    ∀ x ∈ (grun R h cls ops).2, ∃ it ∈ (run R h cls full init ops).queue, it.content = x.2.1 := by
  rw [← grun_fst]; exact (J_grun R h cls ops).gq

/-- executed contents are queue contents -/
theorem executed_in_queue (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) :
    ∀ e ∈ (run R h cls full init ops).executed, ∃ it ∈ (run R h cls full init ops).queue, it.content = e.content := by
  rw [← grun_fst]; exact (J_grun R h cls ops).eq

/-- **SC-25 at content level.** If the digest is injective on every content that ever appears in the queue, every
executed operation's EXACT content was audited PASS by an auditor (a ghost audit record with that operation id, that
content, pass = true and an auditor). Adversary class TRACE_ARBITRARY (any operations, any caller ids, any `h`
injective on the run's contents, any classifier). -/
theorem sc25_content_safe (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op)
    (hinj : Set.InjOn h {c | ∃ it ∈ (run R h cls full init ops).queue, it.content = c}) :
    ∀ e ∈ (run R h cls full init ops).executed,
      ∃ x ∈ (grun R h cls ops).2, x.1 = e.id ∧ x.2.1 = e.content ∧ x.2.2.1 = true ∧ x.2.2.2 ∈ R.auditors := by
  intro e he
  obtain ⟨hv, -⟩ := (sc25_safe R h cls ops).1 e he
  obtain ⟨v, hvmem, hid, hpass, hd, a, hby, ha⟩ := hv
  have hJ := J_grun R h cls ops
  rw [grun_fst] at hJ
  obtain ⟨x, hx, hxid, hxd, hxp, hxby⟩ := hJ.verd v (List.mem_of_mem_take hvmem)
  obtain ⟨it₁, hit₁, hc₁⟩ := hJ.gq x hx
  obtain ⟨it₂, hit₂, hc₂⟩ := hJ.eq e he
  have hcont : x.2.1 = e.content := hinj ⟨it₁, hit₁, hc₁⟩ ⟨it₂, hit₂, hc₂⟩ (by rw [hxd, hd])
  rw [hby] at hxby
  cases hxby
  exact ⟨x, hx, hxid.trans hid, hcont, hxp.trans hpass, ha⟩

/-- **Necessity (review witness W3).** With a constant digest the auditor passes content 7, the agent amends it to
50, and 50 executes; the only ghost audit record is of content 7, so no audit of 50 exists. -/
theorem digest_only_executes_unaudited :
    let ops : List Op := [.submit 1 0 7 false, .audit 2 0 true, .amend 1 0 50, .check 0, .fire 0]
    (run R0 (fun _ => 0) cls0 full init ops).executed.map Exec.content = [50] ∧
      (grun R0 (fun _ => 0) cls0 ops).2 = [(0, 7, true, 2)] := by
  decide

end ControlStack.SC25Content
