/-
SC-20: an agent poisons a training/distillation dataset or a hidden label.

NO FORMAL CLAIM about semantic cleanliness: whether an example or label is "poisoned" is a semantic judgement (and an
allowlisted source can itself be poisoned). What CAN be stated is the provenance/lineage property the threat model
proposes ("dataset provenance, forbidden file/label transitions and immutable training-set hash"):

- examples enter through an ingestion pipeline that labels each with its source; a source must be allowlisted and the
  example's content must match the digest registered for it (content addressing);
- examples the agent writes have no source: they are QUARANTINED and enter a training set only after a reviewer other
  than their writer promotes exactly that content (by digest);
- an admin freezes a training manifest (example ids with digests); training uses the CURRENT stored contents, so it
  re-checks every digest against the frozen manifest and refuses on any mismatch (no label flip after the freeze);
- an absorbing admin HALT.

Main results (deployed configuration `full`; adversary class TRACE_ARBITRARY: any ingestions, agent writes, edits of
stored examples (including label flips), promotions by any caller, freezes and training runs):
- `sc20_safe`: from `init`, every example used in any training run has content whose digest is either registered for
  it by an allowlisted source or was promoted by a reviewer other than its writer;
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`); non-vacuity `honest_training`, `reviewed_promotion`.

Necessity witnesses: `no_quarantine_breaks`, `edit_after_freeze_breaks` (no re-check: a label flip after the freeze
is trained on), `unlisted_source_breaks`, `self_promotion_refused` (positive), `no_halt_check_breaks`.

What remains semantic and unformalised: whether allowlisted, registered or reviewed content is actually clean, whether
labels are correct, and whether the reviewer looked carefully. Premises: the pipeline's source labels and the content
registry are trusted; the digest is collision-resistant on the contents in play (digest-level statements here, as in
SC-16); training reads only through the trusted loader. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC20

open ControlStack.Gate

structure Env where
  allow : List ℕ
  registry : ℕ → Option ℕ
  reviewers : List ℕ
  admins : List ℕ
  h : ℕ → ℕ

structure Ex where
  id : ℕ
  content : ℕ
  src : Option ℕ
  writer : ℕ
deriving DecidableEq, Repr

structure St where
  /-- newest version first -/
  store : List Ex
  /-- (example id, reviewer, digest promoted) -/
  promoted : List (ℕ × ℕ × ℕ)
  manifest : Option (List (ℕ × ℕ))
  /-- training runs: (example id, content used) -/
  trained : List (List (ℕ × ℕ))
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | ingest (src id x : ℕ)
  | agentWrite (caller id x : ℕ)
  | edit (id x : ℕ)
  | promote (caller id : ℕ)
  | freeze (caller : ℕ) (ids : List ℕ)
  | train
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  sourceCheck : Bool
  quarantine : Bool
  recheck : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], none, [], false⟩

def exOf (s : St) (id : ℕ) : Option Ex := s.store.find? (fun e => e.id = id)

/-- may this example (by its current content) enter a frozen manifest? -/
def admitted (E : Env) (C : Checks) (s : St) (e : Ex) : Bool :=
  match e.src with
  | some src => !C.sourceCheck || (decide (src ∈ E.allow) && decide (E.registry e.id = some (E.h e.content)))
  | none => !C.quarantine || s.promoted.any (fun p => p.1 = e.id && p.2.2 = E.h e.content)

def manifestOf (E : Env) (C : Checks) (s : St) (ids : List ℕ) : List (ℕ × ℕ) :=
  ids.filterMap (fun i => (exOf s i).bind (fun e => if admitted E C s e then some (i, E.h e.content) else none))

/-- every manifest entry's current content still has the frozen digest -/
def intact (E : Env) (s : St) (m : List (ℕ × ℕ)) : Bool :=
  m.all (fun p => (exOf s p.1).any (fun e => E.h e.content = p.2))

def runOf (s : St) (m : List (ℕ × ℕ)) : List (ℕ × ℕ) := m.filterMap (fun p => (exOf s p.1).map (fun e => (p.1, e.content)))

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .ingest src id x => if s.halted ∧ C.haltCheck then s else { s with store := ⟨id, x, some src, 0⟩ :: s.store }
  | .agentWrite c id x => if s.halted ∧ C.haltCheck then s else { s with store := ⟨id, x, none, c⟩ :: s.store }
  | .edit id x =>
    if s.halted ∧ C.haltCheck then s
    else match exOf s id with
      | none => s
      | some e => { s with store := { e with content := x } :: s.store }
  | .promote c id =>
    if s.halted ∧ C.haltCheck then s
    else match exOf s id with
      | none => s
      | some e =>
        if c ∈ E.reviewers ∧ c ≠ e.writer ∧ e.src = none then
          { s with promoted := s.promoted ++ [(id, c, E.h e.content)] }
        else s
  | .freeze c ids =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ E.admins then { s with manifest := some (manifestOf E C s ids) } else s
  | .train =>
    if s.halted ∧ C.haltCheck then s
    else match s.manifest with
      | none => s
      | some m => if C.recheck = true → intact E s m = true then { s with trained := s.trained ++ [runOf s m] } else s
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run E C s (o :: ops) = run E C (step E C s o) ops := rfl

/-! ## Invariant and safety -/

/-- a digest that is registered for the example, or that a reviewer promoted -/
def Adm (E : Env) (s : St) (i d : ℕ) : Prop :=
  E.registry i = some d ∨ ∃ p ∈ s.promoted, p.1 = i ∧ p.2.2 = d ∧ p.2.1 ∈ E.reviewers

def Good (E : Env) (s : St) : Prop := ∀ r ∈ s.trained, ∀ q ∈ r, Adm E s q.1 (E.h q.2)

structure Inv (E : Env) (s : St) : Prop where
  prom : ∀ p ∈ s.promoted, p.2.1 ∈ E.reviewers
  man : ∀ m, s.manifest = some m → ∀ q ∈ m, Adm E s q.1 q.2
  trained : Good E s

theorem inv_init (E : Env) : Inv E init := ⟨by simp [init], by simp [init], by simp [init, Good]⟩

theorem Adm.mono {E : Env} {s t : St} (hp : s.promoted ⊆ t.promoted) {i d : ℕ} (h : Adm E s i d) : Adm E t i d :=
  h.imp id (fun ⟨p, hp', rest⟩ => ⟨p, hp hp', rest⟩)

theorem exOf_spec {s : St} {i : ℕ} {e : Ex} (h : exOf s i = some e) : e.id = i := by simpa using List.find?_some h

theorem manifestOf_adm (E : Env) (s : St) (hi : Inv E s) (ids : List ℕ) : ∀ q ∈ manifestOf E full s ids, Adm E s q.1 q.2 := by
  intro q hq
  simp only [manifestOf, List.mem_filterMap] at hq
  obtain ⟨i, _, hq⟩ := hq
  cases he : exOf s i with
  | none => simp [he] at hq
  | some e =>
    simp only [he, Option.bind_some] at hq
    split_ifs at hq with ha
    cases hq
    have hid := exOf_spec he
    simp only [admitted, full, Bool.not_true, Bool.false_or] at ha
    cases hsrc : e.src with
    | some src =>
      simp only [hsrc, Bool.and_eq_true, decide_eq_true_eq] at ha
      exact Or.inl (hid ▸ ha.2)
    | none =>
      simp only [hsrc, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
      obtain ⟨p, hp, h1, h2⟩ := ha
      exact Or.inr ⟨p, hp, h1.trans hid, h2, hi.prom p hp⟩

theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o) := by
  cases o with
  | promote c id =>
    cases he : exOf s id with
    | none => simp only [step, he]; split_ifs <;> exact h
    | some e =>
      simp only [step, he]
      split_ifs with h1 h2
      · exact h
      · have hsub : s.promoted ⊆ s.promoted ++ [(id, c, E.h e.content)] := fun _ y => List.mem_append_left _ y
        refine ⟨fun p hp => ?_, fun m hm q hq => (h.man m hm q hq).mono hsub,
          fun r hr q hq => (h.trained r hr q hq).mono hsub⟩
        rcases List.mem_append.1 hp with hp | hp
        · exact h.prom p hp
        · simp at hp; subst hp; exact h2.1
      · exact h
  | freeze c ids =>
    simp only [step]
    split_ifs
    · exact h
    · refine ⟨h.prom, fun m hm => ?_, h.trained⟩
      simp only [Option.some.injEq] at hm
      subst hm
      exact manifestOf_adm E s h ids
    · exact h
  | train =>
    simp only [step]
    split_ifs
    · exact h
    · cases hm : s.manifest with
      | none => exact h
      | some m =>
        dsimp only
        split_ifs with hc
        · simp only [full, true_implies] at hc
          refine ⟨h.prom, fun m' hm' q hq => ?_, fun r hr q hq => ?_⟩
          · simp only [Option.some.injEq] at hm'
            subst hm'
            exact h.man _ hm q hq
          rcases List.mem_append.1 hr with hr | hr
          · exact h.trained r hr q hq
          · simp at hr; subst hr
            simp only [runOf, List.mem_filterMap] at hq
            obtain ⟨p, hp, hq⟩ := hq
            cases he : exOf s p.1 with
            | none => simp [he] at hq
            | some e =>
              simp only [he, Option.map_some, Option.some.injEq] at hq
              subst hq
              have hint := (List.all_eq_true.1 hc) p hp
              simp only [he, Option.any_some, decide_eq_true_eq] at hint
              have := h.man m hm p hp
              show Adm E s p.1 (E.h e.content)
              rw [hint]
              exact this
        · exact h
  | halt c =>
    simp only [step]
    split_ifs
    · exact ⟨h.prom, h.man, h.trained⟩
    · exact h
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact h | exact ⟨h.prom, h.man, h.trained⟩

theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv E s o h)

/-- **SC-20 provenance safety.** After any trace from `init`, every example used in any training run has content
whose digest is registered for it (allowlisted, content-addressed source) or was promoted by a reviewer other than its
writer. Adversary: TRACE_ARBITRARY (including edits and label flips after the freeze). NOT a claim that the data is
clean. -/
theorem sc20_safe (E : Env) (ops : List Op) : Good E (run E full init ops) := (run_inv E init ops (inv_init E)).trained

theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s := by
  cases o with
  | halt c =>
    simp only [step]
    split_ifs
    · cases s; simp_all
    · rfl
  | _ => simp [step, full, hh]

/-- **Halt freezes training**: once halted, no trace changes the state. -/
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s := by
  induction ops with
  | nil => rfl
  | cons o ops ih => rw [run_cons, step_halted E s o hh, ih]

theorem trained_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.trained <+: (step E C s o).trained := by
  cases o with
  | train =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals exact List.prefix_refl _

def sys (E : Env) : System St Op (List (ℕ × ℕ)) where
  step := step E full
  effects := St.trained

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := fun s r => ∀ q ∈ r, Adm E s q.1 (E.h q.2)
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => trained_prefix E full s o
  inv_ok := fun _ h r hr => h.trained r hr

/-! ## Non-vacuity and necessity witnesses

Source 50 is allowlisted and registers digest 7 for example 0; agent 1, reviewer 2, admin 9; digest = content. -/

def E0 : Env := ⟨[50], fun i => if i = 0 then some 7 else none, [2], [9], id⟩

/-- **Non-vacuity**: a registered example from an allowlisted source is trained on. -/
theorem honest_training :
    (run E0 full init [.ingest 50 0 7, .freeze 9 [0], .train]).trained = [[(0, 7)]] := by
  decide

/-- **Non-vacuity**: an agent-written example enters after an independent reviewer promotes it. -/
theorem reviewed_promotion :
    (run E0 full init [.agentWrite 1 1 66, .promote 2 1, .freeze 9 [1], .train]).trained = [[(1, 66)]] := by
  decide

/-- without quarantine, an unreviewed agent-written example is trained on -/
theorem no_quarantine_breaks :
    (run E0 { full with quarantine := false } init [.agentWrite 1 1 66, .freeze 9 [1], .train]).trained =
      [[(1, 66)]] ∧
    (run E0 full init [.agentWrite 1 1 66, .freeze 9 [1], .train]).trained = [[]] := by
  decide

/-- without the re-check, a label flip after the freeze is trained on; with it, training refuses -/
theorem edit_after_freeze_breaks :
    (run E0 { full with recheck := false } init [.ingest 50 0 7, .freeze 9 [0], .edit 0 8, .train]).trained =
      [[(0, 8)]] ∧
    (run E0 full init [.ingest 50 0 7, .freeze 9 [0], .edit 0 8, .train]).trained = [] := by
  decide

/-- without the source check, an example from an unlisted source with no registered digest is trained on -/
theorem unlisted_source_breaks :
    (run E0 { full with sourceCheck := false } init [.ingest 51 2 66, .freeze 9 [2], .train]).trained = [[(2, 66)]] ∧
    (run E0 full init [.ingest 51 2 66, .freeze 9 [2], .train]).trained = [[]] := by
  decide

/-- a reviewer cannot promote its own example -/
theorem self_promotion_refused :
    (run E0 full init [.agentWrite 2 1 66, .promote 2 1]).promoted = [] := by
  decide

/-- without the halt check, training continues after a halt -/
theorem no_halt_check_breaks :
    (run E0 { full with haltCheck := false } init [.ingest 50 0 7, .freeze 9 [0], .halt 9, .train]).trained =
      [[(0, 7)]] ∧
    (run E0 full init [.ingest 50 0 7, .freeze 9 [0], .halt 9, .train]).trained = [] := by
  decide

end ControlStack.SC20

#print axioms ControlStack.SC20.sc20_safe
#print axioms ControlStack.SC20.halt_freezes
#print axioms ControlStack.SC20.spec
#print axioms ControlStack.SC20.honest_training
#print axioms ControlStack.SC20.reviewed_promotion
#print axioms ControlStack.SC20.no_quarantine_breaks
#print axioms ControlStack.SC20.edit_after_freeze_breaks
#print axioms ControlStack.SC20.unlisted_source_breaks
#print axioms ControlStack.SC20.self_promotion_refused
#print axioms ControlStack.SC20.no_halt_check_breaks
