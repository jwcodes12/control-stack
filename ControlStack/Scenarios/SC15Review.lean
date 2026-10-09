/-
SC-15: an agent inserts a hidden functional backdoor in source code.

NO FORMAL CLAIM about backdoors: whether a change contains a backdoor is a semantic judgement about program behaviour
under an open-ended threat model; no review process can be proved to catch it. What CAN be stated is the narrower
process invariant the threat model proposes ("no changes to specified auth/crypto/egress surfaces without review"):

- a change (content digest, the paths it actually touches as computed by a trusted diff, and the paths the author
  declares) is merged only if a reviewer other than the author approved EXACTLY that content, trusted CI passed on
  EXACTLY that content, and — if the change touches a security-sensitive surface (computed from the trusted diff, not
  the author's declaration) — a designated security reviewer other than the author also approved exactly that content;
- authors may amend changes (new content and paths); an absorbing admin HALT.

Main results (deployed configuration `full`; adversary class TRACE_ARBITRARY: any proposals, amendments, reviews and
CI runs in any order, any declarations):
- `sc15_safe`: from `init`, every merged change had an exact-content review by a non-author, a passing CI run on
  exactly that content, and, if it touches a sensitive surface, an exact-content security review by a non-author;
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`); non-vacuity `honest_merge`.

Necessity witnesses: `stale_review_breaks` (the review is matched by change id, so an amended change merges on the old
review), `declared_paths_breaks` (sensitivity computed from the author's declaration: an under-declared auth change
skips security review), `ci_other_content_breaks`, `self_review_breaks`, `no_halt_check_breaks`.

What remains semantic and unformalised: whether reviewed, tested code contains a backdoor; whether the sensitive-surface
list is complete; reviewer competence; test adequacy. A contract proved on restricted code (the second part of the
SC-15 policy) would be a separate, code-specific Lean development. Premises: the diff, CI and merge gate are trusted
and the merge gate is the only path to the protected branch. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC15

open ControlStack.Gate

structure Env where
  reviewers : List ℕ
  security : List ℕ
  admins : List ℕ
  sensitive : List ℕ
  testsPass : ℕ → Bool

structure Change where
  id : ℕ
  author : ℕ
  content : ℕ
  paths : List ℕ
  declared : List ℕ
deriving DecidableEq, Repr

/-- a review: change id, reviewer, author, content reviewed, security review? -/
structure Rev where
  id : ℕ
  reviewer : ℕ
  author : ℕ
  content : ℕ
  sec : Bool
deriving DecidableEq, Repr

structure St where
  /-- newest version first -/
  changes : List Change
  reviews : List Rev
  /-- trusted CI results: (change id, content, pass) -/
  ci : List (ℕ × ℕ × Bool)
  merged : List Change
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | propose (caller id content : ℕ) (paths declared : List ℕ)
  | amend (caller id content : ℕ) (paths : List ℕ)
  | review (caller id : ℕ) (sec : Bool)
  | runCI (id : ℕ)
  | merge (id : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  exact : Bool
  trustedPaths : Bool
  ciExact : Bool
  distinct : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true, true⟩

def init : St := ⟨[], [], [], [], false⟩

def chOf (s : St) (id : ℕ) : Option Change := s.changes.find? (fun c => c.id = id)

def touchesSensitive (E : Env) (C : Checks) (c : Change) : Bool :=
  (if C.trustedPaths then c.paths else c.declared).any (fun p => p ∈ E.sensitive)

/-- the merge gate's review test for change `c` (`sec`: security review) -/
abbrev Reviewed (C : Checks) (s : St) (c : Change) (sec : Bool) : Prop :=
  ∃ r ∈ s.reviews, r.id = c.id ∧ r.author = c.author ∧ (sec = true → r.sec = true) ∧
    (C.exact = true → r.content = c.content)

/-- the role a review needs: security reviewer for a security review, reviewer otherwise -/
def roleOk (E : Env) (sec : Bool) (r : ℕ) : Bool := if sec then decide (r ∈ E.security) else decide (r ∈ E.reviewers)

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .propose a id x ps ds =>
    if s.halted ∧ C.haltCheck then s
    else if chOf s id = none then { s with changes := ⟨id, a, x, ps, ds⟩ :: s.changes } else s
  | .amend a id x ps =>
    if s.halted ∧ C.haltCheck then s
    else match chOf s id with
      | none => s
      | some c => if c.author = a then { s with changes := { c with content := x, paths := ps } :: s.changes } else s
  | .review r id sec =>
    if s.halted ∧ C.haltCheck then s
    else match chOf s id with
      | none => s
      | some c =>
        if roleOk E sec r = true ∧ (C.distinct = true → r ≠ c.author) then
          { s with reviews := s.reviews ++ [⟨id, r, c.author, c.content, sec⟩] }
        else s
  | .runCI id =>
    if s.halted ∧ C.haltCheck then s
    else match chOf s id with
      | none => s
      | some c => { s with ci := s.ci ++ [(id, c.content, E.testsPass c.content)] }
  | .merge id =>
    if s.halted ∧ C.haltCheck then s
    else match chOf s id with
      | none => s
      | some c =>
        if Reviewed C s c false ∧ (touchesSensitive E C c = true → Reviewed C s c true) ∧
            (∃ x ∈ s.ci, x.1 = id ∧ (C.ciExact = true → x.2.1 = c.content) ∧ x.2.2 = true) then
          { s with merged := s.merged ++ [c] }
        else s
  | .halt a => if a ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run E C s (o :: ops) = run E C (step E C s o) ops := rfl

/-! ## Invariant and safety -/

/-- an exact-content review of `c` by a non-author holding the role it reviewed in (a security review when `sec`) -/
def RevOk (E : Env) (s : St) (c : Change) (sec : Bool) : Prop :=
  ∃ r ∈ s.reviews, r.id = c.id ∧ r.content = c.content ∧ r.reviewer ≠ c.author ∧ (sec = true → r.sec = true) ∧
    roleOk E r.sec r.reviewer = true

def MergeOk (E : Env) (s : St) (c : Change) : Prop :=
  RevOk E s c false ∧ ((c.paths.any (fun p => p ∈ E.sensitive)) = true → RevOk E s c true) ∧
    ∃ x ∈ s.ci, x.1 = c.id ∧ x.2.1 = c.content ∧ x.2.2 = true

structure Inv (E : Env) (s : St) : Prop where
  revs : ∀ r ∈ s.reviews, r.reviewer ≠ r.author ∧ roleOk E r.sec r.reviewer = true
  merged : ∀ c ∈ s.merged, MergeOk E s c

theorem inv_init (E : Env) : Inv E init := ⟨by simp [init], by simp [init]⟩

theorem MergeOk.mono {E : Env} {s t : St} (hr : s.reviews ⊆ t.reviews) (hc : s.ci ⊆ t.ci) {c : Change}
    (h : MergeOk E s c) : MergeOk E t c := by
  obtain ⟨⟨r, hrm, h1⟩, h2, x, hx, h3⟩ := h
  refine ⟨⟨r, hr hrm, h1⟩, fun hs => ?_, x, hc hx, h3⟩
  obtain ⟨r', hr', h4⟩ := h2 hs
  exact ⟨r', hr hr', h4⟩

theorem revOk_of {E : Env} {s : St} (h : Inv E s) {c : Change} {sec : Bool} (hrv : Reviewed full s c sec) :
    ∃ r ∈ s.reviews, r.id = c.id ∧ r.content = c.content ∧ r.reviewer ≠ c.author ∧ (sec = true → r.sec = true) ∧
      roleOk E r.sec r.reviewer = true := by
  obtain ⟨r, hr, h1, h2, h3, h4⟩ := hrv
  obtain ⟨h5, h6⟩ := h.revs r hr
  exact ⟨r, hr, h1, h4 rfl, h2 ▸ h5, h3, h6⟩

theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o) := by
  cases o with
  | review r id sec =>
    cases hc : chOf s id with
    | none => simp only [step, hc]; split_ifs <;> exact h
    | some c =>
      simp only [step, hc]
      split_ifs with h1 h2
      · exact h
      · obtain ⟨hrole, hd⟩ := h2
        simp only [full, true_implies] at hd
        refine ⟨fun x hx => ?_, fun m hm => by refine MergeOk.mono ?_ ?_ (h.merged m hm) <;> intro _ y <;> simp [y]⟩
        rcases List.mem_append.1 hx with hx | hx
        · exact h.revs x hx
        · simp at hx; subst hx; exact ⟨hd, hrole⟩
      · exact h
  | runCI id =>
    cases hc : chOf s id with
    | none => simp only [step, hc]; split_ifs <;> exact h
    | some c =>
      simp only [step, hc]
      split_ifs
      · exact h
      · exact ⟨h.revs, fun m hm => by refine MergeOk.mono ?_ ?_ (h.merged m hm) <;> intro _ y <;> simp [y]⟩
  | merge id =>
    cases hc : chOf s id with
    | none => simp only [step, hc]; split_ifs <;> exact h
    | some c =>
      simp only [step, hc]
      split_ifs with h1 h2
      · exact h
      · obtain ⟨hr, hs, x, hx, hxid, hxc, hxp⟩ := h2
        have hid : c.id = id := by simpa using List.find?_some hc
        refine ⟨h.revs, fun m hm => ?_⟩
        rcases List.mem_append.1 hm with hm | hm
        · exact h.merged m hm
        · simp at hm; subst hm
          refine ⟨revOk_of h hr, fun hsens => revOk_of h (hs (by simpa [touchesSensitive, full] using hsens)),
            x, hx, hxid.trans hid.symm, hxc rfl, hxp⟩
      · exact h
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact h | exact ⟨h.revs, h.merged⟩

theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv E s o h)

/-- **SC-15 process safety.** After any trace from `init`, every merged change had an exact-content review by a
non-author reviewer, a passing trusted CI run on exactly that content, and, if it touches a security-sensitive surface
(by the trusted diff), an exact-content review by a non-author security reviewer. Adversary: TRACE_ARBITRARY. This is
NOT a claim that merged code has no backdoor. -/
theorem sc15_safe (E : Env) (ops : List Op) : ∀ c ∈ (run E full init ops).merged, MergeOk E (run E full init ops) c :=
  (run_inv E init ops (inv_init E)).merged

theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s := by
  cases o with
  | halt c =>
    simp only [step]
    split_ifs
    · cases s; simp_all
    · rfl
  | _ => simp [step, full, hh]

/-- **Halt freezes merging**: once halted, no trace changes the state. -/
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s := by
  induction ops with
  | nil => rfl
  | cons o ops ih => rw [run_cons, step_halted E s o hh, ih]

theorem merged_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.merged <+: (step E C s o).merged := by
  cases o with
  | merge id =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals exact List.prefix_refl _

def sys (E : Env) : System St Op Change where
  step := step E full
  effects := St.merged

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := MergeOk E
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => merged_prefix E full s o
  inv_ok := fun _ h c hc => h.merged c hc

/-! ## Non-vacuity and necessity witnesses

Author 1, reviewer 2, security reviewer 3, admin 9; path 100 is the auth surface; content 13 fails the tests. -/

def E0 : Env := ⟨[2], [3], [9], [100], fun x => x != 13⟩

/-- **Non-vacuity**: a reviewed, tested, non-sensitive change merges. -/
theorem honest_merge :
    (run E0 full init [.propose 1 0 7 [5] [5], .review 2 0 false, .runCI 0, .merge 0]).merged = [⟨0, 1, 7, [5], [5]⟩] := by
  decide

/-- a review matched by change id only lets an amended change merge on the old review -/
theorem stale_review_breaks :
    let ops := [Op.propose 1 0 7 [5] [5], .review 2 0 false, .amend 1 0 8 [5], .runCI 0, .merge 0]
    (run E0 { full with exact := false } init ops).merged.map Change.content = [8] ∧
    (run E0 { full with exact := false } init ops).reviews.map Rev.content = [7] ∧
    (run E0 full init ops).merged = [] := by
  decide

/-- sensitivity computed from the author's declaration: an under-declared auth change skips security review -/
theorem declared_paths_breaks :
    let ops := [Op.propose 1 0 7 [100] [], .review 2 0 false, .runCI 0, .merge 0]
    (run E0 { full with trustedPaths := false } init ops).merged = [⟨0, 1, 7, [100], []⟩] ∧
    (run E0 full init ops).merged = [] := by
  decide

/-- CI matched by change id only: tests passed on content 7, failing content 13 merges -/
theorem ci_other_content_breaks :
    let ops := [Op.propose 1 0 7 [5] [5], .runCI 0, .amend 1 0 13 [5], .review 2 0 false, .merge 0]
    (run E0 { full with ciExact := false } init ops).merged.map Change.content = [13] ∧
    (run E0 full init ops).merged = [] := by
  decide

/-- if the author is also a reviewer and distinctness is not checked, it approves its own change -/
theorem self_review_breaks :
    let E1 : Env := ⟨[1, 2], [3], [9], [100], fun x => x != 13⟩
    let ops := [Op.propose 1 0 7 [5] [5], .review 1 0 false, .runCI 0, .merge 0]
    (run E1 { full with distinct := false } init ops).merged = [⟨0, 1, 7, [5], [5]⟩] ∧
    (run E1 full init ops).merged = [] := by
  decide

/-- without the halt check, merges continue after a halt -/
theorem no_halt_check_breaks :
    let ops := [Op.propose 1 0 7 [5] [5], .review 2 0 false, .runCI 0, .halt 9, .merge 0]
    (run E0 { full with haltCheck := false } init ops).merged = [⟨0, 1, 7, [5], [5]⟩] ∧
    (run E0 full init ops).merged = [] := by
  decide

end ControlStack.SC15

#print axioms ControlStack.SC15.sc15_safe
#print axioms ControlStack.SC15.halt_freezes
#print axioms ControlStack.SC15.spec
#print axioms ControlStack.SC15.honest_merge
#print axioms ControlStack.SC15.stale_review_breaks
#print axioms ControlStack.SC15.declared_paths_breaks
#print axioms ControlStack.SC15.ci_other_content_breaks
#print axioms ControlStack.SC15.self_review_breaks
#print axioms ControlStack.SC15.no_halt_check_breaks
