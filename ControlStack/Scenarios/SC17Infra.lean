/-
SC-17: no infrastructure-as-code / cluster permission sabotage.

An abstract desired-state model (families F4/F7 for the review gate, F1/F3 for the live state):
- the permission state is a set of grants (subject, verb, resource); a trusted `allowed` predicate on WHOLE states is
  the policy ceiling (it can forbid combinations, e.g. one subject holding two verbs that together escalate);
- the agent proposes diffs (adds, deletes) and may amend its proposals; a reviewer other than the author approves
  exactly the diff it saw;
- a trusted gate applies a diff atomically only if an approval matches exactly the current diff and the RESULTING state
  satisfies the ceiling; the result is computed from the desired state, so any out-of-band drift in the live state is
  reverted (and flagged) at every apply, and `reconcile` reverts it in between;
- an absorbing admin HALT.

Main results (deployed configuration `full`; adversary class TRACE_ARBITRARY: any proposals, amendments, approvals by
any caller, out-of-band live mutations, reconciles and applies):
- `sc17_safe`: from `init` (any initial grants), at every apply the live state equals the new desired state, satisfies
  the ceiling, and the applied diff is exactly one a reviewer other than its author approved; no proposal applies twice;
- `reconcile_restores`: after a reconcile, live = desired;
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`); non-vacuity `honest_apply`.

Necessity witnesses: `text_ceiling_composition_breaks` (checking the ceiling on the diff text: two individually
acceptable diffs compose into a forbidden combination), `approve_then_amend_breaks`, `no_drift_detection_breaks` (an
out-of-band grant persists through an apply), `no_halt_check_breaks`.

Premises outside the model: the gate is the only writer of the desired state and the reconciler the only legitimate
writer of live state; drift detection sees the whole live state; reviewer/admin credentials are held by those
principals; `allowed` captures the intended ceiling. Not claimed: that out-of-band changes are prevented between
reconciles (they are reverted, not prevented), or that approved diffs are wise. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC17

open ControlStack.Gate

/-- a grant: (subject, verb, resource) -/
abbrev G := ℕ × ℕ × ℕ

structure Diff where
  adds : List G
  dels : List G
deriving DecidableEq, Repr

def applyDiff (st : List G) (d : Diff) : List G := st.filter (fun g => g ∉ d.dels) ++ d.adds

structure Env where
  reviewers : List ℕ
  admins : List ℕ
  allowed : List G → Bool

structure Pr where
  id : ℕ
  author : ℕ
  diff : Diff
deriving DecidableEq, Repr

structure Ap where
  id : ℕ
  reviewer : ℕ
  author : ℕ
  diff : Diff
deriving DecidableEq, Repr

/-- an apply: proposal, author, diff applied, live and desired state right after -/
structure AppRec where
  id : ℕ
  author : ℕ
  diff : Diff
  live : List G
  desired : List G
deriving DecidableEq, Repr

structure St where
  desired : List G
  live : List G
  /-- newest version first -/
  props : List Pr
  approvals : List Ap
  applied : List AppRec
  done : List ℕ
  flags : List ℕ
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | propose (caller id : ℕ) (d : Diff)
  | amend (caller id : ℕ) (d : Diff)
  | approve (caller id : ℕ)
  | oob (g : G)
  | reconcile
  | apply (id : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  exact : Bool
  resultCheck : Bool
  drift : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init (g0 : List G) : St := ⟨g0, g0, [], [], [], [], [], false⟩

def propOf (s : St) (id : ℕ) : Option Pr := s.props.find? (fun p => p.id = id)

/-- the live state an apply produces: from the desired state (drift reverted) or, without drift handling, from live -/
def newLive (C : Checks) (s : St) (d : Diff) : List G := applyDiff (if C.drift then s.desired else s.live) d

def ceilingOk (E : Env) (C : Checks) (s : St) (d : Diff) : Bool :=
  if C.resultCheck then E.allowed (newLive C s d) else E.allowed d.adds

/-- drift seen at an apply is flagged -/
def flagUpd (C : Checks) (s : St) (id : ℕ) : List ℕ := if C.drift ∧ s.live ≠ s.desired then s.flags ++ [id] else s.flags

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .propose c id d =>
    if s.halted ∧ C.haltCheck then s
    else if propOf s id = none then { s with props := ⟨id, c, d⟩ :: s.props } else s
  | .amend c id d =>
    if s.halted ∧ C.haltCheck then s
    else match propOf s id with
      | none => s
      | some p => if p.author = c then { s with props := ⟨id, c, d⟩ :: s.props } else s
  | .approve c id =>
    if s.halted ∧ C.haltCheck then s
    else match propOf s id with
      | none => s
      | some p =>
        if c ∈ E.reviewers ∧ c ≠ p.author then { s with approvals := s.approvals ++ [⟨id, c, p.author, p.diff⟩] }
        else s
  | .oob g => { s with live := g :: s.live }
  | .reconcile =>
    if s.halted ∧ C.haltCheck then s
    else if C.drift ∧ s.live ≠ s.desired then { s with live := s.desired, flags := s.flags ++ [0] } else s
  | .apply id =>
    if s.halted ∧ C.haltCheck then s
    else match propOf s id with
      | none => s
      | some p =>
        if id ∉ s.done ∧ (∃ a ∈ s.approvals, a.id = id ∧ a.author = p.author ∧ (C.exact = true → a.diff = p.diff)) ∧
            ceilingOk E C s p.diff = true then
          { s with desired := applyDiff s.desired p.diff, live := newLive C s p.diff,
                   applied := s.applied ++ [⟨id, p.author, p.diff, newLive C s p.diff, applyDiff s.desired p.diff⟩],
                   done := s.done ++ [id],
                   flags := flagUpd C s id }
        else s
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run E C s (o :: ops) = run E C (step E C s o) ops := rfl

/-! ## Invariant and safety -/

/-- at the apply: live equals desired, within the ceiling, and the diff is exactly one an independent reviewer approved -/
def AppOk (E : Env) (s : St) (e : AppRec) : Prop :=
  E.allowed e.live = true ∧ e.live = e.desired ∧
    ∃ a ∈ s.approvals, a.id = e.id ∧ a.diff = e.diff ∧ a.reviewer ∈ E.reviewers ∧ a.reviewer ≠ e.author

def Good (E : Env) (s : St) : Prop := (∀ e ∈ s.applied, AppOk E s e) ∧ (s.applied.map AppRec.id).Nodup

structure Inv (E : Env) (s : St) : Prop where
  appr : ∀ a ∈ s.approvals, a.reviewer ∈ E.reviewers ∧ a.reviewer ≠ a.author
  apps : ∀ e ∈ s.applied, E.allowed e.live = true ∧ e.live = e.desired ∧
    ∃ a ∈ s.approvals, a.id = e.id ∧ a.diff = e.diff ∧ a.author = e.author
  done_ok : ∀ e ∈ s.applied, e.id ∈ s.done
  nodup : (s.applied.map AppRec.id).Nodup

theorem inv_init (E : Env) (g0 : List G) : Inv E (init g0) :=
  ⟨by simp [init], by simp [init], by simp [init], by simp [init]⟩

theorem Inv.good {E : Env} {s : St} (h : Inv E s) : Good E s := by
  refine ⟨fun e he => ?_, h.nodup⟩
  obtain ⟨h1, h2, a, ha, h3, h4, h5⟩ := h.apps e he
  obtain ⟨h6, h7⟩ := h.appr a ha
  exact ⟨h1, h2, a, ha, h3, h4, h6, h5 ▸ h7⟩

theorem propOf_spec {s : St} {id : ℕ} {p : Pr} (h : propOf s id = some p) : p ∈ s.props ∧ p.id = id :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- steps that touch only proposals, live state or flags -/
theorem inv_same {E : Env} {s t : St} (h : Inv E s) (ha : t.approvals = s.approvals) (hp : t.applied = s.applied)
    (hd : t.done = s.done) : Inv E t :=
  ⟨ha ▸ h.appr, by rw [hp, ha]; exact h.apps, by rw [hp, hd]; exact h.done_ok, hp ▸ h.nodup⟩

theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o) := by
  cases o with
  | approve c id =>
    cases hp : propOf s id with
    | none => simp only [step, hp]; split_ifs <;> exact h
    | some p =>
      simp only [step, hp]
      split_ifs with h1 h2
      · exact h
      · refine ⟨fun a ha => ?_, fun e he => ?_, h.done_ok, h.nodup⟩
        · rcases List.mem_append.1 ha with ha | ha
          · exact h.appr a ha
          · simp at ha; subst ha; exact h2
        · obtain ⟨x1, x2, a, ha, x3⟩ := h.apps e he
          exact ⟨x1, x2, a, List.mem_append_left _ ha, x3⟩
      · exact h
  | apply id =>
    cases hp : propOf s id with
    | none => simp only [step, hp]; split_ifs <;> exact h
    | some p =>
      simp only [step, hp]
      split_ifs with h1 h2
      · exact h
      · obtain ⟨hn, ⟨a, ha, hid, hau, hdf⟩, hc⟩ := h2
        simp only [full, forall_const] at hdf
        have hnl : newLive full s p.diff = applyDiff s.desired p.diff := rfl
        have hce : E.allowed (newLive full s p.diff) = true := by simpa [ceilingOk, full] using hc
        refine ⟨h.appr, fun e he => ?_, fun e he => ?_, ?_⟩
        · rcases List.mem_append.1 he with he | he
          · exact h.apps e he
          · simp at he; subst he
            exact ⟨hce, hnl, a, ha, hid, hdf, hau⟩
        · rcases List.mem_append.1 he with he | he
          · exact List.mem_append_left _ (h.done_ok e he)
          · simp at he; subst he; simp
        · simp only [List.map_append, List.map_cons, List.map_nil]
          refine List.nodup_append.2 ⟨h.nodup, List.nodup_singleton _, fun x hx y hy => ?_⟩
          simp only [List.mem_singleton] at hy
          subst hy
          rintro rfl
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
          exact hn (h.done_ok e he)
      · exact h
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact h | exact inv_same h rfl rfl rfl

theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv E s o h)

/-- **SC-17 safety.** After any trace from `init`, at every apply the live state equals the new desired state and
satisfies the ceiling, and the applied diff is exactly one a reviewer other than its author approved; no proposal
applies twice. Adversary: TRACE_ARBITRARY (including out-of-band live mutations). -/
theorem sc17_safe (E : Env) (g0 : List G) (ops : List Op) : Good E (run E full (init g0) ops) :=
  (run_inv E _ ops (inv_init E g0)).good

/-- **Drift is reverted**: after a reconcile (not halted), live = desired. -/
theorem reconcile_restores (E : Env) (s : St) (hh : s.halted = false) :
    (step E full s .reconcile).live = (step E full s .reconcile).desired := by
  simp only [step, hh, Bool.false_eq_true, false_and, ite_false, show full.drift = true from rfl, true_and]
  split_ifs with h1
  · rfl
  · simpa using h1

/-! ## Halt -/

theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) :
    (step E full s o).applied = s.applied ∧ (step E full s o).halted = true := by
  cases o with
  | oob g => simp [step, hh]
  | halt c => simp only [step]; split_ifs <;> simp [hh]
  | _ => simp [step, full, hh]

/-- **Halt freezes applies**: once halted, no trace applies anything. -/
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) :
    (run E full s ops).applied = s.applied := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    rw [run_cons]
    obtain ⟨h1, h2⟩ := step_halted E s o hh
    rw [ih _ h2, h1]

/-! ## Client of the shared gate interface -/

theorem applied_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.applied <+: (step E C s o).applied := by
  cases o with
  | apply id =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | oob g => exact List.prefix_refl _
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals exact List.prefix_refl _

def sys (E : Env) : System St Op AppRec where
  step := step E full
  effects := St.applied

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := AppOk E
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => applied_prefix E full s o
  inv_ok := fun _ h e he => h.good.1 e he

/-! ## Non-vacuity and necessity witnesses

Agent (author) 1, reviewer 2, admin 9. The ceiling forbids subject 1 holding both verb 1 and verb 2 on resource 1. -/

def E0 : Env := ⟨[2], [9], fun st => !(decide ((1, 1, 1) ∈ st) && decide ((1, 2, 1) ∈ st))⟩

def dA : Diff := ⟨[(1, 1, 1)], []⟩
def dB : Diff := ⟨[(1, 2, 1)], []⟩
def dC : Diff := ⟨[(3, 3, 3)], []⟩

/-- **Non-vacuity**: a reviewed diff within the ceiling applies. -/
theorem honest_apply :
    (run E0 full (init []) [.propose 1 0 dA, .approve 2 0, .apply 0]).live = [(1, 1, 1)] := by
  decide

/-- checking the ceiling on the diff TEXT: two individually acceptable diffs compose into the forbidden combination;
checking the resulting state refuses the second -/
theorem text_ceiling_composition_breaks :
    (E0.allowed (run E0 { full with resultCheck := false } (init [])
      [.propose 1 0 dA, .approve 2 0, .apply 0, .propose 1 1 dB, .approve 2 1, .apply 1]).live) = false ∧
    (run E0 full (init [])
      [.propose 1 0 dA, .approve 2 0, .apply 0, .propose 1 1 dB, .approve 2 1, .apply 1]).live = [(1, 1, 1)] := by
  decide

/-- approving one diff and applying an amended one, unless the approval must match exactly -/
theorem approve_then_amend_breaks :
    let s := run E0 { full with exact := false } (init []) [.propose 1 0 dA, .approve 2 0, .amend 1 0 dC, .apply 0]
    s.live = [(3, 3, 3)] ∧ s.approvals.map Ap.diff = [dA] ∧
    (run E0 full (init []) [.propose 1 0 dA, .approve 2 0, .amend 1 0 dC, .apply 0]).applied = [] := by
  decide

/-- without drift handling, an out-of-band grant survives an apply (live ≠ desired); with it, the apply reverts it -/
theorem no_drift_detection_breaks :
    let s := run E0 { full with drift := false } (init []) [.oob (5, 5, 5), .propose 1 0 dA, .approve 2 0, .apply 0]
    s.live = [(5, 5, 5), (1, 1, 1)] ∧ s.desired = [(1, 1, 1)] ∧
    (run E0 full (init []) [.oob (5, 5, 5), .propose 1 0 dA, .approve 2 0, .apply 0]).live = [(1, 1, 1)] := by
  decide

/-- without the halt check, applies continue after a halt -/
theorem no_halt_check_breaks :
    (run E0 { full with haltCheck := false } (init []) [.propose 1 0 dA, .approve 2 0, .halt 9, .apply 0]).live =
      [(1, 1, 1)] ∧
    (run E0 full (init []) [.propose 1 0 dA, .approve 2 0, .halt 9, .apply 0]).live = [] := by
  decide

end ControlStack.SC17

#print axioms ControlStack.SC17.sc17_safe
#print axioms ControlStack.SC17.reconcile_restores
#print axioms ControlStack.SC17.halt_freezes
#print axioms ControlStack.SC17.spec
#print axioms ControlStack.SC17.honest_apply
#print axioms ControlStack.SC17.text_ceiling_composition_breaks
#print axioms ControlStack.SC17.approve_then_amend_breaks
#print axioms ControlStack.SC17.no_drift_detection_breaks
#print axioms ControlStack.SC17.no_halt_check_breaks
