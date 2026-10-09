/-
SC-27: tampered evidence and assurance manifests — hash-chained log with an external anchor.

Relation to `ControlStack/Scenarios/SC27.lean`: that file is a compatibility facade re-exporting the audit-gate
models (record ordering). This file is the separate evidence-integrity model the SC-27 threat needs: an agent that can
change workspace files, reports or CI evidence must not get a substituted or fabricated record accepted.

The model (families F3/F4):
- an evidence log the writer appends to; the writer also controls the log's storage and can REWRITE it at any time
  (modify, reorder, truncate) — a ghost `truth` records what was really appended;
- each log has a hash-chain head `chainHead H h0 log` (each entry commits to the previous head);
- an INDEPENDENT witness periodically records the current head (an anchor; a ghost copy of the anchored log is kept
  for the statement); the writer can also publish heads of its own;
- a verifier accepts a manifest (a list of evidence entries) only if its chain head equals a head the independent
  witness anchored — not the writer's own heads, not the current storage, not an anchored prefix plus extra entries;
- an absorbing admin HALT.

Main results (deployed configuration `full`; adversary class TRACE_ARBITRARY: any appends, rewrites, writer-published
heads, anchoring times and manifests):
- `sc27_safe`: if the chain head is injective on the lists in play (the manifests accepted and the anchored logs;
  `Set.InjOn`, not global injectivity), every accepted manifest is EXACTLY a log the independent witness anchored, so
  modification, reordering, truncation or extension after anchoring is detected;
- `chainHead_injective`: the idealisation behind the premise — if the pair hash `H` is injective and never returns
  `h0`, the chain head is injective (this global form is impossible for a real compressing hash; the theorem above uses
  only the restricted premise);
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`); non-vacuity `honest_accept`; positive
  `tamper_after_anchor_detected`.

Necessity witnesses: `no_anchor_rollback_breaks` (checking only the writer's current storage accepts a full rewrite),
`self_signed_breaks` (accepting heads the writer published), `unanchored_suffix_breaks`, `collision_breaks` (the
injectivity premise cannot be dropped), and the honest limit `rewrite_before_anchor_window`: entries are protected only
once anchored.

Premises outside the model: the witness is independent of the writer (separate credentials and storage) and its
anchor log is append-only; the verifier code and its anchor source are not under the writer's control; the hash is
collision-resistant on the logs in play. Not claimed: that anchored evidence is true. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC27Chain

open ControlStack.Gate

/-- the hash-chain head: each entry is hashed with the previous head -/
def chainHead (H : ℕ → ℕ → ℕ) (h0 : ℕ) (l : List ℕ) : ℕ := l.foldl H h0

theorem chainHead_concat (H : ℕ → ℕ → ℕ) (h0 : ℕ) (l : List ℕ) (e : ℕ) :
    chainHead H h0 (l ++ [e]) = H (chainHead H h0 l) e := by
  simp [chainHead, List.foldl_append]

/-- **Idealisation**: with an injective pair hash that never returns `h0`, the chain head is injective. -/
theorem chainHead_injective (H : ℕ → ℕ → ℕ) (h0 : ℕ) (hinj : ∀ a b c d, H a b = H c d → a = c ∧ b = d)
    (hne : ∀ a b, H a b ≠ h0) : Function.Injective (chainHead H h0) := by
  intro l₁ l₂ h
  induction l₁ using List.reverseRecOn generalizing l₂ with
  | nil =>
    rcases List.eq_nil_or_concat l₂ with rfl | ⟨L, b, rfl⟩
    · rfl
    · rw [List.concat_eq_append, chainHead_concat] at h
      exact absurd h.symm (hne _ _)
  | append_singleton L₁ b₁ ih =>
    rcases List.eq_nil_or_concat l₂ with rfl | ⟨L₂, b₂, rfl⟩
    · rw [chainHead_concat] at h
      exact absurd h (hne _ _)
    · rw [List.concat_eq_append, chainHead_concat, chainHead_concat] at h
      obtain ⟨h1, h2⟩ := hinj _ _ _ _ h
      rw [List.concat_eq_append, ih h1, h2]

structure Env where
  H : ℕ → ℕ → ℕ
  h0 : ℕ
  admins : List ℕ

structure St where
  /-- the writer-controlled storage -/
  log : List ℕ
  /-- ghost: what was really appended -/
  truth : List ℕ
  /-- (head, ghost copy of the anchored log if anchored by the independent witness; none if writer-published) -/
  anchors : List (ℕ × Option (List ℕ))
  accepted : List (List ℕ)
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | append (e : ℕ)
  | rewrite (l : List ℕ)
  | anchor
  | writerAnchor (hd : ℕ)
  | verify (m : List ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  anchorCheck : Bool
  independentOnly : Bool
  noSuffix : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], [], [], false⟩

/-- the verifier's acceptance rule -/
abbrev Accepts (E : Env) (C : Checks) (s : St) (m : List ℕ) : Prop :=
  (∃ a ∈ s.anchors, a.1 = chainHead E.H E.h0 m ∧ (C.independentOnly = true → a.2.isSome = true)) ∨
  (C.anchorCheck = false ∧ chainHead E.H E.h0 m = chainHead E.H E.h0 s.log) ∨
  (C.noSuffix = false ∧ ∃ a ∈ s.anchors, a.2.isSome = true ∧
    ∃ k ∈ List.range (m.length + 1), a.1 = chainHead E.H E.h0 (m.take k))

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .append e => if s.halted ∧ C.haltCheck then s else { s with log := s.log ++ [e], truth := s.truth ++ [e] }
  | .rewrite l => if s.halted ∧ C.haltCheck then s else { s with log := l }
  | .anchor =>
    if s.halted ∧ C.haltCheck then s
    else { s with anchors := s.anchors ++ [(chainHead E.H E.h0 s.log, some s.log)] }
  | .writerAnchor hd => if s.halted ∧ C.haltCheck then s else { s with anchors := s.anchors ++ [(hd, none)] }
  | .verify m =>
    if s.halted ∧ C.haltCheck then s
    else if Accepts E C s m then { s with accepted := s.accepted ++ [m] } else s
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run E C s (o :: ops) = run E C (step E C s o) ops := rfl

/-! ## Invariant and safety -/

/-- an accepted manifest whose chain head matches an independently anchored log -/
def AccOk (E : Env) (s : St) (m : List ℕ) : Prop :=
  ∃ a ∈ s.anchors, ∃ l, a.2 = some l ∧ chainHead E.H E.h0 l = chainHead E.H E.h0 m

structure Inv (E : Env) (s : St) : Prop where
  anc : ∀ a ∈ s.anchors, ∀ l, a.2 = some l → a.1 = chainHead E.H E.h0 l
  acc : ∀ m ∈ s.accepted, AccOk E s m

theorem inv_init (E : Env) : Inv E init := ⟨by simp [init], by simp [init]⟩

theorem AccOk.mono {E : Env} {s t : St} (ha : s.anchors ⊆ t.anchors) {m : List ℕ} (h : AccOk E s m) : AccOk E t m := by
  obtain ⟨a, hm, l, h1, h2⟩ := h
  exact ⟨a, ha hm, l, h1, h2⟩

theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o) := by
  cases o with
  | anchor =>
    simp only [step]
    split_ifs
    · exact h
    · refine ⟨fun a ha l hl => ?_, fun m hm => (h.acc m hm).mono (fun _ x => List.mem_append_left _ x)⟩
      rcases List.mem_append.1 ha with ha | ha
      · exact h.anc a ha l hl
      · simp at ha; subst ha; simp at hl; subst hl; rfl
  | writerAnchor hd =>
    simp only [step]
    split_ifs
    · exact h
    · refine ⟨fun a ha l hl => ?_, fun m hm => (h.acc m hm).mono (fun _ x => List.mem_append_left _ x)⟩
      rcases List.mem_append.1 ha with ha | ha
      · exact h.anc a ha l hl
      · simp at ha; subst ha; simp at hl
  | verify m =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · refine ⟨h.anc, fun x hx => ?_⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact h.acc x hx
      · simp at hx; subst hx
        rcases h2 with ⟨a, ha, hhd, hs⟩ | ⟨hc, _⟩ | ⟨hc, _⟩
        · obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (hs rfl)
          exact ⟨a, ha, l, hl, (h.anc a ha l hl).symm.trans hhd⟩
        · exact absurd hc (by decide)
        · exact absurd hc (by decide)
    · exact h
  | append e => simp only [step]; split_ifs <;> first | exact h | exact ⟨h.anc, h.acc⟩
  | rewrite l => simp only [step]; split_ifs <;> first | exact h | exact ⟨h.anc, h.acc⟩
  | halt c => simp only [step]; split_ifs <;> first | exact h | exact ⟨h.anc, h.acc⟩

theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv E s o h)

/-- **SC-27 safety.** If the chain head is injective on the lists in play (accepted manifests and independently
anchored logs), every accepted manifest is exactly a log the independent witness anchored: modification, reordering,
truncation or extension after anchoring is never accepted. Adversary: TRACE_ARBITRARY (the writer rewrites storage,
publishes its own heads, chooses manifests). -/
theorem sc27_safe (E : Env) (ops : List Op)
    (hinj : Set.InjOn (chainHead E.H E.h0) {l | l ∈ (run E full init ops).accepted ∨
      ∃ a ∈ (run E full init ops).anchors, a.2 = some l}) :
    ∀ m ∈ (run E full init ops).accepted, ∃ a ∈ (run E full init ops).anchors, a.2 = some m := by
  intro m hm
  obtain ⟨a, ha, l, hl, heq⟩ := (run_inv E init ops (inv_init E)).acc m hm
  refine ⟨a, ha, ?_⟩
  rw [hl, hinj (Or.inr ⟨a, ha, hl⟩) (Or.inl hm) heq]

/-! ## Halt -/

theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s := by
  cases o with
  | halt c =>
    simp only [step]
    split_ifs
    · cases s; simp_all
    · rfl
  | _ => simp [step, full, hh]

/-- **Halt freezes**: once halted, no trace changes the state (nothing more is accepted). -/
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s := by
  induction ops with
  | nil => rfl
  | cons o ops ih => rw [run_cons, step_halted E s o hh, ih]

/-! ## Client of the shared gate interface -/

theorem accepted_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.accepted <+: (step E C s o).accepted := by
  cases o with
  | verify m =>
    simp only [step]
    split_ifs
    · exact List.prefix_refl _
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  | _ => simp only [step]; split_ifs <;> exact List.prefix_refl _

def sys (E : Env) : System St Op (List ℕ) where
  step := step E full
  effects := St.accepted

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := AccOk E
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => accepted_prefix E full s o
  inv_ok := fun _ h m hm => h.acc m hm

/-! ## Non-vacuity and necessity witnesses

Pair hash `H h e = 100 h + e + 1`, `h0 = 0`, admin 9: heads `[5] ↦ 6`, `[5,6] ↦ 607`, `[7] ↦ 8`. -/

def E0 : Env := ⟨fun h e => 100 * h + e + 1, 0, [9]⟩

/-- **Non-vacuity**: an anchored log is accepted. -/
theorem honest_accept : (run E0 full init [.append 5, .append 6, .anchor, .verify [5, 6]]).accepted = [[5, 6]] := by
  decide

/-- after anchoring, a modified or reordered log is not accepted -/
theorem tamper_after_anchor_detected :
    (run E0 full init [.append 5, .anchor, .rewrite [7], .verify [7]]).accepted = [] ∧
    (run E0 full init [.append 5, .append 6, .anchor, .rewrite [6, 5], .verify [6, 5]]).accepted = [] := by
  decide

/-- without an external anchor (checking the writer's current storage), a full rewrite is accepted -/
theorem no_anchor_rollback_breaks :
    let s := run E0 { full with anchorCheck := false } init [.append 5, .rewrite [7], .verify [7]]
    s.accepted = [[7]] ∧ s.truth = [5] ∧ s.anchors = [] := by
  decide

/-- accepting heads the writer published itself accepts a fabricated log -/
theorem self_signed_breaks :
    (run E0 { full with independentOnly := false } init [.append 5, .writerAnchor 8, .verify [7]]).accepted = [[7]] ∧
    (run E0 full init [.append 5, .writerAnchor 8, .verify [7]]).accepted = [] := by
  decide

/-- accepting an anchored prefix plus unanchored entries opens a tampering window -/
theorem unanchored_suffix_breaks :
    (run E0 { full with noSuffix := false } init [.append 5, .anchor, .verify [5, 99]]).accepted = [[5, 99]] ∧
    (run E0 full init [.append 5, .anchor, .verify [5, 99]]).accepted = [] := by
  decide

/-- with a colliding hash, a different log with the anchored head is accepted even with every check on -/
theorem collision_breaks :
    (run ⟨fun h e => (h + e) % 10, 0, [9]⟩ full init [.append 5, .anchor, .verify [2, 3]]).accepted = [[2, 3]] := by
  decide

/-- **Honest limit**: a rewrite BEFORE anchoring is anchored and accepted; entries are protected only once anchored -/
theorem rewrite_before_anchor_window :
    let s := run E0 full init [.append 5, .rewrite [7], .anchor, .verify [7]]
    s.accepted = [[7]] ∧ s.truth = [5] := by
  decide

/-- without the halt check, manifests are still accepted after a halt -/
theorem no_halt_check_breaks :
    (run E0 { full with haltCheck := false } init [.append 5, .anchor, .halt 9, .verify [5]]).accepted = [[5]] ∧
    (run E0 full init [.append 5, .anchor, .halt 9, .verify [5]]).accepted = [] := by
  decide

end ControlStack.SC27Chain

#print axioms ControlStack.SC27Chain.chainHead_injective
#print axioms ControlStack.SC27Chain.sc27_safe
#print axioms ControlStack.SC27Chain.halt_freezes
#print axioms ControlStack.SC27Chain.spec
#print axioms ControlStack.SC27Chain.honest_accept
#print axioms ControlStack.SC27Chain.tamper_after_anchor_detected
#print axioms ControlStack.SC27Chain.no_anchor_rollback_breaks
#print axioms ControlStack.SC27Chain.self_signed_breaks
#print axioms ControlStack.SC27Chain.unanchored_suffix_breaks
#print axioms ControlStack.SC27Chain.collision_breaks
#print axioms ControlStack.SC27Chain.rewrite_before_anchor_window
#print axioms ControlStack.SC27Chain.no_halt_check_breaks
