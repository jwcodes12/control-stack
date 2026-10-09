/-
SC-27 with an EXTENSION-ONLY witness (gap found by the SC-27 runtime test, scenarios/SC-27/evidence/run-1;
prereg/SC27-ANCHOR-CHAIN.md, "beyond the model").

`SC27Chain.sc27_safe` says every accepted manifest was anchored at SOME point. A periodic witness that anchors
whatever storage holds would therefore later anchor TAMPERED storage, which then becomes acceptable
(`periodic_anchor_launders`). The runtime witness (`scenarios/SC-27/harness/witness.py`) is extension-only: it anchors a
new state only if it extends the previously anchored state of that log, and otherwise records a fork alarm and does not
anchor. This file models that witness.

Model: storage `log` (writer-controlled: `append`, arbitrary `rewrite`); the witness's memory `last` (the last
anchored log); anchors (head, ghost copy of the anchored log), oldest first; fork alarms; accepted manifests.
`verify m` accepts iff `m`'s chain head equals an anchored head.

Results (deployed `full`, `extOnly = true`; adversary class TRACE_ARBITRARY: any appends, rewrites, anchoring times
and manifests):
- `anchors_chain`: the anchored logs form a chain under the prefix order (each is a prefix of every later one), and
  all are prefixes of the witness's latest anchor;
- `sc27_ext_safe`: with the chain head injective on the lists in play (`Set.InjOn`, as in `SC27Chain`), every
  accepted manifest is an anchored log AND a prefix of the witness's latest anchor, at every point of every trace. A
  log that does not extend an anchored state (modified, reordered or truncated after anchoring) is never anchored
  later (`tampered_never_anchored`), so it never becomes acceptable;
- `alarm_iff`: the witness raises a fork alarm exactly when current storage does not extend its last anchor;
- `honest_liveness`: if storage extends the last anchor (honest appends only), the next anchoring anchors it and the
  current log is accepted;
- `head_check_iff_prefix`: the runtime witness compares chain HEADS (the head of the first n₀ entries equals the
  previous head, and n₀ ≤ length); under the injectivity premise this is exactly the prefix check modelled here.
Witness: `periodic_anchor_launders` (without the extension check a rewrite is anchored and accepted; with it, a fork
alarm and nothing accepted).

Premises: witness independence (its memory and anchor log are outside the writer's control) and verifier integrity,
as in `SC27Chain`; collision resistance on the logs in play. Not claimed: that anchored evidence is true. A rewrite
BEFORE the first anchoring is still anchored (`SC27Chain.rewrite_before_anchor_window`). No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC27Chain

namespace ControlStack.SC27ExtensionOnly

open ControlStack.SC27Chain (chainHead)

structure Env where
  H : ℕ → ℕ → ℕ
  h0 : ℕ

structure St where
  log : List ℕ
  last : Option (List ℕ)
  /-- (head, ghost copy of the anchored log), oldest first -/
  anchors : List (ℕ × List ℕ)
  alarms : List (List ℕ)
  accepted : List (List ℕ)
deriving DecidableEq, Repr

inductive Op where
  | append (e : ℕ)
  | rewrite (l : List ℕ)
  | anchor
  | verify (m : List ℕ)
deriving DecidableEq, Repr

def init : St := ⟨[], none, [], [], []⟩

/-- does the current storage extend the last anchored state? -/
def extendsLast (s : St) : Bool := match s.last with
  | none => true
  | some l0 => l0.isPrefixOf s.log

def doAnchor (E : Env) (s : St) : St :=
  { s with last := some s.log, anchors := s.anchors ++ [(chainHead E.H E.h0 s.log, s.log)] }

/-- `extOnly`: the extension-only witness (deployed); `false`: anchor whatever storage holds -/
def step (E : Env) (extOnly : Bool) (s : St) : Op → St
  | .append e => { s with log := s.log ++ [e] }
  | .rewrite l => { s with log := l }
  | .anchor =>
    if extOnly then (if extendsLast s then doAnchor E s else { s with alarms := s.alarms ++ [s.log] })
    else doAnchor E s
  | .verify m =>
    if ∃ a ∈ s.anchors, a.1 = chainHead E.H E.h0 m then { s with accepted := s.accepted ++ [m] } else s

def run (E : Env) (extOnly : Bool) (s : St) (ops : List Op) : St := ops.foldl (step E extOnly) s

theorem run_cons (E : Env) (b : Bool) (s : St) (o : Op) (ops : List Op) :
    run E b s (o :: ops) = run E b (step E b s o) ops := rfl

theorem extendsLast_iff (s : St) : extendsLast s = true ↔ ∀ l0, s.last = some l0 → l0 <+: s.log := by
  unfold extendsLast
  cases s.last with
  | none => simp
  | some l0 => simp [List.isPrefixOf_iff_prefix]

/-! ## Invariant -/

structure Inv (E : Env) (s : St) : Prop where
  heads : ∀ a ∈ s.anchors, a.1 = chainHead E.H E.h0 a.2
  chain : s.anchors.Pairwise (fun a b => a.2 <+: b.2)
  toLast : ∀ a ∈ s.anchors, ∃ l, s.last = some l ∧ a.2 <+: l
  lastAnch : ∀ l, s.last = some l → ∃ a ∈ s.anchors, a.2 = l
  acc : ∀ m ∈ s.accepted, ∃ a ∈ s.anchors, a.1 = chainHead E.H E.h0 m

theorem inv_init (E : Env) : Inv E init := ⟨by simp [init], by simp [init], by simp [init], by simp [init], by simp [init]⟩

theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E true s o) := by
  cases o with
  | append e => exact ⟨h.heads, h.chain, h.toLast, h.lastAnch, h.acc⟩
  | rewrite l => exact ⟨h.heads, h.chain, h.toLast, h.lastAnch, h.acc⟩
  | anchor =>
    simp only [step, ite_true]
    split_ifs with hx
    · rw [extendsLast_iff] at hx
      refine ⟨fun a ha => ?_, ?_, fun a ha => ?_, fun l hl => ?_, fun m hm => ?_⟩
      · rcases List.mem_append.1 ha with ha | ha
        · exact h.heads a ha
        · simp at ha; subst ha; rfl
      · simp only [doAnchor]
        refine List.pairwise_append.2 ⟨h.chain, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
        simp at hb; subst hb
        obtain ⟨l, hl, hp⟩ := h.toLast a ha
        exact hp.trans (hx l hl)
      · refine ⟨s.log, rfl, ?_⟩
        rcases List.mem_append.1 ha with ha | ha
        · obtain ⟨l, hl, hp⟩ := h.toLast a ha
          exact hp.trans (hx l hl)
        · simp at ha; subst ha; exact List.prefix_refl _
      · simp only [doAnchor, Option.some.injEq] at hl; subst hl
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
      · obtain ⟨a, ha, he⟩ := h.acc m hm
        exact ⟨a, List.mem_append_left _ ha, he⟩
    · exact ⟨h.heads, h.chain, h.toLast, h.lastAnch, h.acc⟩
  | verify m =>
    simp only [step]
    split_ifs with hv
    · refine ⟨h.heads, h.chain, h.toLast, h.lastAnch, fun x hx => ?_⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact h.acc x hx
      · simp at hx; subst hx; exact hv
    · exact h

theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E true s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv E s o h)

/-! ## (1) The anchored logs form a chain -/

/-- **Anchors form a prefix chain**: each anchored log is a prefix of every later anchored log and of the witness's
latest anchor. -/
theorem anchors_chain (E : Env) (ops : List Op) :
    (run E true init ops).anchors.Pairwise (fun a b => a.2 <+: b.2) ∧
      ∀ a ∈ (run E true init ops).anchors, ∃ l, (run E true init ops).last = some l ∧ a.2 <+: l :=
  let h := run_inv E init ops (inv_init E)
  ⟨h.chain, h.toLast⟩

/-! ## (2) Strengthened safety -/

/-- **SC-27, extension-only.** If the chain head is injective on the accepted manifests and the anchored logs, every
accepted manifest is an anchored log and a prefix of the witness's latest anchor. -/
theorem sc27_ext_safe (E : Env) (ops : List Op)
    (hinj : Set.InjOn (chainHead E.H E.h0) {l | l ∈ (run E true init ops).accepted ∨
      ∃ a ∈ (run E true init ops).anchors, a.2 = l}) :
    ∀ m ∈ (run E true init ops).accepted,
      (∃ a ∈ (run E true init ops).anchors, a.2 = m) ∧ ∃ l, (run E true init ops).last = some l ∧ m <+: l := by
  intro m hm
  have h := run_inv E init ops (inv_init E)
  obtain ⟨a, ha, he⟩ := h.acc m hm
  have hm' : a.2 = m := hinj (Or.inr ⟨a, ha, rfl⟩) (Or.inl hm) ((h.heads a ha).symm.trans he)
  obtain ⟨l, hl, hp⟩ := h.toLast a ha
  exact ⟨⟨a, ha, hm'⟩, l, hl, hm' ▸ hp⟩

/-- **A log that does not extend an anchored state is never anchored later.** If `l` is anchored and `l'` is not an
extension of it, no later anchor is `l'`: every later anchor extends `l`. -/
theorem tampered_never_anchored (E : Env) (s : St) (hs : Inv E s) (ops : List Op) (l : List ℕ)
    (hl : ∃ a ∈ s.anchors, a.2 = l) :
    ∀ a ∈ (run E true s ops).anchors, a ∈ s.anchors ∨ l <+: a.2 := by
  induction ops generalizing s with
  | nil => intro a ha; exact Or.inl ha
  | cons o ops ih =>
    intro a ha
    rw [run_cons] at ha
    have hs' := step_inv E s o hs
    have hl' : ∃ a ∈ (step E true s o).anchors, a.2 = l := by
      obtain ⟨b, hb, rfl⟩ := hl
      refine ⟨b, ?_, rfl⟩
      cases o with
      | anchor =>
        simp only [step, ite_true]; split_ifs
        · exact List.mem_append_left _ hb
        · exact hb
      | verify m => simp only [step]; split_ifs <;> exact hb
      | _ => exact hb
    rcases ih _ hs' hl' a ha with h1 | h1
    · -- a was added by this step o (or already present)
      cases o with
      | anchor =>
        simp only [step, ite_true] at h1; split_ifs at h1 with hx
        · rcases List.mem_append.1 h1 with h1 | h1
          · exact Or.inl h1
          · simp at h1; subst h1
            right
            obtain ⟨b, hb, rfl⟩ := hl
            rw [extendsLast_iff] at hx
            obtain ⟨l0, hl0, hp⟩ := hs.toLast b hb
            exact hp.trans (hx l0 hl0)
        · exact Or.inl h1
      | verify m => simp only [step] at h1; split_ifs at h1 <;> exact Or.inl h1
      | _ => exact Or.inl h1
    · exact Or.inr h1

/-! ## (3) Fork alarms -/

/-- **Alarm soundness and completeness**: an anchoring step raises a fork alarm exactly when current storage does not
extend the last anchor; then nothing is anchored. -/
theorem alarm_iff (E : Env) (s : St) :
    ((step E true s .anchor).alarms = s.alarms ++ [s.log] ↔ extendsLast s = false) ∧
      (extendsLast s = false → (step E true s .anchor).anchors = s.anchors) := by
  refine ⟨⟨fun h => ?_, fun h => by simp [step, h]⟩, fun h => by simp [step, h]⟩
  by_contra hx
  have hx' : extendsLast s = true := by simpa using hx
  simp [step, hx', doAnchor] at h

/-! ## (4) Honest liveness -/

/-- **Honest liveness.** If storage extends the last anchor (only honest appends since), the next anchoring anchors it
and the current log is then accepted. -/
theorem honest_liveness (E : Env) (s : St) (hx : extendsLast s = true) :
    s.log ∈ (run E true s [.anchor, .verify s.log]).accepted ∧ (run E true s [.anchor, .verify s.log]).last = some s.log := by
  simp [run, step, hx, doAnchor]

/-- appends preserve extension: honest appends after an anchor keep the storage an extension -/
theorem append_extends (s : St) (e : ℕ) (hx : extendsLast s = true) : extendsLast { s with log := s.log ++ [e] } = true := by
  rw [extendsLast_iff] at hx ⊢
  intro l0 hl0
  exact (hx l0 hl0).trans (List.prefix_append _ _)

/-! ## Runtime correspondence: the head check -/

/-- **The runtime's head check is the prefix check** under collision resistance: the head of the first n₀ entries of
`l` equals the head of `l0` and n₀ = |l0| ≤ |l| iff `l0` is a prefix of `l`, provided the chain head is injective on
`{l0, l.take |l0|}`. -/
theorem head_check_iff_prefix (H : ℕ → ℕ → ℕ) (h0 : ℕ) (l0 l : List ℕ)
    (hinj : Set.InjOn (chainHead H h0) {l0, l.take l0.length}) :
    (l0.length ≤ l.length ∧ chainHead H h0 (l.take l0.length) = chainHead H h0 l0) ↔ l0 <+: l := by
  constructor
  · rintro ⟨_, hh⟩
    have := hinj (by simp) (by simp) hh
    rw [← this]
    exact List.take_prefix _ _
  · intro hp
    refine ⟨hp.length_le, ?_⟩
    have e : l.take l0.length = l0 := (List.prefix_iff_eq_take.1 hp).symm
    rw [e]

/-! ## Witness: the periodic witness launders a rewrite -/

def E0 : Env := ⟨fun h e => 100 * h + e + 1, 0⟩

/-- **Periodic anchoring launders a rewrite**; the extension-only witness raises a fork alarm instead. -/
theorem periodic_anchor_launders :
    (run E0 false init [.append 5, .anchor, .rewrite [7], .anchor, .verify [7]]).accepted = [[7]] ∧
    (run E0 true init [.append 5, .anchor, .rewrite [7], .anchor, .verify [7]]).accepted = [] ∧
    (run E0 true init [.append 5, .anchor, .rewrite [7], .anchor, .verify [7]]).alarms = [[7]] := by
  decide

/-- **Non-vacuity**: honest appends are anchored and accepted at each period. -/
theorem honest_periods :
    (run E0 true init [.append 5, .anchor, .verify [5], .append 6, .anchor, .verify [5, 6]]).accepted =
      [[5], [5, 6]] := by
  decide

end ControlStack.SC27ExtensionOnly

#print axioms ControlStack.SC27ExtensionOnly.anchors_chain
#print axioms ControlStack.SC27ExtensionOnly.sc27_ext_safe
#print axioms ControlStack.SC27ExtensionOnly.tampered_never_anchored
#print axioms ControlStack.SC27ExtensionOnly.alarm_iff
#print axioms ControlStack.SC27ExtensionOnly.honest_liveness
#print axioms ControlStack.SC27ExtensionOnly.append_extends
#print axioms ControlStack.SC27ExtensionOnly.head_check_iff_prefix
#print axioms ControlStack.SC27ExtensionOnly.periodic_anchor_launders
#print axioms ControlStack.SC27ExtensionOnly.honest_periods
