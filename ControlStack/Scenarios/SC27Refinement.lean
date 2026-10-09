/-
SC-27 refinement: the runtime's event structure (scenarios/SC-27/harness/chain.py, writer.py, witness.py,
verifier.py, reconcile.py; prereg/SC27-ANCHOR-CHAIN.md) as a concrete machine, with a forward simulation into
`SC27ExtensionOnly`. This is criterion 3, as for SC-16, SC-18, SC-25, SC-26 and SC-28.

Concrete machine (`CSt`, `COp`, `stepC`, one log):
- **Writer.** It owns its storage, the entries of `log-<name>.jsonl`. Heads are recomputed by every reader, never
  trusted.
  - `append e`: append an entry.
  - `rewrite l`: replace the storage (the writer controls its files).
  - `publish h`: add a head to the writer's own `published-heads.jsonl`.
- **Witness.** `examine` reads the storage read-only. Its memory is only `(n₀, h₀)`, the length and chain head of
  its last anchor; `ghostLast` is a ghost copy of that list, used only by α. Branches:
  - empty storage: no record (`{"kind": "empty"}`);
  - `len = n₀` and head = h₀: unchanged, no record;
  - `len < n₀`, or the head of the first n₀ entries ≠ h₀: a FORK record, and nothing is anchored;
  - otherwise: an ANCHOR record (head, n). Each record is `fsync`'d to the witness's OWN log.
- **Verifier.** `verify m` recomputes the chain head of the manifest. It accepts iff that head is an ANCHOR head in
  the WITNESS's log. Flag `trustWriter`, the runtime control `--writer-heads`: it also accepts heads the writer
  published itself.

α (into `SC27ExtensionOnly.St`):
- storage ↦ log;
- `ghostLast` ↦ last;
- anchor records ↦ anchors (head, ghost list);
- fork records ↦ alarms;
- accepted ↦ accepted.
Event map:
- append ↦ [append]; rewrite ↦ [rewrite]; verify ↦ [verify];
- examine ↦ [anchor] when it writes a record; [] when it writes none (empty or unchanged);
- publish ↦ [].

The premise `TraceInj`: at every examine, the chain head is injective on {last anchored list, first n₀ entries of
storage}. Only the ANCHOR branch needs it. It is exactly the premise of `head_check_iff_prefix`, which turns the
runtime's head comparison into the model's prefix check. Collision resistance of SHA-256 on the lists in play; not
global injectivity.

Results (deployed, `trustWriter = false`; adversary class TRACE_ARBITRARY: any appends, rewrites, published heads,
examine times, and manifests):
- `simulation`, `simulation_run`.
- `concrete_ext_safe` (`sc27_ext_safe` transferred): every accepted manifest is a list the witness anchored, and a
  prefix of its latest anchor. Premise: head injective on the accepted and anchored lists, as in the model.
- `concrete_tampered_never_anchored` (`tampered_never_anchored` transferred): once a list is anchored, every later
  anchor record extends it.
- `concrete_alarm_iff` (alarm soundness and completeness). For NON-EMPTY storage, an examine writes a fork record
  exactly when storage does not extend the last anchor; the "unchanged" no-op happens only when it does.
- `empty_truncation_silent` (a runtime gap, recorded): the witness checks for empty storage BEFORE comparing with its
  last anchor. Truncating an anchored log to empty therefore raises NO fork alarm, where the model raises one.
  Safety is unaffected, since nothing is anchored, and so is the verifier. Only alarm completeness fails, for this
  one case.
- `writer_heads_breaks` (the self-anchoring control): a verifier that also trusts the writer's published heads
  accepts a rewritten log; the deployed verifier refuses it.
- `honest_concrete`: honest appends are anchored and accepted at each period (non-vacuity).

Premises (as in `SC27Chain` and `SC27ExtensionOnly`):
- witness independence: the writer cannot write the witness's memory or log;
- verifier integrity: it reads only the witness's log;
- `fsync` durability of the witness log;
- collision resistance on the lists in play.

Not covered:
- that the Python implements this machine (TESTED: run-1 and reconcile.py);
- several logs: each is independent and modelled singly;
- partial lines from concurrent appends (`read_entries` drops them).
Classical forward simulation; no novelty.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC27ExtensionOnly

namespace ControlStack.SC27Refinement

open ControlStack.SC27Chain (chainHead)
open ControlStack.SC27ExtensionOnly (Env)

/-! ## The concrete machine -/

/-- a record in the witness's own log; `g` is a ghost copy of the storage examined -/
inductive WRec where
  | anc (head n : ℕ) (g : List ℕ)
  | fork (head n anchoredHead anchoredN : ℕ) (g : List ℕ)
deriving DecidableEq, Repr

structure CSt where
  store : List ℕ
  pub : List ℕ
  /-- the witness's memory: (n₀, h₀) of its last anchor -/
  wlast : Option (ℕ × ℕ)
  /-- ghost: the last anchored list -/
  ghostLast : Option (List ℕ)
  wlog : List WRec
  accepted : List (List ℕ)
deriving DecidableEq, Repr

inductive COp where
  | append (e : ℕ)
  | rewrite (l : List ℕ)
  | publish (h : ℕ)
  | examine
  | verify (m : List ℕ)
deriving DecidableEq, Repr

def cinit : CSt := ⟨[], [], none, none, [], []⟩

/-- the anchor records of a witness log: (head, ghost list) -/
def ancs (l : List WRec) : List (ℕ × List ℕ) :=
  l.filterMap fun r => match r with
    | .anc h _ g => some (h, g)
    | _ => none

/-- the fork records of a witness log -/
def forks (l : List WRec) : List (List ℕ) :=
  l.filterMap fun r => match r with
    | .fork _ _ _ _ g => some g
    | _ => none

@[simp] theorem ancs_anc (l : List WRec) (h n : ℕ) (g : List ℕ) : ancs (l ++ [.anc h n g]) = ancs l ++ [(h, g)] := by
  simp [ancs, List.filterMap_append]
@[simp] theorem ancs_fork (l : List WRec) (h n ah an : ℕ) (g : List ℕ) :
    ancs (l ++ [.fork h n ah an g]) = ancs l := by
  simp [ancs, List.filterMap_append]
@[simp] theorem forks_anc (l : List WRec) (h n : ℕ) (g : List ℕ) : forks (l ++ [.anc h n g]) = forks l := by
  simp [forks, List.filterMap_append]
@[simp] theorem forks_fork (l : List WRec) (h n ah an : ℕ) (g : List ℕ) :
    forks (l ++ [.fork h n ah an g]) = forks l ++ [g] := by
  simp [forks, List.filterMap_append]

def anchorIt (E : Env) (s : CSt) : CSt :=
  { s with wlast := some (s.store.length, chainHead E.H E.h0 s.store), ghostLast := some s.store,
           wlog := s.wlog ++ [.anc (chainHead E.H E.h0 s.store) s.store.length s.store] }

def forkIt (E : Env) (s : CSt) (n0 h0 : ℕ) : CSt :=
  { s with wlog := s.wlog ++ [.fork (chainHead E.H E.h0 s.store) s.store.length h0 n0 s.store] }

/-- the witness's `examine` (witness.py), comparing chain heads -/
def examine (E : Env) (s : CSt) : CSt :=
  if s.store = [] then s
  else match s.wlast with
    | none => anchorIt E s
    | some (n0, h0) =>
      if s.store.length = n0 ∧ chainHead E.H E.h0 s.store = h0 then s
      else if s.store.length < n0 ∨ chainHead E.H E.h0 (s.store.take n0) ≠ h0 then forkIt E s n0 h0
      else anchorIt E s

/-- `trustWriter`: the `--writer-heads` control (false when deployed) -/
def stepC (E : Env) (trustWriter : Bool) (s : CSt) : COp → CSt
  | .append e => { s with store := s.store ++ [e] }
  | .rewrite l => { s with store := l }
  | .publish h => { s with pub := s.pub ++ [h] }
  | .examine => examine E s
  | .verify m =>
    if (∃ a ∈ ancs s.wlog, a.1 = chainHead E.H E.h0 m) ∨ (trustWriter = true ∧ chainHead E.H E.h0 m ∈ s.pub) then
      { s with accepted := s.accepted ++ [m] }
    else s

def runC (E : Env) (b : Bool) (s : CSt) (ops : List COp) : CSt := ops.foldl (stepC E b) s

theorem runC_cons (E : Env) (b : Bool) (s : CSt) (o : COp) (ops : List COp) :
    runC E b s (o :: ops) = runC E b (stepC E b s o) ops := rfl

theorem runC_append (E : Env) (b : Bool) (s : CSt) (x y : List COp) :
    runC E b s (x ++ y) = runC E b (runC E b s x) y := by
  simp [runC, List.foldl_append]

/-! ## Invariant and the injectivity premise -/

/-- the witness's memory is the length and head of the (ghost) last anchored list -/
def CInv (E : Env) (s : CSt) : Prop := s.wlast = s.ghostLast.map (fun l => (l.length, chainHead E.H E.h0 l))

theorem cinv_init (E : Env) : CInv E cinit := rfl

theorem cinv_step (E : Env) (b : Bool) (s : CSt) (o : COp) (h : CInv E s) : CInv E (stepC E b s o) := by
  cases o with
  | examine =>
    simp only [stepC, examine]
    split_ifs
    · exact h
    · cases hw : s.wlast with
      | none => exact rfl
      | some p =>
        obtain ⟨n0, h0⟩ := p
        dsimp only
        split_ifs
        · exact h
        · exact h
        · exact rfl
  | verify m => simp only [stepC]; split_ifs <;> exact h
  | _ => exact h

theorem cinv_run (E : Env) (b : Bool) (s : CSt) (ops : List COp) (h : CInv E s) : CInv E (runC E b s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [runC_cons]; exact ih _ (cinv_step E b s o h)

/-- collision resistance at an examine: injective on {last anchored list, the same-length prefix of storage} -/
def ExamInj (E : Env) (s : CSt) : Prop :=
  ∀ l0, s.ghostLast = some l0 → Set.InjOn (chainHead E.H E.h0) {l0, s.store.take l0.length}

/-- `ExamInj` at every examine of a (deployed) trace -/
def TraceInj (E : Env) : CSt → List COp → Prop
  | _, [] => True
  | s, o :: ops => (o = .examine → ExamInj E s) ∧ TraceInj E (stepC E false s o) ops

theorem traceInj_append (E : Env) (s : CSt) (x y : List COp) :
    TraceInj E s (x ++ y) ↔ TraceInj E s x ∧ TraceInj E (runC E false s x) y := by
  induction x generalizing s with
  | nil => simp [TraceInj, runC]
  | cons o x ih => simp only [List.cons_append, TraceInj, ih, runC_cons]; exact and_assoc.symm

/-! ## Abstraction and forward simulation -/

def α (s : CSt) : SC27ExtensionOnly.St := ⟨s.store, s.ghostLast, ancs s.wlog, forks s.wlog, s.accepted⟩

def opsOf (E : Env) (s : CSt) : COp → List SC27ExtensionOnly.Op
  | .append e => [.append e]
  | .rewrite l => [.rewrite l]
  | .publish _ => []
  | .examine =>
    if s.store = [] then []
    else match s.wlast with
      | none => [.anchor]
      | some (n0, h0) => if s.store.length = n0 ∧ chainHead E.H E.h0 s.store = h0 then [] else [.anchor]
  | .verify m => [.verify m]

theorem extends_of_prefix {s : CSt} {l0 : List ℕ} (hg : s.ghostLast = some l0) (hp : l0 <+: s.store) :
    SC27ExtensionOnly.extendsLast (α s) = true := by
  simp [SC27ExtensionOnly.extendsLast, α, hg, List.isPrefixOf_iff_prefix, hp]

theorem not_extends_of_not_prefix {s : CSt} {l0 : List ℕ} (hg : s.ghostLast = some l0) (hp : ¬ l0 <+: s.store) :
    SC27ExtensionOnly.extendsLast (α s) = false := by
  simp only [SC27ExtensionOnly.extendsLast, α, hg]
  cases hb : l0.isPrefixOf s.store
  · rfl
  · exact absurd (List.isPrefixOf_iff_prefix.1 hb) hp

theorem simulation (E : Env) (s : CSt) (o : COp) (h : CInv E s) (hinj : o = .examine → ExamInj E s) :
    α (stepC E false s o) = SC27ExtensionOnly.run E true (α s) (opsOf E s o) := by
  cases o with
  | append e => rfl
  | rewrite l => rfl
  | publish x => rfl
  | verify m =>
    simp only [stepC, opsOf, SC27ExtensionOnly.run, List.foldl_cons, List.foldl_nil, SC27ExtensionOnly.step]
    by_cases hv : ∃ a ∈ ancs s.wlog, a.1 = chainHead E.H E.h0 m
    · rw [ite_eq_left (Or.inl hv), ite_eq_left (show ∃ a ∈ (α s).anchors, a.1 = chainHead E.H E.h0 m from hv)]
      rfl
    · rw [ite_eq_right (by simpa using hv), ite_eq_right (show ¬ ∃ a ∈ (α s).anchors, a.1 = _ from hv)]
  | examine =>
    have hI := hinj rfl
    simp only [stepC, examine, opsOf]
    by_cases he : s.store = []
    · rw [ite_eq_left he, ite_eq_left he]; rfl
    · rw [ite_eq_right he, ite_eq_right he]
      cases hg : s.ghostLast with
      | none =>
        have hw : s.wlast = none := by rw [h, hg]; rfl
        rw [hw]
        dsimp only
        simp only [SC27ExtensionOnly.run, List.foldl_cons, List.foldl_nil, SC27ExtensionOnly.step, ite_true]
        have hx : SC27ExtensionOnly.extendsLast (α s) = true := by simp [SC27ExtensionOnly.extendsLast, α, hg]
        rw [ite_eq_left hx]
        simp [anchorIt, α, SC27ExtensionOnly.doAnchor]
      | some l0 =>
        have hw : s.wlast = some (l0.length, chainHead E.H E.h0 l0) := by rw [h, hg]; rfl
        rw [hw]
        dsimp only
        by_cases hu : s.store.length = l0.length ∧ chainHead E.H E.h0 s.store = chainHead E.H E.h0 l0
        · rw [ite_eq_left hu, ite_eq_left hu]; rfl
        · rw [ite_eq_right hu, ite_eq_right hu]
          simp only [SC27ExtensionOnly.run, List.foldl_cons, List.foldl_nil, SC27ExtensionOnly.step, ite_true]
          by_cases hf : s.store.length < l0.length ∨
              chainHead E.H E.h0 (s.store.take l0.length) ≠ chainHead E.H E.h0 l0
          · rw [ite_eq_left hf]
            have hnp : ¬ l0 <+: s.store := by
              intro hp
              have hc := (SC27ExtensionOnly.head_check_iff_prefix E.H E.h0 l0 s.store
                (fun _ ha _ hb hab => by
                  rcases ha with rfl | ha <;> rcases hb with rfl | hb
                  · rfl
                  · simp only [Set.mem_singleton_iff] at hb; rw [hb, ← List.prefix_iff_eq_take.1 hp]
                  · simp only [Set.mem_singleton_iff] at ha; rw [ha, ← List.prefix_iff_eq_take.1 hp]
                  · simp only [Set.mem_singleton_iff] at ha hb; rw [ha, hb])).2 hp
              rcases hf with hf | hf
              · omega
              · exact hf hc.2
            rw [ite_eq_right (by rw [not_extends_of_not_prefix hg hnp]; simp)]
            simp [forkIt, α]
          · rw [ite_eq_right hf]
            have hc : l0.length ≤ s.store.length ∧
                chainHead E.H E.h0 (s.store.take l0.length) = chainHead E.H E.h0 l0 := by
              have h2 := not_or.1 hf
              exact ⟨Nat.le_of_not_lt h2.1, not_not.1 h2.2⟩
            have hp := (SC27ExtensionOnly.head_check_iff_prefix E.H E.h0 l0 s.store (hI l0 hg)).1 hc
            rw [ite_eq_left (extends_of_prefix hg hp)]
            simp [anchorIt, α, SC27ExtensionOnly.doAnchor]

def absTrace (E : Env) : CSt → List COp → List SC27ExtensionOnly.Op
  | _, [] => []
  | s, o :: ops => opsOf E s o ++ absTrace E (stepC E false s o) ops

theorem simulation_run (E : Env) (s : CSt) (ops : List COp) (h : CInv E s) (ht : TraceInj E s ops) :
    α (runC E false s ops) = SC27ExtensionOnly.run E true (α s) (absTrace E s ops) := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    change α (runC E false (stepC E false s o) ops) = _
    rw [ih _ (cinv_step E false s o h) ht.2, simulation E s o h ht.1]
    simp [absTrace, SC27ExtensionOnly.run, List.foldl_append]

theorem α_cinit : α cinit = SC27ExtensionOnly.init := rfl

/-! ## Transfer -/

/-- **SC-27 extension-only safety for the concrete witness and verifier** (`sc27_ext_safe` transferred). Under
`TraceInj` (the witness's head checks) and injectivity on the accepted and anchored lists, every accepted manifest is
a list the witness anchored, and a prefix of its latest anchor. -/
theorem concrete_ext_safe (E : Env) (ops : List COp) (ht : TraceInj E cinit ops)
    (hinj : Set.InjOn (chainHead E.H E.h0) {l | l ∈ (runC E false cinit ops).accepted ∨
      ∃ a ∈ ancs (runC E false cinit ops).wlog, a.2 = l}) :
    ∀ m ∈ (runC E false cinit ops).accepted,
      (∃ a ∈ ancs (runC E false cinit ops).wlog, a.2 = m) ∧
        ∃ l, (runC E false cinit ops).ghostLast = some l ∧ m <+: l := by
  have e := simulation_run E cinit ops (cinv_init E) ht
  rw [α_cinit] at e
  have key := SC27ExtensionOnly.sc27_ext_safe E (absTrace E cinit ops)
  rw [← e] at key
  exact key hinj

/-- **Tampered storage is never anchored later** (`tampered_never_anchored` transferred): once a list `l` is anchored
in the witness log, every anchor record written afterwards is an earlier one or extends `l`. -/
theorem concrete_tampered_never_anchored (E : Env) (pre post : List COp) (ht : TraceInj E cinit (pre ++ post))
    (l : List ℕ) (hl : ∃ a ∈ ancs (runC E false cinit pre).wlog, a.2 = l) :
    ∀ a ∈ ancs (runC E false cinit (pre ++ post)).wlog, a ∈ ancs (runC E false cinit pre).wlog ∨ l <+: a.2 := by
  rw [traceInj_append] at ht
  have hc := cinv_run E false cinit pre (cinv_init E)
  have e1 := simulation_run E cinit pre (cinv_init E) ht.1
  rw [α_cinit] at e1
  have hinv : SC27ExtensionOnly.Inv E (α (runC E false cinit pre)) := by
    rw [e1]; exact SC27ExtensionOnly.run_inv E _ _ (SC27ExtensionOnly.inv_init E)
  have e2 := simulation_run E _ post hc ht.2
  rw [runC_append]
  have key := SC27ExtensionOnly.tampered_never_anchored E (α (runC E false cinit pre)) hinv
    (absTrace E (runC E false cinit pre) post) l hl
  rw [← e2] at key
  exact key

/-- **Fork alarms, concrete** (soundness and completeness of the head-comparing witness on NON-EMPTY storage, after
the first anchor). With the injectivity premise at this examine:
- a fork record is written exactly when storage does not extend the last anchor;
- nothing is anchored then;
- the silent "unchanged" case happens only when storage is the last anchor. -/
theorem concrete_alarm_iff (E : Env) (s : CSt) (h : CInv E s) (hI : ExamInj E s) (hne : s.store ≠ [])
    (l0 : List ℕ) (hg : s.ghostLast = some l0) :
    (forks (stepC E false s .examine).wlog = forks s.wlog ++ [s.store] ↔ ¬ l0 <+: s.store) ∧
      (¬ l0 <+: s.store → ancs (stepC E false s .examine).wlog = ancs s.wlog) := by
  have hsim := simulation E s .examine h (fun _ => hI)
  have hw : s.wlast = some (l0.length, chainHead E.H E.h0 l0) := by rw [h, hg]; rfl
  have hfa : forks (stepC E false s .examine).wlog =
      (SC27ExtensionOnly.run E true (α s) (opsOf E s .examine)).alarms := congrArg SC27ExtensionOnly.St.alarms hsim
  have han : ancs (stepC E false s .examine).wlog =
      (SC27ExtensionOnly.run E true (α s) (opsOf E s .examine)).anchors := congrArg SC27ExtensionOnly.St.anchors hsim
  have hops : opsOf E s .examine =
      if s.store.length = l0.length ∧ chainHead E.H E.h0 s.store = chainHead E.H E.h0 l0 then [] else [.anchor] := by
    unfold opsOf; rw [ite_eq_right hne, hw]
  by_cases hp : l0 <+: s.store
  · have hx := extends_of_prefix hg hp
    have hfe : forks (stepC E false s .examine).wlog = forks s.wlog := by
      rw [hfa, hops]
      split_ifs
      · rfl
      · simp only [SC27ExtensionOnly.run, List.foldl_cons, List.foldl_nil, SC27ExtensionOnly.step, ite_true]
        rw [ite_eq_left hx]; rfl
    refine ⟨⟨fun hf => ?_, fun hn => absurd hp hn⟩, fun hn => absurd hp hn⟩
    rw [hfe] at hf
    have := congrArg List.length hf
    simp at this
  · have hx := not_extends_of_not_prefix hg hp
    have hu : ¬ (s.store.length = l0.length ∧ chainHead E.H E.h0 s.store = chainHead E.H E.h0 l0) := by
      rintro ⟨h1, h2⟩
      apply hp
      have ht : s.store.take l0.length = s.store := by rw [← h1, List.take_length]
      have := hI l0 hg (by simp) (by simp) (show chainHead E.H E.h0 l0 = chainHead E.H E.h0 (s.store.take l0.length)
        by rw [ht, h2])
      rw [this, ht]
    rw [hops, ite_eq_right hu] at hfa han
    simp only [SC27ExtensionOnly.run, List.foldl_cons, List.foldl_nil, SC27ExtensionOnly.step, ite_true] at hfa han
    rw [ite_eq_right (by rw [hx]; simp)] at hfa han
    exact ⟨⟨fun _ => hp, fun _ => hfa⟩, fun _ => han⟩

/-! ## Witnesses -/

def E0 : Env := SC27ExtensionOnly.E0

/-- **The runtime witness is silent on truncation to empty.** After anchoring [5], the writer truncates its storage to
[]: the witness writes no fork record (it returns `empty` first), where the model raises an alarm. Nothing is anchored
and nothing is accepted either way. -/
theorem empty_truncation_silent :
    forks (runC E0 false cinit [.append 5, .examine, .rewrite [], .examine]).wlog = [] ∧
      (SC27ExtensionOnly.run E0 true SC27ExtensionOnly.init [.append 5, .anchor, .rewrite [], .anchor]).alarms = [[]] ∧
      ancs (runC E0 false cinit [.append 5, .examine, .rewrite [], .examine]).wlog = [(1 * 0 + 5 + 1, [5])] := by
  decide

/-- **Self-anchoring control** (`--writer-heads`): the writer anchors [5] with the witness, rewrites to [7], and
publishes [7]'s head itself. A verifier that trusts published heads accepts [7]. The deployed verifier refuses it,
and the witness records a fork. -/
theorem writer_heads_breaks :
    let ops : List COp := [.append 5, .examine, .rewrite [7], .publish (chainHead E0.H E0.h0 [7]), .examine,
      .verify [7]]
    (runC E0 true cinit ops).accepted = [[7]] ∧ (runC E0 false cinit ops).accepted = [] ∧
      forks (runC E0 false cinit ops).wlog = [[7]] := by
  decide

/-- **Non-vacuity**: honest appends are anchored and accepted at each period; an unchanged log writes no record. -/
theorem honest_concrete :
    let t := runC E0 false cinit [.append 5, .examine, .verify [5], .examine, .append 6, .examine, .verify [5, 6]]
    t.accepted = [[5], [5, 6]] ∧ (ancs t.wlog).length = 2 ∧ forks t.wlog = [] := by
  decide

end ControlStack.SC27Refinement

#print axioms ControlStack.SC27Refinement.simulation
#print axioms ControlStack.SC27Refinement.simulation_run
#print axioms ControlStack.SC27Refinement.concrete_ext_safe
#print axioms ControlStack.SC27Refinement.concrete_tampered_never_anchored
#print axioms ControlStack.SC27Refinement.concrete_alarm_iff
#print axioms ControlStack.SC27Refinement.empty_truncation_silent
#print axioms ControlStack.SC27Refinement.writer_heads_breaks
#print axioms ControlStack.SC27Refinement.honest_concrete
