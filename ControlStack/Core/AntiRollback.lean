/-
Anti-rollback: a durable store that an untrusted operator (or a backup restore) can roll back, plus a trusted
MONOTONIC anchor. This discharges the `anti_rollback` premise (ASSURANCE-LEDGER.md: SC-14, SC-28; SC-26 nonce
history) for any gate with a `Spec`, under one premise: a trusted monotonic anchor, such as a TPM NV counter or a
transparency-log head.

Model (`RSt`, `ROp`, `stepR`) over any gate `G : System St Op Eff`:
- the store holds a record ⟨version, state, predecessor state, op⟩; every record ever written stays available in
  `hist` (the operator's backups);
- the anchor holds the last COMMITTED record (version + digest; here the record itself, so collision resistance
  of a real digest is a premise as in SC-27);
- `write o`: on a FRESH store (store = anchor), write ⟨v+1, step st o, st, o⟩. On a stale store, fail closed (halt);
- `bump`: commit point. If the store is exactly the next record (version + 1, predecessor = anchored state), the
  anchor advances and the op's effects are RELEASED (`released`). Otherwise nothing happens;
- `restart`: on a fresh store, resume. If the store is the next record (the crash window: written, not yet anchored),
  RECOVER by committing it. Otherwise, i.e. rolled back or forked, fail closed;
- `rollback k`: the adversary restores any record ever written.
`check = false` is the same machine without the anchor checks (the unsafe design).

Results:
- (1) `rollback_transfer` (adversary class TRACE_ARBITRARY: any interleaving of writes, commits, restarts and
  rollbacks to any backup):
  - the anchored state is exactly the PLAIN run of the committed ops (`anchor.st = G.run init committed`);
  - the released effects are exactly that run's effects;
  - so any `Spec` of `G` holds of everything ever released. `accepts_only_fresh`: the gate writes only from the
    anchored state.
  - `sc28_rollback_safe` instantiates this for SC-28: the budget theorem holds with storage rollback ALLOWED. The
    `legal` exclusion of rollback becomes the anchor premise.
- (2) `rollback_without_anchor_double_spends` (SC-28): without the anchor, restoring the pre-work snapshot re-spends
  the budget (released usage 20 > cap 10). With the anchor the replay is refused and the gate halts.
  `nonce_replay_without_anchor` shows the same for a one-use nonce.
- (3) `honest_liveness`: without rollbacks (commits, and crashes between write and commit followed by restart), the
  gate never halts and commits every op.
- (4) crash window: `restart` recovers a written-but-unanchored record only if it is exactly the next record
  (version + 1 and predecessor digest = anchored state). This is part of (1): recovery never admits a rollback.
  `crash_then_rollback_halts`: after a crash, restoring an older backup and restarting fails closed.

The anchor is a premise (trusted hardware or service): monotonic, not resettable by the operator, read and
incremented atomically, with the gate's write-then-increment protocol. Record integrity (the operator restores but
cannot forge records) is a premise, e.g. records MACed with a key the operator lacks. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate
import ControlStack.Scenarios.SC28Budget

namespace ControlStack.AntiRollback

open ControlStack.Gate

variable {St Op Eff : Type}

/-- a store record: version, state, predecessor state (the digest chain), and the op that produced it -/
structure Rec (St Op : Type) where
  ver : ℕ
  st : St
  prev : St
  op : Option Op
deriving DecidableEq, Repr

structure RSt (St Op Eff : Type) where
  /-- the durable store (may be rolled back) -/
  store : Rec St Op
  /-- every record ever written: the operator's backups -/
  hist : List (Rec St Op)
  /-- the trusted monotonic anchor: the last committed record -/
  anchor : Rec St Op
  /-- volatile fail-closed flag -/
  halted : Bool
  /-- ghost: the committed ops, in order -/
  committed : List Op
  /-- the effects released to the world (only at commit) -/
  released : List Eff
deriving DecidableEq, Repr

inductive ROp (Op : Type) where
  | write (o : Op)
  | bump
  | restart
  | rollback (k : ℕ)
deriving DecidableEq, Repr

def genesis (init : St) : Rec St Op := ⟨0, init, init, none⟩

def rinit (G : System St Op Eff) (init : St) : RSt St Op Eff :=
  ⟨genesis init, [genesis init], genesis init, false, [], G.effects init⟩

/-- the store is exactly the next record after the anchor -/
def IsNext (s : RSt St Op Eff) : Prop := s.store.ver = s.anchor.ver + 1 ∧ s.store.prev = s.anchor.st ∧ s.store.op ≠ none

instance [DecidableEq St] (s : RSt St Op Eff) : Decidable (IsNext s) := by unfold IsNext; infer_instance

/-- commit the store record: advance the anchor, release the effects its op produced (relative to its predecessor) -/
def commit (G : System St Op Eff) (s : RSt St Op Eff) : RSt St Op Eff :=
  { s with anchor := s.store, committed := s.committed ++ s.store.op.toList,
           released := s.released ++ (G.effects s.store.st).drop (G.effects s.store.prev).length, halted := false }

variable [DecidableEq St] [DecidableEq Op]

def stepR (G : System St Op Eff) (check : Bool) (s : RSt St Op Eff) : ROp Op → RSt St Op Eff
  | .write o =>
    if s.halted then s
    else if check = false ∨ s.store = s.anchor then
      let r : Rec St Op := ⟨s.anchor.ver + 1, G.step s.store.st o, s.store.st, some o⟩
      { s with store := r, hist := s.hist ++ [r] }
    else { s with halted := true }
  | .bump =>
    if s.halted then s
    else if check = false ∨ IsNext s then commit G s else s
  | .restart =>
    if check = false ∨ s.store = s.anchor then { s with halted := false }
    else if IsNext s then commit G s
    else { s with halted := true }
  | .rollback k =>
    match s.hist[k]? with
    | none => s
    | some r => { s with store := r }

def runR (G : System St Op Eff) (check : Bool) (s : RSt St Op Eff) (ops : List (ROp Op)) : RSt St Op Eff :=
  ops.foldl (stepR G check) s

/-! ## (1) Transfer: the anchored state is the plain run of the committed ops -/

/-- the invariant: backups are honest records (state = step of predecessor by its op); the store is a backup; the
anchor is the plain run of the committed ops and its effects are exactly the released ones -/
structure RInv (G : System St Op Eff) (S : Spec G) (init : St) (s : RSt St Op Eff) : Prop where
  hist_ok : ∀ r ∈ s.hist, r = genesis init ∨ ∃ o, r.op = some o ∧ r.st = G.step r.prev o
  store_mem : s.store ∈ s.hist
  anchor_run : s.anchor.st = G.run init s.committed
  released_eq : s.released = G.effects s.anchor.st
  anchor_ver : s.anchor.ver = s.committed.length
  inv : S.Inv s.anchor.st

omit [DecidableEq St] [DecidableEq Op] in
theorem rinv_init (G : System St Op Eff) (S : Spec G) (init : St) (h : S.Inv init) : RInv G S init (rinit G init) :=
  ⟨by simp [rinit], by simp [rinit], rfl, rfl, rfl, h⟩

omit [DecidableEq St] [DecidableEq Op] in
theorem run_append_one (G : System St Op Eff) (init : St) (l : List Op) (o : Op) :
    G.run init (l ++ [o]) = G.step (G.run init l) o := by
  simp [System.run, List.foldl_append]

omit [DecidableEq St] [DecidableEq Op] in
theorem commit_inv (G : System St Op Eff) (S : Spec G) (init : St) (s : RSt St Op Eff) (h : RInv G S init s)
    (hn : IsNext s) : RInv G S init (commit G s) := by
  obtain ⟨hv, hp, ho⟩ := hn
  obtain ⟨o, hop⟩ := Option.ne_none_iff_exists'.1 ho
  have hst : s.store.st = G.step s.anchor.st o := by
    rcases h.hist_ok _ h.store_mem with hg | ⟨o', ho', hs⟩
    · rw [hg] at hop; simp [genesis] at hop
    · rw [hop] at ho'; cases ho'; rw [hs, hp]
  refine ⟨h.hist_ok, h.store_mem, ?_, ?_, ?_, ?_⟩
  · simp only [commit, hop, Option.toList_some]
    rw [run_append_one, ← h.anchor_run, hst]
  · simp only [commit]
    rw [h.released_eq, hst, hp]
    exact List.prefix_iff_eq_append.1 (S.log_prefix _ o)
  · simp only [commit, hop, Option.toList_some, List.length_append, List.length_singleton]
    rw [hv, h.anchor_ver]
  · simp only [commit]; rw [hst]; exact S.step_inv _ o h.inv

theorem stepR_inv (G : System St Op Eff) (S : Spec G) (init : St) (s : RSt St Op Eff) (o : ROp Op)
    (h : RInv G S init s) : RInv G S init (stepR G true s o) := by
  cases o with
  | write o =>
    simp only [stepR]
    split_ifs with hh hf
    · exact h
    · refine ⟨fun r hr => ?_, by simp, h.anchor_run, h.released_eq, h.anchor_ver, h.inv⟩
      rcases List.mem_append.1 hr with hr | hr
      · exact h.hist_ok r hr
      · simp only [List.mem_singleton] at hr; subst hr; exact Or.inr ⟨o, rfl, rfl⟩
    · exact ⟨h.hist_ok, h.store_mem, h.anchor_run, h.released_eq, h.anchor_ver, h.inv⟩
  | bump =>
    simp only [stepR]
    split_ifs with hh hn
    · exact h
    · exact commit_inv G S init s h (by simpa using hn)
    · exact h
  | restart =>
    simp only [stepR]
    by_cases hf : s.store = s.anchor
    · rw [if_pos (Or.inr hf)]
      exact ⟨h.hist_ok, h.store_mem, h.anchor_run, h.released_eq, h.anchor_ver, h.inv⟩
    · rw [if_neg (fun hc => hc.elim (by simp) hf)]
      split_ifs with hn
      · exact commit_inv G S init s h hn
      · exact ⟨h.hist_ok, h.store_mem, h.anchor_run, h.released_eq, h.anchor_ver, h.inv⟩
  | rollback k =>
    simp only [stepR]
    split
    · exact h
    · rename_i r hr
      exact ⟨h.hist_ok, List.mem_of_getElem? hr, h.anchor_run, h.released_eq, h.anchor_ver, h.inv⟩

theorem runR_inv (G : System St Op Eff) (S : Spec G) (init : St) (s : RSt St Op Eff) (ops : List (ROp Op))
    (h : RInv G S init s) : RInv G S init (runR G true s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => exact ih _ (stepR_inv G S init s o h)

/-- **Transfer under rollback.** For any gate with a spec, after ANY interleaving of writes, commits, crashes and
restarts, and rollbacks of the store to any backup: the anchored state is the plain run of the committed ops, the
released effects are exactly that run's effects, and the spec holds of everything released. Rollback cannot replay
or re-spend anything, because what is released is a plain run. -/
theorem rollback_transfer (G : System St Op Eff) (S : Spec G) (init : St) (hinit : S.Inv init)
    (ops : List (ROp Op)) :
    let t := runR G true (rinit G init) ops
    t.anchor.st = G.run init t.committed ∧ t.released = G.effects (G.run init t.committed) ∧
      S.Inv (G.run init t.committed) ∧ (∀ e ∈ t.released, S.ok (G.run init t.committed) e) ∧
      t.anchor.ver = t.committed.length := by
  have h := runR_inv G S init _ ops (rinv_init G S init hinit)
  refine ⟨h.anchor_run, by rw [h.released_eq, h.anchor_run], by rw [← h.anchor_run]; exact h.inv, ?_, h.anchor_ver⟩
  intro e he
  rw [h.released_eq, h.anchor_run] at he
  rw [← h.anchor_run] at he ⊢
  exact S.inv_ok _ h.inv e he

/-- **The gate only writes from the anchored (latest committed) state.** -/
theorem accepts_only_fresh (G : System St Op Eff) (s : RSt St Op Eff) (o : Op)
    (hw : (stepR G true s (.write o)).store ≠ s.store) : s.store = s.anchor ∧ s.halted = false := by
  simp only [stepR] at hw
  split_ifs at hw with hh hf
  · exact absurd rfl hw
  · simp only [false_or] at hf
    exact ⟨hf, by simpa using hh⟩
  · exact absurd rfl hw

/-! ## (3) Honest liveness -/

omit [DecidableEq St] [DecidableEq Op] in
theorem next_ne (a : Rec St Op) (x y : St) (o : Option Op) : (⟨a.ver + 1, x, y, o⟩ : Rec St Op) ≠ a := by
  intro h
  have := congrArg Rec.ver h
  simp at this

/-- an honest schedule item: commit an op; or crash after the write and restart (recovery); or a bare restart -/
inductive HItem (Op : Type) where
  | exec (o : Op)
  | crash (o : Op)
  | restart

def expand : HItem Op → List (ROp Op)
  | .exec o => [.write o, .bump]
  | .crash o => [.write o, .restart]
  | .restart => [.restart]

def hops : HItem Op → List Op
  | .exec o => [o]
  | .crash o => [o]
  | .restart => []

/-- **Honest liveness.** Without rollbacks, from a fresh, running state, the gate never halts and commits every op
(crashes between write and commit are recovered at restart). -/
theorem honest_liveness (G : System St Op Eff) (s : RSt St Op Eff) (hf : s.store = s.anchor) (hh : s.halted = false)
    (items : List (HItem Op)) :
    let t := runR G true s (items.flatMap expand)
    t.halted = false ∧ t.store = t.anchor ∧ t.committed = s.committed ++ items.flatMap hops := by
  induction items generalizing s with
  | nil => exact ⟨hh, hf, by simp [runR]⟩
  | cons it items ih =>
    have key : ∃ s', runR G true s (expand it) = s' ∧ s'.store = s'.anchor ∧ s'.halted = false ∧
        s'.committed = s.committed ++ hops it := by
      cases it with
      | exec o =>
        refine ⟨_, rfl, ?_⟩
        simp [runR, stepR, hh, hf, IsNext, commit, expand, hops]
      | crash o =>
        refine ⟨_, rfl, ?_⟩
        simp [runR, stepR, hh, hf, IsNext, commit, expand, hops, next_ne]
      | restart =>
        refine ⟨_, rfl, ?_⟩
        simp [runR, stepR, hf, expand, hops]
    obtain ⟨s', hs', hf', hh', hc'⟩ := key
    have e : runR G true s ((it :: items).flatMap expand) = runR G true s' (items.flatMap expand) := by
      simp only [List.flatMap_cons, runR, List.foldl_append]
      rw [← hs']; rfl
    rw [e]
    obtain ⟨i1, i2, i3⟩ := ih s' hf' hh'
    refine ⟨i1, i2, ?_⟩
    rw [i3, hc']
    simp [List.flatMap_cons]

/-! ## (2) Witnesses: rollback without the anchor -/

/-- a one-use nonce gate: the state is the list of used nonces, its effects are those uses -/
def nonceGate : System (List ℕ) ℕ ℕ where
  step := fun s n => if n ∈ s then s else s ++ [n]
  effects := id

/-- use nonce 0, commit; restore the genesis backup; use nonce 0 again, commit -/
def replayTrace : List (ROp ℕ) := [.write 0, .bump, .rollback 0, .write 0, .bump]

/-- **Without the anchor, a restored backup replays a consumed nonce** (released [0, 0]). With the anchor the replay
is refused, the gate fails closed, and nonce 0 is released once. -/
theorem nonce_replay_without_anchor :
    (runR nonceGate false (rinit nonceGate []) replayTrace).released = [0, 0] ∧
    (runR nonceGate true (rinit nonceGate []) replayTrace).released = [0] ∧
    (runR nonceGate true (rinit nonceGate []) replayTrace).halted = true := by
  decide

/-- SC-28's work steps under the anchor (legal ops only; storage rollback is now the adversary's `rollback`) -/
abbrev G28 := SC28.sys [9] 10

def w28 (o : SC28.Op) (h : SC28.legal o) : ROp {o : SC28.Op // SC28.legal o} := .write ⟨o, h⟩

/-- issue a 10-unit lease, assign it, consume 10; restore the backup taken before the work; consume 10 again -/
def spendTrace : List (ROp {o : SC28.Op // SC28.legal o}) :=
  [w28 (.issue 9 0 10) trivial, .bump, w28 (.assignTo 9 1 0) trivial, .bump, w28 (.work 1 10 10) trivial, .bump,
   .rollback 2, w28 (.work 1 10 10) trivial, .bump]

/-- **Without the anchor, a restored backup re-spends the budget** (SC-28: released usage 20 against a cap of 10).
With the anchor the replay is refused (fail closed) and usage stays 10. -/
theorem rollback_without_anchor_double_spends :
    (runR G28 false (rinit G28 SC28.init) spendTrace).released = [(1, 0, 10), (1, 0, 10)] ∧
    (runR G28 true (rinit G28 SC28.init) spendTrace).released = [(1, 0, 10)] ∧
    (runR G28 true (rinit G28 SC28.init) spendTrace).halted = true := by
  decide

/-- **SC-28 with storage rollback allowed.** Under the anchor, after any trace of legal SC-28 ops interleaved with
crashes, restarts and rollbacks to any backup, the released usage is the usage of a plain legal run, so SC-28's
budget theorem holds of it. -/
theorem sc28_rollback_safe (admins : List ℕ) (G : ℕ) (ops : List (ROp {o : SC28.Op // SC28.legal o})) :
    let t := runR (SC28.sys admins G) true (rinit (SC28.sys admins G) SC28.init) ops
    t.released = (SC28.run admins G SC28.full SC28.init (t.committed.map Subtype.val)).usage ∧
      SC28.Good G (SC28.run admins G SC28.full SC28.init (t.committed.map Subtype.val)) := by
  have h := rollback_transfer (SC28.sys admins G) (SC28.spec admins G) SC28.init (SC28.inv_init G) ops
  have erun : ∀ (l : List {o : SC28.Op // SC28.legal o}) (s : SC28.St),
      (SC28.sys admins G).run s l = SC28.run admins G SC28.full s (l.map Subtype.val) := by
    intro l; induction l with
    | nil => intro s; rfl
    | cons o l ih => intro s; exact ih _
  refine ⟨?_, ?_⟩
  · rw [h.2.1, erun]; rfl
  · have hinv := h.2.2.1
    rw [erun] at hinv
    exact hinv.good

/-! ## (4) The crash window cannot be used to roll back -/

/-- **Crash, then rollback, then restart: fail closed.** Commit op 1; write op 2 and crash before the anchor
increment; restore the genesis backup; restart. The gate halts and nothing beyond op 1 is released. -/
theorem crash_then_rollback_halts :
    let t := runR nonceGate true (rinit nonceGate []) [.write 1, .bump, .write 2, .rollback 0, .restart]
    t.halted = true ∧ t.released = [1] ∧ t.committed = [1] := by
  decide

/-- **Crash recovery.** Commit op 1; write op 2 and crash; restart. The written record is exactly the next record,
so it is committed: both ops are released, no halt. -/
theorem crash_recovery_commits :
    let t := runR nonceGate true (rinit nonceGate []) [.write 1, .bump, .write 2, .restart]
    t.halted = false ∧ t.released = [1, 2] ∧ t.committed = [1, 2] := by
  decide

end ControlStack.AntiRollback

#print axioms ControlStack.AntiRollback.rollback_transfer
#print axioms ControlStack.AntiRollback.accepts_only_fresh
#print axioms ControlStack.AntiRollback.honest_liveness
#print axioms ControlStack.AntiRollback.nonce_replay_without_anchor
#print axioms ControlStack.AntiRollback.rollback_without_anchor_double_spends
#print axioms ControlStack.AntiRollback.sc28_rollback_safe
#print axioms ControlStack.AntiRollback.crash_then_rollback_halts
#print axioms ControlStack.AntiRollback.crash_recovery_commits
