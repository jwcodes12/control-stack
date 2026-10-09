/-
SC-26 over a lossy network, two follow-ups to `SC26LossyLiveness`.

(1) HALT under loss (`lossy_halt`). After a concrete halt, under any legal lossy trace (drops, duplicates, reorders,
crashes, recover and transmit attempts, direct bank calls):
- every message in flight is one that was in flight at the halt (recover and transmit are refused once halted;
  `dup` and `deliverAt` act only on existing copies; `drop` only removes);
- every bank entry was in the bank or in flight at the halt.
So no new key ever lands (`lossy_halt_keys`). This is the weaker form of `SC26Refinement.concrete_halt`: under loss the
wire is no longer frozen, but it only shrinks or copies.
Witness `recover_ignores_halt_lossy`: in a design whose recover ignores HALT (v2), a stranded intent that was never in
flight at the halt is paid after the halt, even when the network drops the first re-transmission. The v3 design pays
nothing on the same trace.

(2) Per-copy fairness (`TSt`, `stepT`). The tagged machine runs the lossy machine and additionally tags every
physical transmission with a fresh transmission id. A duplicate keeps its copy's id; a drop removes one tagged copy.
- `runT_c`: the projection to the lossy machine is exact, so `lossy_safe` applies.
- `tag_persists`: an id always names the same message.
- `recover_batch_has_k`: the gate does retransmit. If it is not halted and k has an unacknowledged intent, the
  recover's batch contains a copy of k with a fresh id.
- `tagged_progress`: if the tagged copy of k from that retransmission is delivered (`deliverAt` at an index holding
  that id) before every copy of it is dropped, then k is paid, exactly once. Drops of OTHER messages, including other
  copies of k, are allowed anywhere. This is strictly weaker than `SC26LossyLiveness.Delivers`, which forbade all
  drops before delivery.
- `tagged_rounds`: in a window of retransmission rounds in which the tagged k-copy of some round is delivered, the
  payment lands by the end of the window and is in the bank exactly once after any continuation.
- `per_copy_weaker`: a trace whose delivery segment contains a drop of another copy. The old `Delivers` premise
  fails and the per-copy premise holds; k is paid.

No novelty is claimed: these are classical message-identity and fail-stop arguments.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC26LossyLiveness

namespace ControlStack.SC26LossyHalt

open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness.Concrete
open ControlStack.SC26LossyLiveness

/-! ## (1) HALT under loss -/

theorem bankApply_mem (b : List (ℕ × Tx)) (k : ℕ) (tx : Tx) (e : ℕ × Tx) (he : e ∈ bankApply b k tx) :
    e ∈ b ∨ e = (k, tx) := by
  unfold bankApply at he
  split_ifs at he
  · exact Or.inl he
  · rcases List.mem_append.1 he with h | h
    · exact Or.inl h
    · simp only [List.mem_singleton] at h; exact Or.inr h

/-- one lossy step from a halted state: still halted; in-flight messages and bank entries come from the old ones -/
theorem stepL_halted (R : Roles) (cap : ℕ) (s : CSt) (o : LOp) (ho : legalL R o) (hh : s.halted = true) :
    (stepL R cap true s o).halted = true ∧ (∀ m ∈ (stepL R cap true s o).wire, m ∈ s.wire) ∧
      ∀ e ∈ (stepL R cap true s o).bank, e ∈ s.bank ∨ e ∈ s.wire := by
  cases o with
  | base o =>
    obtain ⟨h1, h2, h3⟩ := stepC_halted R cap s o ho hh
    exact ⟨h1, fun m hm => by simp only [stepL] at hm; rwa [h2] at hm, h3⟩
  | drop j =>
    exact ⟨hh, fun m hm => (List.eraseIdx_sublist _ _).subset hm, fun e he => Or.inl he⟩
  | dup j =>
    simp only [stepL]
    split
    · exact ⟨hh, fun m hm => hm, fun e he => Or.inl he⟩
    · rename_i m0 hm0
      refine ⟨hh, fun m hm => ?_, fun e he => Or.inl he⟩
      rcases List.mem_append.1 hm with hm | hm
      · exact hm
      · simp only [List.mem_singleton] at hm; subst hm; exact List.mem_of_getElem? hm0
  | deliverAt j =>
    simp only [stepL]
    split
    · exact ⟨hh, fun m hm => hm, fun e he => Or.inl he⟩
    · rename_i m0 hm0
      refine ⟨hh, fun m hm => hm, fun e he => ?_⟩
      simp only [procWith, if_true] at he
      rcases bankApply_mem _ _ _ e he with h | h
      · exact Or.inl h
      · subst h; exact Or.inr (List.mem_of_getElem? hm0)

/-- **(1) Lossy HALT.** After a halt, for any legal lossy continuation: the gate stays halted, every in-flight
message was in flight at the halt, and every bank entry was in the bank or in flight at the halt. -/
theorem lossy_halt (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o)
    (hh : s.halted = true) :
    (runL R cap true s ops).halted = true ∧ (∀ m ∈ (runL R cap true s ops).wire, m ∈ s.wire) ∧
      ∀ e ∈ (runL R cap true s ops).bank, e ∈ s.bank ∨ e ∈ s.wire := by
  induction ops generalizing s with
  | nil => exact ⟨hh, fun m hm => hm, fun e he => Or.inl he⟩
  | cons o ops ih =>
    obtain ⟨h1, h2, h3⟩ := stepL_halted R cap s o (hops o List.mem_cons_self) hh
    obtain ⟨i1, i2, i3⟩ := ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')) h1
    rw [runL_cons]
    refine ⟨i1, fun m hm => h2 m (i2 m hm), fun e he => ?_⟩
    rcases i3 e he with h | h
    · exact h3 e h
    · exact Or.inr (h2 e h)

/-- **No new key lands after a halt** (under any loss, duplication, reordering, crashes and recovery attempts) -/
theorem lossy_halt_keys (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o)
    (hh : s.halted = true) (x : ℕ) (hx : x ∈ (runL R cap true s ops).bank.map Prod.fst) :
    x ∈ s.bank.map Prod.fst ∨ x ∈ s.wire.map Prod.fst := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  rcases (lossy_halt R cap s ops hops hh).2.2 e he with h | h
  · exact Or.inl (List.mem_map_of_mem h)
  · exact Or.inr (List.mem_map_of_mem h)

/-- the lossy machine with a configurable recovery (v2: `rch = false` ignores HALT) -/
def stepLH (R : Roles) (cap : ℕ) (rch : Bool) (s : CSt) : LOp → CSt
  | .base o => stepC R cap rch s o
  | o => stepL R cap true s o

def runLH (R : Roles) (cap : ℕ) (rch : Bool) (s : CSt) (ops : List LOp) : CSt := ops.foldl (stepLH R cap rch) s

/-- **Recovery that ignores HALT lands a stranded intent even under loss.** The halted gate has an intent that was
never in flight. The v2 recovery re-transmits; the network drops it; recovery re-transmits again; the bank pays.
The v3 recovery pays nothing. -/
theorem recover_ignores_halt_lossy :
    strandedState.halted = true ∧ strandedState.wire = [] ∧ strandedState.bank = [] ∧
    (runLH R0 10 false strandedState [.base .recover, .drop 0, .base .recover, .base (.bankProcess 0)]).bank =
      [(0, wTx)] ∧
    (runLH R0 10 true strandedState [.base .recover, .drop 0, .base .recover, .base (.bankProcess 0)]).bank = [] := by
  decide

/-! ## (2) Per-copy fairness: tagged transmissions -/

/-- the lossy machine plus a tagged copy of the wire: (transmission id, message) -/
structure TSt where
  c : CSt
  tw : List (ℕ × (ℕ × Tx))
  fresh : ℕ
deriving DecidableEq, Repr

/-- fresh ids for newly transmitted messages -/
def tagNew (fresh : ℕ) (l : List (ℕ × Tx)) : List (ℕ × (ℕ × Tx)) := l.mapIdx fun i m => (fresh + i, m)

def stepT (R : Roles) (cap : ℕ) (st : TSt) : LOp → TSt
  | .base o =>
    let c' := stepC R cap true st.c o
    let nw := c'.wire.drop st.c.wire.length
    ⟨c', st.tw ++ tagNew st.fresh nw, st.fresh + nw.length⟩
  | .drop j => ⟨stepL R cap true st.c (.drop j), st.tw.eraseIdx j, st.fresh⟩
  | .dup j =>
    ⟨stepL R cap true st.c (.dup j),
      match st.tw[j]? with
      | none => st.tw
      | some e => st.tw ++ [e], st.fresh⟩
  | .deliverAt j => ⟨stepL R cap true st.c (.deliverAt j), st.tw, st.fresh⟩

def runT (R : Roles) (cap : ℕ) (st : TSt) (ops : List LOp) : TSt := ops.foldl (stepT R cap) st

def tinit : TSt := ⟨cinit, [], 0⟩

theorem runT_append (R : Roles) (cap : ℕ) (st : TSt) (a b : List LOp) :
    runT R cap st (a ++ b) = runT R cap (runT R cap st a) b := by
  simp [runT, List.foldl_append]

theorem runT_cons (R : Roles) (cap : ℕ) (st : TSt) (o : LOp) (ops : List LOp) :
    runT R cap st (o :: ops) = runT R cap (stepT R cap st o) ops := rfl

theorem stepT_c (R : Roles) (cap : ℕ) (st : TSt) (o : LOp) : (stepT R cap st o).c = stepL R cap true st.c o := by
  cases o <;> rfl

/-- **The projection is exact**: the tagged machine's gate, bank and wire are the lossy machine's -/
theorem runT_c (R : Roles) (cap : ℕ) (st : TSt) (ops : List LOp) : (runT R cap st ops).c = runL R cap true st.c ops := by
  induction ops generalizing st with
  | nil => rfl
  | cons o ops ih => rw [runT_cons, ih, stepT_c]; rfl

theorem tagNew_snd (fresh : ℕ) (l : List (ℕ × Tx)) : (tagNew fresh l).map Prod.snd = l := by
  apply List.ext_getElem
  · simp [tagNew]
  · intro i h1 h2; simp [tagNew, List.getElem_mapIdx]

theorem mem_tagNew (fresh : ℕ) (l : List (ℕ × Tx)) (e : ℕ × (ℕ × Tx)) (he : e ∈ tagNew fresh l) :
    ∃ i, ∃ h : i < l.length, e = (fresh + i, l[i]) := by
  obtain ⟨i, h, rfl⟩ := List.mem_mapIdx.1 he
  exact ⟨i, h, rfl⟩

/-- the tagged invariant: the tags shadow the wire exactly, and all ids are below `fresh` -/
structure TInv (st : TSt) : Prop where
  shadow : st.c.wire = st.tw.map Prod.snd
  below : ∀ e ∈ st.tw, e.1 < st.fresh

theorem tinv_init : TInv tinit := ⟨rfl, by simp [tinit]⟩

theorem wire_deliverAt (R : Roles) (cap : ℕ) (s : CSt) (j : ℕ) : (stepL R cap true s (.deliverAt j)).wire = s.wire := by
  simp only [stepL]; split <;> rfl

theorem stepT_fresh (R : Roles) (cap : ℕ) (st : TSt) (o : LOp) : st.fresh ≤ (stepT R cap st o).fresh := by
  cases o <;> simp [stepT]

theorem step_tinv (R : Roles) (cap : ℕ) (st : TSt) (o : LOp) (ho : legalL R o) (h : TInv st) :
    TInv (stepT R cap st o) := by
  cases o with
  | base o =>
    obtain ⟨l, hl⟩ := (step_cmono R cap st.c o ho).wire
    have hnw : (stepC R cap true st.c o).wire.drop st.c.wire.length = l := by rw [← hl, List.drop_left]
    refine ⟨?_, fun e he => ?_⟩
    · simp only [stepT, hnw, List.map_append, tagNew_snd, ← h.shadow]; exact hl.symm
    · simp only [stepT, hnw, List.mem_append] at he ⊢
      rcases he with he | he
      · exact lt_of_lt_of_le (h.below e he) (Nat.le_add_right _ _)
      · obtain ⟨i, hi, rfl⟩ := mem_tagNew _ _ e he
        simp only; omega
  | drop j =>
    refine ⟨?_, fun e he => h.below e ((List.eraseIdx_sublist _ _).subset he)⟩
    simp only [stepT, stepL, h.shadow, List.eraseIdx_map]
  | dup j =>
    cases hj : st.tw[j]? with
    | none =>
      have hw : st.c.wire[j]? = none := by rw [h.shadow, List.getElem?_map, hj]; rfl
      refine ⟨?_, ?_⟩
      · simp only [stepT, stepL, hw, hj]; exact h.shadow
      · simp only [stepT, hj]; exact h.below
    | some e0 =>
      have hw : st.c.wire[j]? = some e0.2 := by rw [h.shadow, List.getElem?_map, hj]; rfl
      refine ⟨?_, fun e he => ?_⟩
      · simp only [stepT, stepL, hw, hj, List.map_append, List.map_cons, List.map_nil]; rw [h.shadow]
      · simp only [stepT, hj, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact h.below e he
        · exact h.below _ (List.mem_of_getElem? hj)
  | deliverAt j =>
    refine ⟨?_, h.below⟩
    simp only [stepT, wire_deliverAt]; exact h.shadow

theorem run_tinv (R : Roles) (cap : ℕ) (st : TSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o) (h : TInv st) :
    TInv (runT R cap st ops) := by
  induction ops generalizing st with
  | nil => exact h
  | cons o ops ih =>
    exact ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')) (step_tinv R cap st o (hops o List.mem_cons_self) h)

/-- id t names message m: every copy with id t carries m, and t is already allocated -/
def TagIs (st : TSt) (t : ℕ) (m : ℕ × Tx) : Prop := (∀ e ∈ st.tw, e.1 = t → e.2 = m) ∧ t < st.fresh

theorem step_tagIs (R : Roles) (cap : ℕ) (st : TSt) (o : LOp) (t : ℕ) (m : ℕ × Tx)
    (ht : TagIs st t m) : TagIs (stepT R cap st o) t m := by
  refine ⟨fun e he het => ?_, lt_of_lt_of_le ht.2 (stepT_fresh R cap st o)⟩
  cases o with
  | base o =>
    simp only [stepT, List.mem_append] at he
    rcases he with he | he
    · exact ht.1 e he het
    · obtain ⟨i, hi, rfl⟩ := mem_tagNew _ _ e he
      simp only at het; have := ht.2; omega
  | drop j => exact ht.1 e ((List.eraseIdx_sublist _ _).subset he) het
  | dup j =>
    simp only [stepT] at he
    split at he
    · exact ht.1 e he het
    · rename_i e0 hj
      rcases List.mem_append.1 he with he | he
      · exact ht.1 e he het
      · simp only [List.mem_singleton] at he; subst he; exact ht.1 _ (List.mem_of_getElem? hj) het
  | deliverAt j => exact ht.1 e he het

/-- **An id always names the same message** (duplicates keep it, new transmissions get fresh ids) -/
theorem tag_persists (R : Roles) (cap : ℕ) (st : TSt) (ops : List LOp)
    (t : ℕ) (m : ℕ × Tx) (ht : TagIs st t m) : TagIs (runT R cap st ops) t m := by
  induction ops generalizing st with
  | nil => exact ht
  | cons o ops ih =>
    exact ih _ (step_tagIs R cap st o t m ht)

/-- the copies (with their fresh ids) transmitted by one gate step -/
def batch (R : Roles) (cap : ℕ) (st : TSt) (o : LOp) : List (ℕ × (ℕ × Tx)) :=
  (stepT R cap st o).tw.drop st.tw.length

/-- a freshly transmitted copy's id names its message -/
theorem batch_tagIs (R : Roles) (cap : ℕ) (st : TSt) (o : COp) (h : TInv st) (e : ℕ × (ℕ × Tx))
    (he : e ∈ batch R cap st (.base o)) : TagIs (stepT R cap st (.base o)) e.1 e.2 := by
  simp only [batch, stepT, List.drop_left] at he
  obtain ⟨i, hi, rfl⟩ := mem_tagNew _ _ e he
  refine ⟨fun e' he' het => ?_, by simp only [stepT]; omega⟩
  simp only [stepT, List.mem_append] at he'
  rcases he' with he' | he'
  · have := h.below e' he'; simp only at het; omega
  · obtain ⟨i', hi', rfl⟩ := mem_tagNew _ _ e' he'
    simp only at het ⊢
    have : i' = i := by omega
    subst this; rfl

/-- **The gate does retransmit**: not halted, an unacknowledged intent for k ⇒ the recover's batch has a copy of k -/
theorem recover_batch_has_k (R : Roles) (cap : ℕ) (st : TSt) (hh : st.c.halted = false)
    (k : ℕ) (d : DRow) (hd : d ∈ st.c.delivery) (hk : d.id = k) (hack : d.acked = false) :
    ∃ e ∈ batch R cap st (.base .recover), e.2.1 = k := by
  have hw : (stepC R cap true st.c .recover).wire = st.c.wire ++ unacked st.c := by
    simp [stepC, hh]
  have hu : (d.id, d.tx) ∈ unacked st.c := by
    simp only [unacked, List.mem_map, List.mem_filter]
    exact ⟨d, ⟨hd, by simp [hack]⟩, rfl⟩
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hu
  refine ⟨(st.fresh + i, (d.id, d.tx)), ?_, hk⟩
  simp only [batch, stepT, List.drop_left, hw]
  apply List.mem_mapIdx.2
  refine ⟨i, by simpa using hi, ?_⟩
  simp [hie]

/-- the tagged copy with id t is DELIVERED within `mid`: the bank processes the in-flight copy at an index holding
id t (so not every copy of it has been dropped). Other messages may be dropped before. -/
def DeliveredIn (R : Roles) (cap : ℕ) (st : TSt) (t : ℕ) (mid : List LOp) : Prop :=
  ∃ nd j rest, mid = nd ++ .deliverAt j :: rest ∧ ((runT R cap st nd).tw[j]?).map Prod.fst = some t

/-- **Per-copy progress.** From a reachable tagged state, the gate retransmits (`recover`) and the tagged copy of k
from that retransmission is delivered before being dropped. Then k is paid, exactly once, after any continuation. -/
theorem tagged_progress (R : Roles) (cap : ℕ) (ops0 : List LOp) (hops0 : ∀ o ∈ ops0, legalL R o)
    (k : ℕ) (pre mid post : List LOp) (hleg : ∀ o ∈ pre ++ mid ++ post, legalL R o)
    (hdel : ∃ e ∈ batch R cap (runT R cap (runT R cap tinit ops0) pre) (.base .recover), e.2.1 = k ∧
      DeliveredIn R cap (stepT R cap (runT R cap (runT R cap tinit ops0) pre) (.base .recover)) e.1 mid) :
    let fin := (runT R cap (runT R cap tinit ops0) (pre ++ .base .recover :: mid ++ post)).c
    k ∈ fin.bank.map Prod.fst ∧ (fin.bank.map Prod.fst).count k = 1 := by
  intro fin
  obtain ⟨e, he, hek, nd, j, rest, hmid, htag⟩ := hdel
  set st := runT R cap tinit ops0
  have hpre : ∀ o ∈ pre, legalL R o := fun o ho => hleg o (by simp [ho])
  have hmidl : ∀ o ∈ mid, legalL R o := fun o ho => hleg o (by simp [ho])
  have hpost : ∀ o ∈ post, legalL R o := fun o ho => hleg o (by simp [ho])
  have hnd : ∀ o ∈ nd, legalL R o := fun o ho => hmidl o (by rw [hmid]; simp [ho])
  have hrest : ∀ o ∈ rest, legalL R o := fun o ho => hmidl o (by rw [hmid]; simp [ho])
  have i0 : TInv st := run_tinv R cap tinit ops0 hops0 tinv_init
  set st1 := runT R cap st pre
  have i1 : TInv st1 := run_tinv R cap st pre hpre i0
  set st2 := stepT R cap st1 (.base .recover)
  have i2 : TInv st2 := step_tinv R cap st1 _ trivial i1
  set st3 := runT R cap st2 nd
  have i3 : TInv st3 := run_tinv R cap st2 nd hnd i2
  have t3 : TagIs st3 e.1 e.2 := tag_persists R cap st2 nd _ _ (batch_tagIs R cap st1 _ i1 e he)
  -- the copy at index j is the tagged copy of k
  obtain ⟨x, hx, hxt⟩ : ∃ x, st3.tw[j]? = some x ∧ x.1 = e.1 := by
    cases hj : st3.tw[j]? with
    | none => rw [hj] at htag; simp at htag
    | some x => rw [hj] at htag; simp only [Option.map_some, Option.some.injEq] at htag; exact ⟨x, rfl, htag⟩
  have hx2 : x.2 = e.2 := t3.1 x (List.mem_of_getElem? hx) hxt
  have hw3 : st3.c.wire[j]? = some e.2 := by rw [i3.shadow, List.getElem?_map, hx]; simp [hx2]
  set st4 := stepT R cap st3 (.deliverAt j)
  have hpaid4 : k ∈ st4.c.bank.map Prod.fst := by
    simp only [st4, stepT_c, stepL, hw3, procWith, if_true]
    rw [← hek]; exact (bankApply_keys _ _ _).2
  have hrun : fin = runL R cap true st4.c (rest ++ post) := by
    have e1 : runT R cap st (pre ++ .base .recover :: mid ++ post) = runT R cap st4 (rest ++ post) := by
      rw [hmid]; simp only [List.append_assoc, List.cons_append, runT_append, runT_cons]; try rfl
    show (runT R cap st _).c = _
    rw [e1, runT_c]
  have hrp : ∀ o ∈ rest ++ post, legalL R o := by
    intro o ho; rcases List.mem_append.1 ho with ho | ho
    · exact hrest o ho
    · exact hpost o ho
  have hpaid : k ∈ fin.bank.map Prod.fst := by
    rw [hrun]; exact (run_lmono R cap st4.c (rest ++ post) hrp).bank _ hpaid4
  refine ⟨hpaid, List.count_eq_one_of_mem ?_ hpaid⟩
  have hall : ∀ o ∈ ops0 ++ (pre ++ .base .recover :: mid ++ post), legalL R o := by
    intro o ho
    have key : o ∈ ops0 ∨ o ∈ pre ∨ o ∈ mid ∨ o ∈ post ∨ o = .base .recover := by
      simp only [List.mem_append, List.mem_cons] at ho; tauto
    rcases key with h | h | h | h | h
    · exact hops0 o h
    · exact hpre o h
    · exact hmidl o h
    · exact hpost o h
    · subst h; trivial
  have hg := lossy_safe R cap _ hall
  have hfin : fin = runL R cap true cinit (ops0 ++ (pre ++ .base .recover :: mid ++ post)) := by
    simp only [fin, runT_c, runL_append]; rfl
  rw [← hfin] at hg
  exact hg.2.1

/-- round r's tagged k-copy is delivered (from the round's starting state st0) -/
def DeliversT (R : Roles) (cap : ℕ) (k : ℕ) (st0 : TSt) (r : List LOp × List LOp) : Prop :=
  ∃ e ∈ batch R cap (runT R cap st0 r.1) (.base .recover), e.2.1 = k ∧
    DeliveredIn R cap (stepT R cap (runT R cap st0 r.1) (.base .recover)) e.1 r.2

/-- **Per-copy bounded-loss liveness.** In a window of retransmission rounds, if the tagged k-copy of SOME round is
delivered before being dropped (drops of other copies are allowed anywhere), the payment has landed by the end of
the window and is in the bank exactly once after any legal continuation. -/
theorem tagged_rounds (R : Roles) (cap : ℕ) (ops0 : List LOp) (hops0 : ∀ o ∈ ops0, legalL R o) (k : ℕ)
    (rounds : List (List LOp × List LOp)) (post : List LOp)
    (hleg : ∀ r ∈ rounds, ∀ o ∈ r.1 ++ r.2, legalL R o) (hpost : ∀ o ∈ post, legalL R o)
    (hfair : ∃ j, ∃ hj : j < rounds.length,
      DeliversT R cap k (runT R cap (runT R cap tinit ops0) ((rounds.take j).map roundOps).flatten) rounds[j]) :
    k ∈ (runT R cap (runT R cap tinit ops0) (rounds.map roundOps).flatten).c.bank.map Prod.fst ∧
      ((runT R cap (runT R cap tinit ops0) ((rounds.map roundOps).flatten ++ post)).c.bank.map Prod.fst).count k
        = 1 := by
  obtain ⟨j, hj, hdel⟩ := hfair
  set A := ((rounds.take j).map roundOps).flatten ++ rounds[j].1
  set B := ((rounds.drop (j + 1)).map roundOps).flatten
  have hsplit : (rounds.map roundOps).flatten = A ++ .base .recover :: rounds[j].2 ++ B := by
    conv_lhs => rw [← List.take_append_drop j rounds, List.drop_eq_getElem_cons hj]
    simp only [A, B, List.map_append, List.map_cons, List.flatten_append, List.flatten_cons, roundOps]
    simp
  have hlegr : ∀ o ∈ (rounds.map roundOps).flatten, legalL R o := by
    intro o ho
    simp only [List.mem_flatten, List.mem_map] at ho
    obtain ⟨l, ⟨r, hr, rfl⟩, ho⟩ := ho
    simp only [roundOps, List.mem_append, List.mem_cons] at ho
    rcases ho with ho | ho | ho
    · exact hleg r hr o (List.mem_append_left _ ho)
    · subst ho; trivial
    · exact hleg r hr o (List.mem_append_right _ ho)
  have hin : ∀ o, o ∈ A ∨ o ∈ rounds[j].2 ∨ o ∈ B → legalL R o := by
    intro o ho; apply hlegr; rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto
  have hdel' : ∃ e ∈ batch R cap (runT R cap (runT R cap tinit ops0) A) (.base .recover), e.2.1 = k ∧
      DeliveredIn R cap (stepT R cap (runT R cap (runT R cap tinit ops0) A) (.base .recover)) e.1 rounds[j].2 := by
    simpa only [A, runT_append, DeliversT] using hdel
  have p1 := tagged_progress R cap ops0 hops0 k A rounds[j].2 B
    (fun o ho => hin o (by simp only [List.mem_append] at ho; tauto)) hdel'
  have p2 := tagged_progress R cap ops0 hops0 k A rounds[j].2 (B ++ post)
    (fun o ho => by
      simp only [List.mem_append] at ho
      rcases ho with (ho | ho) | ho | ho
      · exact hin o (Or.inl ho)
      · exact hin o (Or.inr (Or.inl ho))
      · exact hin o (Or.inr (Or.inr ho))
      · exact hpost o ho) hdel'
  refine ⟨?_, ?_⟩
  · rw [hsplit]; exact p1.1
  · rw [hsplit, show A ++ .base .recover :: rounds[j].2 ++ B ++ post =
      A ++ .base .recover :: rounds[j].2 ++ (B ++ post) by simp]
    exact p2.2

/-! ## Witness: the per-copy premise is strictly weaker -/

/-- the logged state, tagged (empty wire) -/
def tLogged : TSt := ⟨loggedState, [], 0⟩

/-- a round: the gate transmits (copy id 0), then retransmits (copy id 1); the network drops copy 0 and delivers
copy 1 -/
def pcRound : List LOp × List LOp := ([.base (.transmit 0)], [.drop 0, .deliverAt 0])

/-- **Per-copy fairness is strictly weaker.** In `pcRound` the network drops a copy before delivering, so the old
`Delivers` premise (drop-free before `bankProcess k`) fails. The per-copy premise holds (copy id 1 of key 0 is
delivered), and key 0 is paid. -/
theorem per_copy_weaker :
    ¬ Delivers 0 pcRound ∧ DeliversT R0 10 0 tLogged pcRound ∧
    (runT R0 10 tLogged (roundOps pcRound)).c.bank = [(0, wTx)] := by
  refine ⟨?_, ?_, by decide⟩
  · rintro ⟨nd, rest, h, -⟩
    -- pcRound.2 contains no bankProcess
    have : LOp.base (.bankProcess 0) ∈ pcRound.2 := by rw [h]; simp
    simp [pcRound] at this
  · refine ⟨(1, (0, wTx)), by decide, rfl, [.drop 0], 0, [], rfl, by decide⟩

end ControlStack.SC26LossyHalt

#print axioms ControlStack.SC26LossyHalt.lossy_halt
#print axioms ControlStack.SC26LossyHalt.lossy_halt_keys
#print axioms ControlStack.SC26LossyHalt.recover_ignores_halt_lossy
#print axioms ControlStack.SC26LossyHalt.runT_c
#print axioms ControlStack.SC26LossyHalt.tag_persists
#print axioms ControlStack.SC26LossyHalt.recover_batch_has_k
#print axioms ControlStack.SC26LossyHalt.tagged_progress
#print axioms ControlStack.SC26LossyHalt.tagged_rounds
#print axioms ControlStack.SC26LossyHalt.per_copy_weaker
