/-
SC-26 over a LOSSY network. This closes the gap that Gemini batch 3 flagged (reviews/lean-2026-10-09-batch3): before
this file, `SC26Refinement` and `SC26Liveness` assumed that the wire never loses a message.

The lossy machine (`LOp`, `stepL`) extends the concrete machine `SC26Refinement.stepC` (v3, recovery checks HALT)
with three adversary-controlled network operations. Everything else is unchanged (`base o` is `stepC o`). The wire
now holds the messages IN FLIGHT.
- `drop j`: the network loses the j-th in-flight message.
- `dup j`: the network duplicates the j-th in-flight message.
- `deliverAt j`: the bank processes the j-th in-flight message, in any order. With `bankProcess key` (first message
  with that key), this gives reordering.
  The bank's processing in `deliverAt` is idempotent by key when `dedup = true` (the deployed bank). With
  `dedup = false` it appends; this is used only for witness (4).

Results.
(1) Safety unchanged (`simulationL`, `lossy_safe`). The forward simulation maps:
  - `drop` and `dup` to [] (they only remove or copy messages that are already logged intents);
  - `deliverAt j` to [arrive key];
  - base operations as in `SC26Refinement.simulation`.
  So `SC26.Good` (every payment exactly approved, keys unique, total ≤ cap) holds for every reachable lossy state.
(2) Liveness under bounded-loss fairness.
  - `lossy_progress`: consider a trace pre ++ [recover] ++ nd ++ [bankProcess k] ++ post, where the gate is not
    halted at the recover and nd contains no drops (that retransmission is not lost before the bank processes it).
    Then k is paid, exactly once. Arbitrary drops, duplicates, reorders and crashes are allowed in pre and post.
  - `lossy_rounds`: the gate retransmits in rounds, each `pre_i ++ [recover] ++ mid_i`. The fairness premise is
    that among R consecutive retransmissions at least one is delivered (`Delivers`). If the gate is not halted at
    the end of the R-round window, then the payment has landed by the end of the window, at most R
    retransmissions, and is in the bank exactly once at the end of any continuation.
(3) `drop_all_no_progress`: an adversary that drops every retransmission prevents progress forever. For every n, n
  rounds of [recover, drop 0, bankProcess 0] return to the same state with an empty bank. Safety still holds there
  (`drop_all_safe`); one undropped round pays.
(4) `no_dedup_lossy_pays_twice`: with a non-idempotent bank, loss followed by retransmission and network duplication
  pays the same intent twice: 20 against a cap of 10. The deployed idempotent bank pays once on the same trace. This
  is the lossy-network instance of `SC26.no_dedup_retry_duplicates`.

Premise status: bounded-loss fairness is an ENVIRONMENT premise about the network, and it is necessary by (3). The
idempotent bank is a premise about the external system, and it is necessary by (4). No novelty is claimed: this is the
classical at-least-once retransmission plus idempotent receiver argument.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC26Liveness

namespace ControlStack.SC26LossyLiveness

open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness.Concrete

/-! ## The lossy machine -/

inductive LOp where
  | base (o : COp)
  | drop (j : ℕ)
  | dup (j : ℕ)
  | deliverAt (j : ℕ)
deriving DecidableEq, Repr

/-- the bank's processing: idempotent by key (deployed), or appending (witness (4) only) -/
def procWith (dedup : Bool) (bank : List (ℕ × Tx)) (key : ℕ) (tx : Tx) : List (ℕ × Tx) :=
  if dedup then bankApply bank key tx else bank ++ [(key, tx)]

def stepL (R : Roles) (cap : ℕ) (dedup : Bool) (s : CSt) : LOp → CSt
  | .base o => stepC R cap true s o
  | .drop j => { s with wire := s.wire.eraseIdx j }
  | .dup j =>
    match s.wire[j]? with
    | none => s
    | some m => { s with wire := s.wire ++ [m] }
  | .deliverAt j =>
    match s.wire[j]? with
    | none => s
    | some m => { s with bank := procWith dedup s.bank m.1 m.2 }

def runL (R : Roles) (cap : ℕ) (dedup : Bool) (s : CSt) (ops : List LOp) : CSt := ops.foldl (stepL R cap dedup) s

theorem runL_append (R : Roles) (cap : ℕ) (dd : Bool) (s : CSt) (a b : List LOp) :
    runL R cap dd s (a ++ b) = runL R cap dd (runL R cap dd s a) b := by
  simp [runL, List.foldl_append]

theorem runL_cons (R : Roles) (cap : ℕ) (dd : Bool) (s : CSt) (o : LOp) (ops : List LOp) :
    runL R cap dd s (o :: ops) = runL R cap dd (stepL R cap dd s o) ops := rfl

/-- untrusted operations never carry the gate credential; network operations are unrestricted -/
def legalL (R : Roles) : LOp → Prop
  | .base o => legalC R o
  | _ => True

/-! ## (1) Safety: the simulation maps drop and dup to [] -/

def opsOfL (s : CSt) : LOp → List Op
  | .base o => opsOf s o
  | .deliverAt j =>
    match s.wire[j]? with
    | none => []
    | some m => [.arrive m.1]
  | _ => []

/-- **Forward simulation for the lossy machine.** -/
theorem simulationL (R : Roles) (cap : ℕ) (s : CSt) (o : LOp) (ho : legalL R o) (h : CInv s) :
    α (stepL R cap true s o) = run R cap full (α s) (opsOfL s o) ∧ CInv (stepL R cap true s o) := by
  cases o with
  | base o => exact simulation R cap s o ho h
  | drop j =>
    exact ⟨rfl, fun m hm => h.wire_logged m ((List.eraseIdx_sublist _ _).subset hm), h.net_payload⟩
  | dup j =>
    cases hw : s.wire[j]? with
    | none => simp only [stepL, opsOfL, hw]; exact ⟨rfl, h⟩
    | some m =>
      simp only [stepL, opsOfL, hw]
      refine ⟨rfl, fun m' hm' => ?_, h.net_payload⟩
      rcases List.mem_append.1 hm' with hm' | hm'
      · exact h.wire_logged m' hm'
      · simp only [List.mem_singleton] at hm'; subst hm'; exact h.wire_logged _ (List.mem_of_getElem? hw)
  | deliverAt j =>
    cases hw : s.wire[j]? with
    | none => simp only [stepL, opsOfL, hw]; exact ⟨rfl, h⟩
    | some m =>
      simp only [stepL, opsOfL, hw]
      refine ⟨?_, ⟨h.wire_logged, h.net_payload⟩⟩
      simp only [run, List.foldl, step]
      have hmem := h.wire_logged m (List.mem_of_getElem? hw)
      have hf := find_net (α s).net (α s) m hmem h.net_payload
      rw [hf]
      simp only [bankAppend, procWith, bankApply, full, α, if_true]
      by_cases hb : m.1 ∈ List.map Prod.fst s.bank
      · rw [if_pos hb, if_pos ⟨trivial, hb⟩]
      · rw [if_neg hb, if_neg (fun h => hb h.2)]

def absTraceL (R : Roles) (cap : ℕ) : CSt → List LOp → List Op
  | _, [] => []
  | s, o :: ops => opsOfL s o ++ absTraceL R cap (stepL R cap true s o) ops

theorem simulation_runL (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o)
    (h : CInv s) :
    α (runL R cap true s ops) = run R cap full (α s) (absTraceL R cap s ops) ∧ CInv (runL R cap true s ops) := by
  induction ops generalizing s with
  | nil => exact ⟨rfl, h⟩
  | cons o ops ih =>
    obtain ⟨h1, h2⟩ := simulationL R cap s o (hops o List.mem_cons_self) h
    obtain ⟨ih1, ih2⟩ := ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')) h2
    refine ⟨?_, ih2⟩
    change α (runL R cap true (stepL R cap true s o) ops) =
      run R cap full (α s) (opsOfL s o ++ absTraceL R cap _ ops)
    rw [ih1, run_append, h1]

theorem opsOfL_legal (R : Roles) (s : CSt) (o : LOp) (ho : legalL R o) : ∀ a ∈ opsOfL s o, legal R a := by
  intro a ha
  cases o with
  | base o => exact opsOf_legal R s o ho a ha
  | deliverAt j =>
    simp only [opsOfL] at ha
    split at ha
    · simp at ha
    · simp only [List.mem_singleton] at ha; subst ha; trivial
  | drop j => simp [opsOfL] at ha
  | dup j => simp [opsOfL] at ha

theorem absTraceL_legal (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o) :
    ∀ a ∈ absTraceL R cap s ops, legal R a := by
  induction ops generalizing s with
  | nil => intro a ha; simp [absTraceL] at ha
  | cons o ops ih =>
    intro a ha
    simp only [absTraceL, List.mem_append] at ha
    rcases ha with ha | ha
    · exact opsOfL_legal R s o (hops o List.mem_cons_self) a ha
    · exact ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')) a ha

/-- **(1) SC-26 safety over a lossy, duplicating, reordering network.** -/
theorem lossy_safe (R : Roles) (cap : ℕ) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o) :
    Good R cap (α (runL R cap true cinit ops)) := by
  rw [(simulation_runL R cap cinit ops hops cinv_init).1, α_init]
  exact sc26_safe R cap _ (absTraceL_legal R cap cinit ops hops)

/-! ## Monotonicity and the ack invariant under loss -/

/-- what survives loss: delivery rows (by id and payload), bank keys, halting. The wire does NOT persist. -/
structure LMono (s t : CSt) : Prop where
  rows : ∀ d ∈ s.delivery, ∃ d' ∈ t.delivery, d'.id = d.id ∧ d'.tx = d.tx
  bank : ∀ x ∈ s.bank.map Prod.fst, x ∈ t.bank.map Prod.fst
  halt : s.halted = true → t.halted = true

theorem LMono.refl (s : CSt) : LMono s s := ⟨fun d hd => ⟨d, hd, rfl, rfl⟩, fun _ h => h, id⟩

theorem LMono.trans {s t u : CSt} (h1 : LMono s t) (h2 : LMono t u) : LMono s u := by
  refine ⟨fun d hd => ?_, fun x hx => h2.bank x (h1.bank x hx), fun h => h2.halt (h1.halt h)⟩
  obtain ⟨d', hd', e1, e2⟩ := h1.rows d hd
  obtain ⟨d'', hd'', e3, e4⟩ := h2.rows d' hd'
  exact ⟨d'', hd'', e3.trans e1, e4.trans e2⟩

theorem step_lmono (R : Roles) (cap : ℕ) (s : CSt) (o : LOp) (ho : legalL R o) : LMono s (stepL R cap true s o) := by
  cases o with
  | base o => have m := step_cmono R cap s o ho; exact ⟨m.rows, m.bank, m.halt⟩
  | drop j => exact ⟨fun d hd => ⟨d, hd, rfl, rfl⟩, fun _ h => h, id⟩
  | dup j =>
    simp only [stepL]; split
    · exact LMono.refl s
    · exact ⟨fun d hd => ⟨d, hd, rfl, rfl⟩, fun _ h => h, id⟩
  | deliverAt j =>
    simp only [stepL]; split
    · exact LMono.refl s
    · exact ⟨fun d hd => ⟨d, hd, rfl, rfl⟩, fun x hx => by
        simp only [procWith, if_true]; exact (bankApply_keys _ _ _).1 x hx, id⟩

theorem run_lmono (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o) :
    LMono s (runL R cap true s ops) := by
  induction ops generalizing s with
  | nil => exact LMono.refl s
  | cons o ops ih =>
    exact (step_lmono R cap s o (hops o List.mem_cons_self)).trans
      (ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')))

theorem step_ackinvL (R : Roles) (cap : ℕ) (s : CSt) (o : LOp) (ho : legalL R o) (h : AckInv s) :
    AckInv (stepL R cap true s o) := by
  cases o with
  | base o => exact step_ackinv R cap s o ho h
  | drop j => exact ackinv_same h rfl rfl
  | dup j =>
    simp only [stepL]; split
    · exact h
    · exact ackinv_same h rfl rfl
  | deliverAt j =>
    have m := step_lmono R cap s (.deliverAt j) trivial
    intro d hd hacked
    have hd' : d ∈ s.delivery := by simp only [stepL] at hd; split at hd <;> exact hd
    exact m.bank _ (h d hd' hacked)

theorem run_ackinvL (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o)
    (h : AckInv s) : AckInv (runL R cap true s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih =>
    exact ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho'))
      (step_ackinvL R cap s o (hops o List.mem_cons_self) h)

/-- a segment in which the network loses nothing -/
def DropFree (l : List LOp) : Prop := ∀ o ∈ l, ∀ j, o ≠ .drop j

/-- without drops, the in-flight messages persist -/
theorem step_wire (R : Roles) (cap : ℕ) (s : CSt) (o : LOp) (ho : legalL R o) (hd : ∀ j, o ≠ .drop j) :
    s.wire <+: (stepL R cap true s o).wire := by
  cases o with
  | base o => exact (step_cmono R cap s o ho).wire
  | drop j => exact absurd rfl (hd j)
  | dup j =>
    simp only [stepL]; split
    · exact List.prefix_refl _
    · exact List.prefix_append _ _
  | deliverAt j =>
    simp only [stepL]; split
    · exact List.prefix_refl _
    · exact List.prefix_refl _

theorem run_wire (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o)
    (hd : DropFree ops) : s.wire <+: (runL R cap true s ops).wire := by
  induction ops generalizing s with
  | nil => exact List.prefix_refl _
  | cons o ops ih =>
    exact (step_wire R cap s o (hops o List.mem_cons_self) (hd o List.mem_cons_self)).trans
      (ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')) (fun o' ho' => hd o' (List.mem_cons_of_mem o ho')))

/-! ## (2) Liveness under bounded-loss fairness -/

/-- **Lossy progress.** From a reachable lossy state with a logged intent for key `k`: if the gate (not halted)
retransmits (`recover`) and that retransmission is not lost before the bank processes `k` (`nd` drop-free), then `k`
is paid, exactly once. The surrounding segments may contain arbitrary drops, duplicates, reorders and crashes. -/
theorem lossy_progress (R : Roles) (cap : ℕ) (ops0 : List LOp) (hops0 : ∀ o ∈ ops0, legalL R o)
    (k : ℕ) (d : DRow) (hd : d ∈ (runL R cap true cinit ops0).delivery) (hk : d.id = k)
    (pre nd post : List LOp) (hleg : ∀ o ∈ pre ++ nd ++ post, legalL R o) (hnd : DropFree nd)
    (hh : (runL R cap true (runL R cap true cinit ops0) pre).halted = false) :
    let fin := runL R cap true (runL R cap true cinit ops0)
      (pre ++ .base .recover :: nd ++ .base (.bankProcess k) :: post)
    k ∈ fin.bank.map Prod.fst ∧ (fin.bank.map Prod.fst).count k = 1 := by
  intro fin
  set s := runL R cap true cinit ops0
  have hpre : ∀ o ∈ pre, legalL R o := fun o ho => hleg o (by simp [ho])
  have hndl : ∀ o ∈ nd, legalL R o := fun o ho => hleg o (by simp [ho])
  have hpost : ∀ o ∈ post, legalL R o := fun o ho => hleg o (by simp [ho])
  set s1 := runL R cap true s pre
  set s2 := stepL R cap true s1 (.base .recover)
  set s2' := runL R cap true s2 nd
  set s3 := stepL R cap true s2' (.base (.bankProcess k))
  have hrun : fin = runL R cap true s3 post := by
    simp only [fin, runL_append, runL_cons]; rfl
  have m1 := run_lmono R cap s pre hpre
  have m2' := run_lmono R cap s2 nd hndl
  have m3 := run_lmono R cap s3 post hpost
  have hack : AckInv s1 :=
    run_ackinvL R cap s pre hpre (run_ackinvL R cap cinit ops0 hops0 (by simp [AckInv, cinit]))
  obtain ⟨d1, hd1, hid1, _⟩ := m1.rows d hd
  have hpaid3 : k ∈ s3.bank.map Prod.fst := by
    cases hacked : d1.acked
    · have hw2 : (d1.id, d1.tx) ∈ s2.wire := by
        simp only [s2, stepL, stepC, hh, Bool.false_eq_true, and_false, ite_false, List.mem_append]
        right
        simp only [unacked, List.mem_map, List.mem_filter]
        exact ⟨d1, ⟨hd1, by simp [hacked]⟩, rfl⟩
      rw [hid1.trans hk] at hw2
      have hw2' : (k, d1.tx) ∈ s2'.wire := (run_wire R cap s2 nd hndl hnd).subset hw2
      obtain ⟨m, hm⟩ : ∃ m, s2'.wire.find? (fun m => m.1 = k) = some m := by
        cases hf : s2'.wire.find? (fun m => m.1 = k) with
        | some m => exact ⟨m, rfl⟩
        | none => rw [List.find?_eq_none] at hf; exact absurd (by simp) (hf _ hw2')
      have hmk : m.1 = k := by simpa using List.find?_some hm
      simp only [s3, stepL, stepC, hm]
      rw [← hmk]
      exact (bankApply_keys _ _ _).2
    · have hb1 := hack d1 hd1 hacked
      rw [hid1, hk] at hb1
      have m12 : LMono s1 s2 := step_lmono R cap s1 (.base .recover) trivial
      have m33 : LMono s2' s3 := step_lmono R cap s2' (.base (.bankProcess k)) trivial
      exact m33.bank _ (m2'.bank _ (m12.bank _ hb1))
  have hpaid : k ∈ fin.bank.map Prod.fst := by rw [hrun]; exact m3.bank _ hpaid3
  refine ⟨hpaid, List.count_eq_one_of_mem ?_ hpaid⟩
  have hall : ∀ o ∈ ops0 ++ (pre ++ .base .recover :: nd ++ .base (.bankProcess k) :: post), legalL R o := by
    intro o ho
    have key : o ∈ ops0 ∨ o ∈ pre ∨ o ∈ nd ∨ o ∈ post ∨ o = .base .recover ∨ o = .base (.bankProcess k) := by
      simp only [List.mem_append, List.mem_cons] at ho; tauto
    rcases key with h | h | h | h | h | h
    · exact hops0 o h
    · exact hpre o h
    · exact hndl o h
    · exact hpost o h
    · subst h; trivial
    · subst h; trivial
  have hg := lossy_safe R cap _ hall
  rw [runL_append] at hg
  exact hg.2.1

/-- a retransmission round: arbitrary operations, the gate's retransmission, then network/adversary operations -/
def roundOps (r : List LOp × List LOp) : List LOp := r.1 ++ .base .recover :: r.2

/-- the round's retransmission is DELIVERED: the bank processes `k` before the network loses anything -/
def Delivers (k : ℕ) (r : List LOp × List LOp) : Prop :=
  ∃ nd rest, r.2 = nd ++ .base (.bankProcess k) :: rest ∧ DropFree nd

/-- **(2) Bounded-loss liveness.** Take a window of rounds, each a retransmission by the gate, in which at least one
retransmission is delivered (bounded-loss fairness: at most R − 1 consecutive retransmissions are lost, and the window
has R rounds). If the gate is not halted at the end of the window, then the payment has landed by the end of the
window (at most R retransmissions) and is in the bank exactly once after any legal continuation. -/
theorem lossy_rounds (R : Roles) (cap : ℕ) (ops0 : List LOp) (hops0 : ∀ o ∈ ops0, legalL R o)
    (k : ℕ) (d : DRow) (hd : d ∈ (runL R cap true cinit ops0).delivery) (hk : d.id = k)
    (rounds : List (List LOp × List LOp)) (post : List LOp)
    (hleg : ∀ r ∈ rounds, ∀ o ∈ r.1 ++ r.2, legalL R o) (hpost : ∀ o ∈ post, legalL R o)
    (hfair : ∃ j, ∃ hj : j < rounds.length, Delivers k rounds[j])
    (hh : (runL R cap true (runL R cap true cinit ops0) (rounds.map roundOps).flatten).halted = false) :
    k ∈ (runL R cap true (runL R cap true cinit ops0) (rounds.map roundOps).flatten).bank.map Prod.fst ∧
      ((runL R cap true (runL R cap true cinit ops0) ((rounds.map roundOps).flatten ++ post)).bank.map
        Prod.fst).count k = 1 := by
  obtain ⟨j, hj, nd, rest, hr, hnd⟩ := hfair
  set s := runL R cap true cinit ops0
  have hlegr : ∀ o ∈ (rounds.map roundOps).flatten, legalL R o := by
    intro o ho
    simp only [List.mem_flatten, List.mem_map] at ho
    obtain ⟨l, ⟨r, hr, rfl⟩, ho⟩ := ho
    simp only [roundOps, List.mem_append, List.mem_cons] at ho
    rcases ho with ho | ho | ho
    · exact hleg r hr o (List.mem_append_left _ ho)
    · subst ho; trivial
    · exact hleg r hr o (List.mem_append_right _ ho)
  -- decompose the window at the delivering round j
  set A := ((rounds.take j).map roundOps).flatten ++ rounds[j].1
  set B := rest ++ ((rounds.drop (j + 1)).map roundOps).flatten
  have hsplit : (rounds.map roundOps).flatten = A ++ .base .recover :: nd ++ .base (.bankProcess k) :: B := by
    conv_lhs => rw [← List.take_append_drop j rounds, List.drop_eq_getElem_cons hj]
    simp only [A, B, List.map_append, List.map_cons, List.flatten_append, List.flatten_cons, roundOps, hr]
    simp
  have hA : ∀ o ∈ A ++ nd ++ B, legalL R o := by
    intro o ho
    apply hlegr
    rw [hsplit]
    simp only [List.mem_append, List.mem_cons] at ho ⊢
    tauto
  have hA' : ∀ o ∈ A ++ nd ++ (B ++ post), legalL R o := by
    intro o ho
    simp only [List.mem_append] at ho
    rcases ho with (ho | ho) | ho | ho
    · exact hA o (by simp [ho])
    · exact hA o (by simp [ho])
    · exact hA o (by simp [ho])
    · exact hpost o ho
  have hh1 : (runL R cap true s A).halted = false := by
    cases hc : (runL R cap true s A).halted
    · rfl
    · have m := run_lmono R cap (runL R cap true s A) (.base .recover :: nd ++ .base (.bankProcess k) :: B)
        (fun o ho => hlegr o (by rw [hsplit]; simp only [List.mem_append, List.mem_cons] at ho ⊢; tauto))
      have := m.halt hc
      rw [← runL_append, show A ++ (.base .recover :: nd ++ .base (.bankProcess k) :: B) =
        A ++ .base .recover :: nd ++ .base (.bankProcess k) :: B by simp, ← hsplit, hh] at this
      exact absurd this (by decide)
  have p1 := lossy_progress R cap ops0 hops0 k d hd hk A nd B hA hnd hh1
  have p2 := lossy_progress R cap ops0 hops0 k d hd hk A nd (B ++ post) hA' hnd hh1
  refine ⟨?_, ?_⟩
  · rw [hsplit]; exact p1.1
  · rw [hsplit, show A ++ .base .recover :: nd ++ .base (.bankProcess k) :: B ++ post =
      A ++ .base .recover :: nd ++ .base (.bankProcess k) :: (B ++ post) by simp]
    exact p2.2

/-! ## (3) Liveness needs the fairness premise -/

/-- the gate's setup for the witnesses: request, approval, reservation and logged intent for key 0 -/
def setupOps : List LOp := [.base (.request 1 wTx), .base (.approve 2 0 wTx), .base (.execute 1 0), .base (.deliver 0)]

theorem setup_reaches : runL R0 10 true cinit setupOps = loggedState := by decide

/-- the adversary loses every retransmission -/
def dropRound : List LOp := [.base .recover, .drop 0, .base (.bankProcess 0)]

theorem drop_round_fixed : runL R0 10 true loggedState dropRound = loggedState := by decide

/-- **(3) Dropping every retransmission prevents progress forever**: after any number n of retransmission rounds the
gate is back in the same state and the bank is empty. With one undropped retransmission the intent is paid. -/
theorem drop_all_no_progress (n : ℕ) :
    runL R0 10 true loggedState (List.replicate n dropRound).flatten = loggedState ∧
      (runL R0 10 true loggedState (List.replicate n dropRound).flatten).bank = [] ∧
      (runL R0 10 true loggedState [.base .recover, .base (.bankProcess 0)]).bank = [(0, wTx)] := by
  have h : runL R0 10 true loggedState (List.replicate n dropRound).flatten = loggedState := by
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.flatten_cons, runL_append, drop_round_fixed, ih]
  exact ⟨h, by rw [h]; decide, by decide⟩

/-- safety still holds in the all-drop run (it is a legal lossy trace from the initial state) -/
theorem drop_all_safe (n : ℕ) :
    Good R0 10 (α (runL R0 10 true cinit (setupOps ++ (List.replicate n dropRound).flatten))) := by
  apply lossy_safe
  intro o ho
  simp only [List.mem_append, List.mem_flatten, List.mem_replicate] at ho
  rcases ho with ho | ⟨l, ⟨-, rfl⟩, ho⟩
  · simp only [setupOps, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> trivial
  · simp only [dropRound, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> trivial

/-! ## (4) Retransmission under loss needs an idempotent bank -/

/-- the first transmission is lost; the gate crashes, recovers and retransmits; the network duplicates the
retransmission and delivers both copies -/
def lossDupTrace : List LOp :=
  [.base (.transmit 0), .drop 0, .base .crash, .base .recover, .dup 0, .deliverAt 0, .deliverAt 1]

/-- **(4) Without an idempotent bank, loss + retransmission + duplication pays twice** (20 against cap 10). The
deployed idempotent bank pays once on the same trace. This is the lossy-network instance of the abstract
`SC26.no_dedup_retry_duplicates` (restated as the last conjunct). -/
theorem no_dedup_lossy_pays_twice :
    (runL R0 10 false loggedState lossDupTrace).bank = [(0, wTx), (0, wTx)] ∧
    ((runL R0 10 false loggedState lossDupTrace).bank.map (fun e => e.2.amount)).sum = 20 ∧
    (runL R0 10 true loggedState lossDupTrace).bank = [(0, wTx)] ∧
    (run R0 20 { full with bankDedup := false } init
      [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .arrive 0, .arrive 0]).bank =
      [(0, tx1), (0, tx1)] :=
  ⟨by decide, by decide, by decide, no_dedup_retry_duplicates.1⟩

end ControlStack.SC26LossyLiveness

#print axioms ControlStack.SC26LossyLiveness.simulationL
#print axioms ControlStack.SC26LossyLiveness.lossy_safe
#print axioms ControlStack.SC26LossyLiveness.lossy_progress
#print axioms ControlStack.SC26LossyLiveness.lossy_rounds
#print axioms ControlStack.SC26LossyLiveness.drop_all_no_progress
#print axioms ControlStack.SC26LossyLiveness.drop_all_safe
#print axioms ControlStack.SC26LossyLiveness.no_dedup_lossy_pays_twice
