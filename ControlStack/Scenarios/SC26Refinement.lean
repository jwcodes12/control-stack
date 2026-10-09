/-
SC-26 refinement: the runtime's event structure (scenarios/SC-26/harness/txgate.py, bank.py, v3) as a concrete
machine, with a forward simulation into the Lean model `ControlStack.SC26` (done-criterion 3, "justified
refinement").

Concrete machine (`CSt`, `COp`, `stepC`), mirroring the runtime:
- Durable gate tables, as in txgate's SQLite schema: next, requests, approvals, reserved, spent, halted, and
  `delivery` rows {id, tx, acked}. The runtime row's seq is the list position; its outcome is not modelled beyond
  `acked`.
- Volatile gate state: `inflight` (the send in progress), lost on `crash`.
- Network: `wire`, every message physically transmitted. A message may be processed by the bank any number of times
  (duplication, delay).
- The bank's durable ledger, deduplicated by key. A repeat with the same payload answers `duplicate`, with a
  different payload `conflict`; neither appends.
- Operations:
  - `request` / `approve` / `execute`: one SQLite transaction each;
  - `deliver`: halt check and intent row, under the halt lock;
  - `transmit i`: physical send of a logged, unacknowledged intent; refused once halted;
  - `bankProcess key`: the bank applies a transmitted message with that key. By the invariant, all messages with
    one key carry the same payload, so which copy is processed does not matter;
  - `ack i`: mark row i acknowledged after the bank holds its key;
  - `crash`: volatile state lost;
  - `recover`: re-transmit every unacknowledged intent, unless halted;
  - `halt`;
  - `bankCall`: direct calls to the bank by other principals.
  `stepC` takes a flag `recoverChecksHalt` (true in v3; `recover_halt_witness` shows false breaks the halt
  corollary).

Results (adversary class TRACE_ARBITRARY: any interleaving of legal concrete operations, any crash points, any
network duplication or delay):
- `simulation`: with abstraction α (durable tables ↦ model state; logged intents ↦ the model's `net`; bank ↦ bank)
  and the concrete invariant `CInv`, every concrete step is matched by 0 or 1 model steps:
  α (stepC s o) = SC26.run (α s) (opsOf s o). The invariant is: every transmitted message is a logged intent, and
  every logged intent carries its request's payload. Mapping:
  - deliver ↦ [deliver id];
  - bankProcess ↦ [arrive key] when the wire holds the key, else [];
  - transmit / ack / crash / recover ↦ [];
  - the gate transactions and halt ↦ themselves;
  - a direct bank call ↦ [bankCall].
- `concrete_safe`: `SC26.Good` holds for α of every reachable concrete state, so `sc26_safe` transfers to the
  concrete machine.
- `concrete_halt`: after a concrete halt, the wire is frozen (no transmit or re-transmit is accepted), and the bank
  only gains messages that were transmitted BEFORE the halt. This is stronger than the model's `halt_freezes`, whose
  `net` also contains logged but untransmitted intents.
- `recover_halt_witness`: a recovery that re-transmits while halted (the v2 → v3 checker blind spot) pays an intent
  that was never transmitted before the halt.

What the refinement covers: the event structure as implemented, with each SQLite transaction an atomic step and
arbitrary interleaving, crashes and network behaviour.
What it does NOT cover:
- that the Python code implements this concrete machine (that link stays TESTED, via check_trace's trace replay and
  the bank access-log reconciliation);
- SQLite atomicity and durability;
- the OS (UID separation, SO_PEERCRED, file permissions);
- liveness (that intents are eventually paid).
These are classical forward-simulation arguments; no novelty is claimed.
-/
import ControlStack.Scenarios.SC26Transaction

namespace ControlStack.SC26Refinement

open ControlStack.SC26

/-! ## The concrete machine -/

/-- a delivery intent row (txgate's `delivery` table) -/
structure DRow where
  id : ℕ
  tx : Tx
  acked : Bool
deriving DecidableEq, Repr

structure CSt where
  next : ℕ
  reqs : List Req
  approvals : List (ℕ × ℕ × Tx)
  reserved : List ℕ
  spent : ℕ
  halted : Bool
  delivery : List DRow
  /-- volatile: the send in progress (delivery row index) -/
  inflight : Option ℕ
  /-- the network: every message physically transmitted -/
  wire : List (ℕ × Tx)
  /-- the bank's durable ledger -/
  bank : List (ℕ × Tx)
deriving DecidableEq, Repr

inductive COp where
  | request (caller : ℕ) (tx : Tx)
  | approve (caller : ℕ) (id : ℕ) (tx : Tx)
  | execute (caller : ℕ) (id : ℕ)
  | deliver (id : ℕ)
  | transmit (i : ℕ)
  | bankProcess (key : ℕ)
  | ack (i : ℕ)
  | crash
  | recover
  | halt (caller : ℕ)
  | bankCall (caller : ℕ) (key : ℕ) (tx : Tx)
deriving DecidableEq, Repr

def cinit : CSt := ⟨0, [], [], [], 0, false, [], none, [], []⟩

def creqOf (s : CSt) (id : ℕ) : Option Req := s.reqs.find? (fun r => r.id = id)

/-- the bank's processing of a transfer: idempotent by key (duplicate and conflict both leave the ledger unchanged) -/
def bankApply (bank : List (ℕ × Tx)) (key : ℕ) (tx : Tx) : List (ℕ × Tx) :=
  if key ∈ bank.map Prod.fst then bank else bank ++ [(key, tx)]

/-- acknowledge row i (txgate's `UPDATE delivery SET acked=1`), clearing the in-progress send -/
def ackSet (s : CSt) (i : ℕ) (d : DRow) : CSt :=
  { s with delivery := s.delivery.set i { d with acked := true }, inflight := none }

/-- the unacknowledged intents as messages -/
def unacked (s : CSt) : List (ℕ × Tx) := (s.delivery.filter (fun d => !d.acked)).map (fun d => (d.id, d.tx))

def stepC (R : Roles) (cap : ℕ) (recoverChecksHalt : Bool) (s : CSt) : COp → CSt
  | .request c tx =>
    if s.halted then s
    else if c ∈ R.agents then { s with reqs := s.reqs ++ [⟨s.next, c, tx⟩], next := s.next + 1 } else s
  | .approve c id tx =>
    if s.halted then s
    else match creqOf s id with
      | none => s
      | some r =>
        if c ∈ R.approvers ∧ c ≠ r.requester ∧ tx = r.tx then { s with approvals := s.approvals ++ [(id, c, tx)] }
        else s
  | .execute _ id =>
    if s.halted then s
    else match creqOf s id with
      | none => s
      | some r =>
        if (∃ ap ∈ s.approvals, ap.1 = id) ∧ id ∉ s.reserved ∧ s.spent + r.tx.amount ≤ cap then
          { s with reserved := s.reserved ++ [id], spent := s.spent + r.tx.amount }
        else s
  | .deliver id =>
    if s.halted then s
    else if id ∈ s.reserved then
      match creqOf s id with
      | none => s
      | some r => { s with delivery := s.delivery ++ [⟨id, r.tx, false⟩] }
    else s
  | .transmit i =>
    if s.halted then s
    else match s.delivery[i]? with
      | none => s
      | some d => if d.acked then s else { s with wire := s.wire ++ [(d.id, d.tx)], inflight := some i }
  | .bankProcess key =>
    match s.wire.find? (fun m => m.1 = key) with
    | none => s
    | some m => { s with bank := bankApply s.bank m.1 m.2 }
  | .ack i =>
    match s.delivery[i]? with
    | none => s
    | some d =>
      if d.id ∈ s.bank.map Prod.fst then ackSet s i d else s
  | .crash => { s with inflight := none }
  | .recover =>
    if recoverChecksHalt ∧ s.halted then s else { s with wire := s.wire ++ unacked s }
  | .halt c => if c ∈ R.admins then { s with halted := true } else s
  | .bankCall c key tx => if c ≠ R.gate then s else { s with bank := bankApply s.bank key tx }

def runC (R : Roles) (cap : ℕ) (rch : Bool) (s : CSt) (ops : List COp) : CSt := ops.foldl (stepC R cap rch) s

/-- untrusted concrete operations never carry the gate credential -/
def legalC (R : Roles) : COp → Prop
  | .bankCall c _ _ => c ≠ R.gate
  | _ => True

/-! ## Abstraction and invariant -/

/-- durable tables ↦ model state; logged intents ↦ the model's `net` -/
def α (s : CSt) : St := ⟨s.next, s.reqs, s.approvals, s.reserved, s.spent, s.halted, s.bank,
  s.delivery.map (fun d => (d.id, d.tx))⟩

/-- the model operations matching one concrete step -/
def opsOf (s : CSt) : COp → List Op
  | .request c tx => [.request c tx]
  | .approve c id tx => [.approve c id tx]
  | .execute c id => [.execute c id]
  | .deliver id => [.deliver id]
  | .bankProcess key => if (s.wire.find? (fun m => m.1 = key)).isSome then [.arrive key] else []
  | .halt c => [.halt c]
  | .bankCall c key tx => [.bankCall c key tx]
  | _ => []

/-- the concrete invariant: transmitted messages are logged intents; logged intents carry their request's payload -/
structure CInv (s : CSt) : Prop where
  wire_logged : ∀ m ∈ s.wire, m ∈ (α s).net
  net_payload : ∀ m ∈ (α s).net, ∃ r, reqOf (α s) m.1 = some r ∧ r.tx = m.2

theorem cinv_init : CInv cinit := ⟨by simp [cinit], by simp [cinit, α]⟩

theorem creqOf_eq (s : CSt) (id : ℕ) : creqOf s id = reqOf (α s) id := rfl

/-- if m is in the net and the net's payloads are determined by their keys, the first entry with m's key is m -/
theorem find_net (net : List (ℕ × Tx)) (s : St) (m : ℕ × Tx) (hm : m ∈ net)
    (hp : ∀ e ∈ net, ∃ r, reqOf s e.1 = some r ∧ r.tx = e.2) :
    net.find? (fun e => e.1 = m.1) = some m := by
  obtain ⟨e, he⟩ : ∃ e, net.find? (fun e => e.1 = m.1) = some e := by
    cases h : net.find? (fun e => e.1 = m.1) with
    | some e => exact ⟨e, rfl⟩
    | none =>
      rw [List.find?_eq_none] at h
      exact absurd (by simp) (h m hm)
  rw [he]
  have hk : e.1 = m.1 := by simpa using List.find?_some he
  obtain ⟨r1, h1, t1⟩ := hp e (List.mem_of_find?_eq_some he)
  obtain ⟨r2, h2, t2⟩ := hp m hm
  rw [hk, h2] at h1
  cases h1
  exact congrArg some (Prod.ext hk (t1.symm.trans t2))

/-! ## Forward simulation -/

theorem α_reqOf_append (s : CSt) (l : List Req) (k : ℕ) (r : Req) (h : reqOf (α s) k = some r) :
    reqOf (α { s with reqs := s.reqs ++ l }) k = some r :=
  reqOf_append (α s) l k r h

/-- **Forward simulation.** Every legal concrete step from an invariant state is matched by its model operations,
and preserves the invariant. -/
theorem simulation (R : Roles) (cap : ℕ) (s : CSt) (o : COp) (ho : legalC R o) (h : CInv s) :
    α (stepC R cap true s o) = run R cap full (α s) (opsOf s o) ∧ CInv (stepC R cap true s o) := by
  cases o with
  | request c tx =>
    refine ⟨?_, ?_⟩
    · show α (stepC R cap true s (.request c tx)) = step R cap full (α s) (.request c tx)
      simp only [stepC, step]
      by_cases hh : s.halted = true
      · rw [if_pos hh, if_pos (show (α s).halted = true ∧ full.haltCheck = true from ⟨hh, rfl⟩)]
      · rw [if_neg hh, if_neg (show ¬((α s).halted = true ∧ full.haltCheck = true) from fun h => hh h.1)]
        by_cases hc : c ∈ R.agents
        · rw [if_pos hc, if_pos hc]; rfl
        · rw [if_neg hc, if_neg hc]
    · simp only [stepC]
      split_ifs
      · exact h
      · refine ⟨fun m hm => h.wire_logged m hm, fun m hm => ?_⟩
        obtain ⟨r, hr, ht⟩ := h.net_payload m hm
        exact ⟨r, α_reqOf_append s _ _ r hr, ht⟩
      · exact h
  | approve c id tx =>
    refine ⟨?_, ?_⟩
    · show α (stepC R cap true s (.approve c id tx)) = step R cap full (α s) (.approve c id tx)
      simp only [stepC, step]
      by_cases hh : s.halted = true
      · rw [if_pos hh, if_pos (show (α s).halted = true ∧ full.haltCheck = true from ⟨hh, rfl⟩)]
      · rw [if_neg hh, if_neg (show ¬((α s).halted = true ∧ full.haltCheck = true) from fun h => hh h.1),
          creqOf_eq]
        cases hr : reqOf (α s) id with
        | none => rfl
        | some r =>
          dsimp only
          by_cases hcond : c ∈ R.approvers ∧ c ≠ r.requester ∧ tx = r.tx
          · rw [if_pos hcond, if_pos ⟨hcond.1, fun _ => hcond.2.1, fun _ => hcond.2.2⟩]; rfl
          · rw [if_neg hcond, if_neg (fun h => hcond ⟨h.1, h.2.1 rfl, h.2.2 rfl⟩)]
    · simp only [stepC]
      split_ifs
      · exact h
      · split
        · exact h
        · split_ifs
          · exact ⟨h.wire_logged, h.net_payload⟩
          · exact h
  | execute c id =>
    refine ⟨?_, ?_⟩
    · show α (stepC R cap true s (.execute c id)) = step R cap full (α s) (.execute c id)
      simp only [stepC, step]
      by_cases hh : s.halted = true
      · rw [if_pos hh, if_pos (show (α s).halted = true ∧ full.haltCheck = true from ⟨hh, rfl⟩)]
      · rw [if_neg hh, if_neg (show ¬((α s).halted = true ∧ full.haltCheck = true) from fun h => hh h.1),
          creqOf_eq]
        cases hr : reqOf (α s) id with
        | none => rfl
        | some r =>
          dsimp only
          by_cases hcond : (∃ ap ∈ s.approvals, ap.1 = id) ∧ id ∉ s.reserved ∧ s.spent + r.tx.amount ≤ cap
          · rw [if_pos hcond, if_pos ⟨hcond.1, fun _ => hcond.2.1, fun _ => hcond.2.2⟩]; rfl
          · rw [if_neg hcond, if_neg (fun h => hcond ⟨h.1, h.2.1 rfl, h.2.2 rfl⟩)]
    · simp only [stepC]
      split_ifs
      · exact h
      · split
        · exact h
        · split_ifs
          · exact ⟨h.wire_logged, h.net_payload⟩
          · exact h
  | deliver id =>
    refine ⟨?_, ?_⟩
    · show α (stepC R cap true s (.deliver id)) = step R cap full (α s) (.deliver id)
      simp only [stepC, step]
      by_cases hh : s.halted = true
      · rw [if_pos hh, if_pos (show (α s).halted = true ∧ full.haltCheck = true from ⟨hh, rfl⟩)]
      · rw [if_neg hh, if_neg (show ¬((α s).halted = true ∧ full.haltCheck = true) from fun h => hh h.1)]
        by_cases hres : id ∈ s.reserved
        · rw [if_pos hres, if_pos (show id ∈ (α s).reserved from hres), creqOf_eq]
          cases hr : reqOf (α s) id with
          | none => rfl
          | some r => simp only [α, List.map_append, List.map_cons, List.map_nil]
        · rw [if_neg hres, if_neg (show id ∉ (α s).reserved from hres)]
    · simp only [stepC, creqOf_eq]
      split_ifs
      · exact h
      · split
        · exact h
        · rename_i r hr
          refine ⟨fun m hm => ?_, fun m hm => ?_⟩
          · have := h.wire_logged m hm
            simp only [α, List.map_append, List.mem_append] at this ⊢
            exact Or.inl this
          · simp only [α, List.map_append, List.mem_append, List.map_cons, List.map_nil,
              List.mem_singleton] at hm
            rcases hm with hm | rfl
            · exact h.net_payload m (by simpa [α] using hm)
            · exact ⟨r, hr, rfl⟩
      · exact h
  | transmit i =>
    refine ⟨?_, ?_⟩
    · simp only [stepC, opsOf, run, List.foldl]
      split_ifs
      · rfl
      · split
        · rfl
        · split_ifs <;> rfl
    · simp only [stepC]
      split_ifs
      · exact h
      · split
        · exact h
        · rename_i d hd
          split_ifs
          · exact h
          · refine ⟨fun m hm => ?_, h.net_payload⟩
            simp only [List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | rfl
            · exact h.wire_logged m hm
            · show (d.id, d.tx) ∈ s.delivery.map (fun d => (d.id, d.tx))
              exact List.mem_map.2 ⟨d, List.mem_of_getElem? hd, rfl⟩
  | bankProcess key =>
    refine ⟨?_, ?_⟩
    · simp only [stepC, opsOf]
      cases hw : s.wire.find? (fun m => m.1 = key) with
      | none => rfl
      | some m =>
        simp only [Option.isSome_some, if_true, run, List.foldl, step]
        have hk : m.1 = key := by simpa using List.find?_some hw
        have hmem := h.wire_logged m (List.mem_of_find?_eq_some hw)
        have hf := find_net (α s).net (α s) m hmem h.net_payload
        rw [hk] at hf
        rw [hf]
        simp only [bankAppend, bankApply, full, α]
        by_cases hb : m.1 ∈ List.map Prod.fst s.bank
        · rw [if_pos hb, if_pos ⟨trivial, hb⟩]
        · rw [if_neg hb, if_neg (fun h => hb h.2)]
    · simp only [stepC]
      split
      · exact h
      · exact ⟨h.wire_logged, h.net_payload⟩
  | ack i =>
    refine ⟨?_, ?_⟩
    · simp only [stepC, opsOf, run, List.foldl]
      split
      · rfl
      · rename_i d hd
        split_ifs
        · have hi : i < s.delivery.length := (List.getElem?_eq_some_iff.1 hd).1
          have hdi : s.delivery[i] = d := (List.getElem?_eq_some_iff.1 hd).2
          simp only [α, ackSet, List.map_set]
          congr 1
          rw [← hdi]
          have hi' : i < (s.delivery.map (fun d => (d.id, d.tx))).length := by simpa using hi
          simpa using List.set_getElem_self hi'
        · rfl
    · simp only [stepC]
      split
      · exact h
      · rename_i d hd
        split_ifs
        · have hi : i < s.delivery.length := (List.getElem?_eq_some_iff.1 hd).1
          have hdi : s.delivery[i] = d := (List.getElem?_eq_some_iff.1 hd).2
          have hnet : (α (ackSet s i d)).net = (α s).net := by
            simp only [α, ackSet, List.map_set]
            rw [← hdi]
            have hi' : i < (s.delivery.map (fun d => (d.id, d.tx))).length := by simpa using hi
            simpa using List.set_getElem_self hi'
          have hreq : ∀ k, reqOf (α (ackSet s i d)) k = reqOf (α s) k := fun k => rfl
          refine ⟨fun m hm => ?_, fun m hm => ?_⟩
          · rw [hnet]; exact h.wire_logged m hm
          · rw [hnet] at hm; rw [hreq]; exact h.net_payload m hm
        · exact h
  | crash => exact ⟨rfl, ⟨h.wire_logged, h.net_payload⟩⟩
  | recover =>
    refine ⟨?_, ?_⟩
    · simp only [stepC, opsOf, run, List.foldl]
      split_ifs <;> rfl
    · simp only [stepC]
      split_ifs
      · exact h
      · refine ⟨fun m hm => ?_, h.net_payload⟩
        simp only [List.mem_append] at hm
        rcases hm with hm | hm
        · exact h.wire_logged m hm
        · simp only [unacked, List.mem_map, List.mem_filter] at hm
          obtain ⟨d, ⟨hd, -⟩, rfl⟩ := hm
          exact List.mem_map.2 ⟨d, hd, rfl⟩
  | halt c =>
    refine ⟨?_, ?_⟩
    · simp only [stepC, opsOf, run, List.foldl, step]
      split_ifs <;> rfl
    · simp only [stepC]
      split_ifs
      · exact ⟨h.wire_logged, h.net_payload⟩
      · exact h
  | bankCall c key tx =>
    simp only [legalC] at ho
    refine ⟨?_, ?_⟩
    · simp [stepC, opsOf, run, step, full, ho]
    · simp only [stepC, ho, ne_eq, not_false_eq_true, if_true]
      exact h

/-! ## Transfer of SC-26 safety to the concrete machine -/

/-- the model trace matching a concrete trace -/
def absTrace (R : Roles) (cap : ℕ) : CSt → List COp → List Op
  | _, [] => []
  | s, o :: ops => opsOf s o ++ absTrace R cap (stepC R cap true s o) ops

theorem run_append (R : Roles) (cap : ℕ) (C : Checks) (s : St) (a b : List Op) :
    run R cap C s (a ++ b) = run R cap C (run R cap C s a) b := by
  simp [run, List.foldl_append]

theorem simulation_run (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp) (hops : ∀ o ∈ ops, legalC R o)
    (h : CInv s) :
    α (runC R cap true s ops) = run R cap full (α s) (absTrace R cap s ops) ∧ CInv (runC R cap true s ops) := by
  induction ops generalizing s with
  | nil => exact ⟨rfl, h⟩
  | cons o ops ih =>
    obtain ⟨h1, h2⟩ := simulation R cap s o (hops o List.mem_cons_self) h
    obtain ⟨ih1, ih2⟩ := ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')) h2
    refine ⟨?_, ih2⟩
    change α (runC R cap true (stepC R cap true s o) ops) = run R cap full (α s) (opsOf s o ++ absTrace R cap _ ops)
    rw [ih1, run_append, h1]

theorem opsOf_legal (R : Roles) (s : CSt) (o : COp) (ho : legalC R o) : ∀ a ∈ opsOf s o, legal R a := by
  intro a ha
  cases o <;> simp only [opsOf] at ha
  all_goals first
    | (simp only [List.mem_singleton] at ha; subst ha; exact ho)
    | (split_ifs at ha <;> simp only [List.mem_singleton, List.not_mem_nil] at ha; subst ha; trivial)
    | simp at ha

theorem absTrace_legal (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp) (hops : ∀ o ∈ ops, legalC R o) :
    ∀ a ∈ absTrace R cap s ops, legal R a := by
  induction ops generalizing s with
  | nil => intro a ha; simp [absTrace] at ha
  | cons o ops ih =>
    intro a ha
    simp only [absTrace, List.mem_append] at ha
    rcases ha with ha | ha
    · exact opsOf_legal R s o (hops o List.mem_cons_self) a ha
    · exact ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')) a ha

theorem α_init : α cinit = init := rfl

/-- **SC-26 safety for the concrete machine.** For every legal concrete trace from the initial state (any
interleaving, crashes, re-transmissions, network duplication), α of the reached state satisfies `SC26.Good`: every
bank entry is exactly approved by an approver who is not the requester, bank keys are unique, and the total is within
the cap. -/
theorem concrete_safe (R : Roles) (cap : ℕ) (ops : List COp) (hops : ∀ o ∈ ops, legalC R o) :
    Good R cap (α (runC R cap true cinit ops)) := by
  rw [(simulation_run R cap cinit ops hops cinv_init).1, α_init]
  exact sc26_safe R cap _ (absTrace_legal R cap cinit ops hops)

/-! ## The concrete halt corollary -/

theorem stepC_halted (R : Roles) (cap : ℕ) (s : CSt) (o : COp) (ho : legalC R o) (hh : s.halted = true) :
    (stepC R cap true s o).halted = true ∧ (stepC R cap true s o).wire = s.wire ∧
      ∀ e ∈ (stepC R cap true s o).bank, e ∈ s.bank ∨ e ∈ s.wire := by
  cases o with
  | bankProcess key =>
    simp only [stepC]
    split
    · exact ⟨hh, rfl, fun e he => Or.inl he⟩
    · rename_i m hm
      refine ⟨hh, rfl, fun e he => ?_⟩
      simp only [bankApply] at he
      split_ifs at he
      · exact Or.inl he
      · rcases List.mem_append.1 he with he | he
        · exact Or.inl he
        · simp only [List.mem_singleton] at he; subst he; exact Or.inr (List.mem_of_find?_eq_some hm)
  | ack i =>
    simp only [stepC]
    split
    · exact ⟨hh, rfl, fun e he => Or.inl he⟩
    · split_ifs
      · exact ⟨hh, rfl, fun e he => Or.inl he⟩
      · exact ⟨hh, rfl, fun e he => Or.inl he⟩
  | crash => exact ⟨hh, rfl, fun e he => Or.inl he⟩
  | halt c =>
    simp only [stepC]
    split_ifs
    · exact ⟨rfl, rfl, fun e he => Or.inl he⟩
    · exact ⟨hh, rfl, fun e he => Or.inl he⟩
  | bankCall c key tx =>
    simp only [legalC] at ho
    have : stepC R cap true s (.bankCall c key tx) = s := by simp [stepC, ho]
    rw [this]
    exact ⟨hh, rfl, fun e he => Or.inl he⟩
  | _ => exact ⟨by simp [stepC, hh], by simp [stepC, hh], fun e he => Or.inl (by simpa [stepC, hh] using he)⟩

/-- **Concrete HALT.** After a concrete halt, no (re-)transmission is accepted for the rest of any legal trace, and
the bank only gains messages that were transmitted before the halt. -/
theorem concrete_halt (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp) (hops : ∀ o ∈ ops, legalC R o)
    (hh : s.halted = true) :
    (runC R cap true s ops).wire = s.wire ∧ ∀ e ∈ (runC R cap true s ops).bank, e ∈ s.bank ∨ e ∈ s.wire := by
  induction ops generalizing s with
  | nil => exact ⟨rfl, fun e he => Or.inl he⟩
  | cons o ops ih =>
    obtain ⟨h1, h2, h3⟩ := stepC_halted R cap s o (hops o List.mem_cons_self) hh
    obtain ⟨ih1, ih2⟩ := ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')) h1
    change (runC R cap true (stepC R cap true s o) ops).wire = s.wire ∧
      ∀ e ∈ (runC R cap true (stepC R cap true s o) ops).bank, e ∈ s.bank ∨ e ∈ s.wire
    refine ⟨ih1.trans h2, fun e he => ?_⟩
    rcases ih2 e he with h | h
    · exact h3 e h
    · right; rw [← h2]; exact h

/-! ## Witness: recovery that ignores HALT -/

def wTx : Tx := ⟨5, 10, 0⟩

/-- a halted gate with one logged intent that was never transmitted (stranded by the halt) -/
def strandedState : CSt := ⟨1, [⟨0, 1, wTx⟩], [(0, 2, wTx)], [0], 10, true, [⟨0, wTx, false⟩], none, [], []⟩

/-- **Recovery must check HALT** (the v2 → v3 checker blind spot). With `recoverChecksHalt = false`, a restarted,
halted gate re-transmits the stranded intent and the bank pays it, although it was never transmitted before the
halt. With the v3 recovery (`true`), the bank stays empty. -/
theorem recover_halt_witness :
    (runC R0 10 false strandedState [.recover, .bankProcess 0]).bank = [(0, wTx)] ∧
    (0, wTx) ∉ strandedState.bank ∧ (0, wTx) ∉ strandedState.wire ∧
    (runC R0 10 true strandedState [.recover, .bankProcess 0]).bank = [] := by
  decide

end ControlStack.SC26Refinement

#print axioms ControlStack.SC26Refinement.simulation
#print axioms ControlStack.SC26Refinement.simulation_run
#print axioms ControlStack.SC26Refinement.concrete_safe
#print axioms ControlStack.SC26Refinement.concrete_halt
#print axioms ControlStack.SC26Refinement.recover_halt_witness
