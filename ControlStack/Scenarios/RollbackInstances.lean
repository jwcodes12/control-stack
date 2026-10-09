/-
Anti-rollback instances (`Core/AntiRollback.lean`) for SC-26 and for the joint LabStack gate.

(a) SC-26. The gate's durable store (requests, approvals, the nonce history `reserved`, spending, sent messages) sits
behind the trusted monotonic anchor. `sc26_rollback_safe`: under ANY interleaving of legal operations, crashes,
restarts and restores of the gate's store to any backup, the released payments are the bank of a plain legal run, so
`SC26.Good` holds of them (exactly approved, unique keys, within the cap).
Witness, `sc26_rollback_without_anchor`: without the anchor, restoring the backup taken before `execute` lets the
consumed approval be RESERVED AGAIN (two committed executions of request 0: a double charge against the budget), and
the payment instruction is released twice. Defence in depth: the receiving bank is idempotent by key
(`receiverLedger`), so the money moves ONCE. With the anchor, the restored store is refused (fail closed), and the
payment is released once.

(b) LabStack. The joint lab gate (SC-26 + SC-16 + SC-28 with the shared money counter and halt) is wrapped as a
`Gate.System` whose effect log is the payment bank, with spec `LabInv`. `lab_rollback_safe`: under arbitrary restores
of the lab's store (money counter, nonce history, leases), the anchored state is a plain legal lab run, so the GLOBAL
budget (payments + price × compute usage ≤ G) and every component's safety hold. This replaces the "no counter
rollback" part of LabStack's `legal` premise by the anchor premise.
Witness, `lab_rollback_reopens_budget`: without the anchor, restoring the genesis backup after a payment of 10
resets the money counter, and compute then spends another 10. Released payments (10) plus anchored compute usage (10)
= 20 > G = 10. With the anchor the restore is refused.

Premises: the anchor (monotonic, not resettable by the operator) and record integrity, as in `Core/AntiRollback.lean`.
The bank's idempotency in (a) is a property of the receiver, outside the gate. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.AntiRollback
import ControlStack.Scenarios.LabStack

namespace ControlStack.RollbackInstances

open ControlStack.Gate ControlStack.AntiRollback

/-! ## (a) SC-26 -/

theorem run_sys26 (R : SC26.Roles) (cap : ℕ) (l : List {o : SC26.Op // SC26.legal R o}) (s : SC26.St) :
    (SC26.sys R cap).run s l = SC26.run R cap SC26.full s (l.map Subtype.val) := by
  induction l generalizing s with
  | nil => rfl
  | cons o l ih => exact ih _

/-- **SC-26 under storage rollback.** The released payments are the bank of a plain legal run of the committed ops, so
`SC26.Good` holds of them, whatever restores of the gate's store happened. -/
theorem sc26_rollback_safe (R : SC26.Roles) (cap : ℕ) (ops : List (ROp {o : SC26.Op // SC26.legal R o})) :
    let t := runR (SC26.sys R cap) true (rinit (SC26.sys R cap) SC26.init) ops
    t.released = (SC26.run R cap SC26.full SC26.init (t.committed.map Subtype.val)).bank ∧
      SC26.Good R cap (SC26.run R cap SC26.full SC26.init (t.committed.map Subtype.val)) := by
  have h := rollback_transfer (SC26.sys R cap) (SC26.spec R cap) SC26.init (SC26.inv_init R cap) ops
  refine ⟨?_, ?_⟩
  · rw [h.2.1, run_sys26]; rfl
  · have hinv := h.2.2.1
    rw [run_sys26] at hinv
    exact hinv.good

/-- the receiving bank applies a payment instruction once per key (idempotency at the receiver) -/
def receiverLedger (l : List (ℕ × SC26.Tx)) : List (ℕ × SC26.Tx) :=
  l.foldl (fun acc e => if e.1 ∈ acc.map Prod.fst then acc else acc ++ [e]) []

def w26 (o : SC26.Op) (h : SC26.legal SC26.R0 o) : ROp {o : SC26.Op // SC26.legal SC26.R0 o} := .write ⟨o, h⟩

/-- request, approve, execute, deliver, arrive (all committed); restore the backup taken after the approval (before
the execute); execute, deliver, arrive again -/
def payReplay : List (ROp {o : SC26.Op // SC26.legal SC26.R0 o}) :=
  [w26 (.request 1 SC26.tx1) trivial, .bump, w26 (.approve 2 0 SC26.tx1) trivial, .bump, w26 (.execute 1 0) trivial,
   .bump, w26 (.deliver 0) trivial, .bump, w26 (.arrive 0) trivial, .bump, .rollback 2,
   w26 (.execute 1 0) trivial, .bump, w26 (.deliver 0) trivial, .bump, w26 (.arrive 0) trivial, .bump]

abbrev G26 := SC26.sys SC26.R0 20

/-- **Without the anchor: double reservation, double instruction, one payment (receiver idempotency).** Two committed
executions of request 0 (the consumed approval is reserved again) and the payment instruction is released twice; the
idempotent receiver pays once. With the anchor the restored store is refused, the gate fails closed and the payment
is released once. -/
theorem sc26_rollback_without_anchor :
    let t := runR G26 false (rinit G26 SC26.init) payReplay
    (t.committed.map Subtype.val).count (.execute 1 0) = 2 ∧ t.released = [(0, SC26.tx1), (0, SC26.tx1)] ∧
      receiverLedger t.released = [(0, SC26.tx1)] ∧
    (runR G26 true (rinit G26 SC26.init) payReplay).released = [(0, SC26.tx1)] ∧
    (runR G26 true (rinit G26 SC26.init) payReplay).halted = true := by
  decide

/-! ## (b) LabStack -/

open ControlStack.LabStack

theorem payStep_bank (P : LabParams) (share : Bool) (s : LabSt) (p : SC26.St) (hp : s.pay.bank <+: p.bank) :
    s.pay.bank <+: (payStep P share s p).pay.bank := by
  unfold payStep
  split_ifs
  · exact hp
  · exact List.prefix_refl _

theorem compStep_bank (P : LabParams) (share : Bool) (s : LabSt) (c : SC28.St) :
    (compStep P share s c).pay.bank = s.pay.bank := by
  unfold compStep
  split_ifs <;> rfl

theorem lab_bank_prefix (P : LabParams) (s : LabSt) (o : LabOp) : s.pay.bank <+: (labStep P true s o).pay.bank := by
  cases o with
  | pay o =>
    simp only [labStep]
    split_ifs
    · exact List.prefix_refl _
    · exact payStep_bank P true s _ (SC26.bank_prefix _ _ _ _ _)
  | dep o => simp only [labStep]; split_ifs <;> exact List.prefix_refl _
  | comp o =>
    simp only [labStep]; split_ifs
    · exact List.prefix_refl _
    · rw [compStep_bank]
  | deployPay n =>
    simp only [labStep]; split_ifs
    · exact List.prefix_refl _
    · exact payStep_bank P true s _ (SC26.bank_prefix _ _ _ _ _)
  | halt c => simp only [labStep]; split_ifs <;> exact List.prefix_refl _

/-- the joint lab gate as a `Gate.System` over legal lab operations; its effect log is the payment bank -/
def labSys (P : LabParams) : System LabSt {o : LabOp // labLegal P o} (ℕ × SC26.Tx) where
  step := fun s o => labStep P true s o.1
  effects := fun s => s.pay.bank

def labSpec (P : LabParams) : Spec (labSys P) where
  Inv := LabInv P
  ok := fun _ _ => True
  step_inv := fun s o h => labStep_inv P true s o.1 o.2 h
  log_prefix := fun s o => lab_bank_prefix P s o.1
  inv_ok := fun _ _ _ _ => trivial

theorem run_lab (P : LabParams) (l : List {o : LabOp // labLegal P o}) (s : LabSt) :
    (labSys P).run s l = labRun P true s (l.map Subtype.val) := by
  induction l generalizing s with
  | nil => rfl
  | cons o l ih => exact ih _

/-- **The lab under storage rollback.** After any interleaving of legal lab operations, crashes, restarts and restores
of the lab's store, the released payments are the bank of a plain legal lab run, which satisfies `LabInv`. So every
component invariant and the GLOBAL budget (payments + price × compute usage ≤ G) hold. -/
theorem lab_rollback_safe (P : LabParams) (ops : List (ROp {o : LabOp // labLegal P o})) :
    let t := runR (labSys P) true (rinit (labSys P) labInit) ops
    let r := labRun P true labInit (t.committed.map Subtype.val)
    t.released = r.pay.bank ∧ LabInv P r ∧
      (r.pay.bank.map (fun e => e.2.amount)).sum + P.price * SC28.usedT r.comp ≤ P.G := by
  have h := rollback_transfer (labSys P) (labSpec P) labInit (labInv_init P) ops
  have hinv : LabInv P (labRun P true labInit
      ((runR (labSys P) true (rinit (labSys P) labInit) ops).committed.map Subtype.val)) := by
    have := h.2.2.1
    rw [run_lab] at this
    exact this
  refine ⟨by rw [h.2.1, run_lab]; rfl, hinv, global_budget P _ hinv⟩

def wl (o : LabOp) (h : labLegal P0 o) : ROp {o : LabOp // labLegal P0 o} := .write ⟨o, h⟩

/-- pay 10 (request … arrive, committed), restore the genesis backup (money counter 0), then compute 10 -/
def budgetReplay : List (ROp {o : LabOp // labLegal P0 o}) :=
  [wl (.pay (.request 1 SC26.tx1)) trivial, .bump, wl (.pay (.approve 2 0 SC26.tx1)) trivial, .bump,
   wl (.pay (.execute 1 0)) trivial, .bump, wl (.pay (.deliver 0)) trivial, .bump, wl (.pay (.arrive 0)) trivial, .bump,
   .rollback 0,
   wl (.comp (.issue 9 0 10)) trivial, .bump, wl (.comp (.assignTo 9 1 0)) trivial, .bump,
   wl (.comp (.work 1 10 10)) trivial, .bump]

/-- **Without the anchor, restoring the money counter re-opens the global budget**: released payments 10 + anchored
compute usage 10 = 20 > G = 10. With the anchor the restore is refused (fail closed) and no compute is committed. -/
theorem lab_rollback_reopens_budget :
    let t := runR (labSys P0) false (rinit (labSys P0) labInit) budgetReplay
    (t.released.map (fun e => e.2.amount)).sum = 10 ∧ SC28.usedT t.anchor.st.comp = 10 ∧
    (runR (labSys P0) true (rinit (labSys P0) labInit) budgetReplay).halted = true ∧
    SC28.usedT (runR (labSys P0) true (rinit (labSys P0) labInit) budgetReplay).anchor.st.comp = 0 := by
  decide

end ControlStack.RollbackInstances

#print axioms ControlStack.RollbackInstances.sc26_rollback_safe
#print axioms ControlStack.RollbackInstances.sc26_rollback_without_anchor
#print axioms ControlStack.RollbackInstances.lab_rollback_safe
#print axioms ControlStack.RollbackInstances.lab_rollback_reopens_budget
