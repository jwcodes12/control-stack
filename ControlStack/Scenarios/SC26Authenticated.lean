/-
SC-26 with authenticated issuers: the instance of `Core/Authenticated.lean` (review finding 1).

`SC26.sc26_safe` reads an `approve c id tx` operation as approver `c`'s consent; the adversary may issue it with any
`c` (review D1 and REVIEW-PACKET-2026-10-09.md §0.1). Here every operation carries its TRUE issuer, reported by the
platform (SO_PEERCRED in the reference harness). Operations that claim an identity (request, approve, execute, direct
bank call, halt) are applied only if the claim equals the issuer (`claim`); `deliver` and `arrive` are gate-internal or
environment events and claim nothing.

Results:
- `sc26_safe_authenticated`: let the gate never issue a direct bank call (its bank traffic is `deliver`/`arrive`).
  For ANY issuers, the authenticated run satisfies `SC26.Good`, and every payment is backed by an `approve` operation
  of exactly its payload ISSUED BY an approver. If the untrusted issuers `U` are disjoint from the approvers, that
  issuer is not in `U`: the adversary cannot manufacture consent. "Credential separation" becomes the single premise
  "the platform-reported identity is the issuer".
- `forged_approval_pays_without_auth`: necessity. Agent 1 issues `approve 2 0 tx1` (claiming approver 2). Without
  authentication the payment lands and no approver issued anything; with authentication the forged approval is a
  no-op and nothing is paid.

Not claimed: that a real platform's identity mechanism is sound (that is the premise), or anything about approvals
whose issuer is a genuine but coerced or deceived approver. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Authenticated
import ControlStack.Scenarios.SC26Transaction

namespace ControlStack.SC26Authenticated

open ControlStack.Gate ControlStack.Authenticated ControlStack.SC26

/-- the SC-26 gate as a raw `Gate.System` (all operations, deployed checks) -/
def raw (R : Roles) (cap : ℕ) : System St Op (ℕ × Tx) := ⟨step R cap full, St.bank⟩

theorem raw_run (R : Roles) (cap : ℕ) (s : St) (ops : List Op) : (raw R cap).run s ops = run R cap full s ops := rfl

/-- the identity each operation claims; `deliver` and `arrive` claim none -/
def claim : Op → Option ℕ
  | .request c _ => some c
  | .approve c _ _ => some c
  | .execute c _ => some c
  | .bankCall c _ _ => some c
  | .halt c => some c
  | .deliver _ => none
  | .arrive _ => none

/-- an approval record is created only by an `approve` operation with exactly that caller, id and payload -/
theorem step_approvals (R : Roles) (cap : ℕ) (s : St) (o : Op) (x : ℕ × ℕ × Tx)
    (hx : x ∈ (step R cap full s o).approvals) : x ∈ s.approvals ∨ o = .approve x.2.1 x.1 x.2.2 := by
  cases o <;> simp only [step, bankAppend] at hx <;> (repeat' split at hx) <;> simp_all
  rcases hx with hx | rfl <;> simp_all

theorem run_approvals (R : Roles) (cap : ℕ) (ops : List Op) (s : St) (x : ℕ × ℕ × Tx)
    (hx : x ∈ (run R cap full s ops).approvals) : x ∈ s.approvals ∨ Op.approve x.2.1 x.1 x.2.2 ∈ ops := by
  induction ops generalizing s with
  | nil => exact Or.inl hx
  | cons o ops ih =>
    rw [run_cons] at hx
    rcases ih _ hx with h | h
    · rcases step_approvals R cap s o x h with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [h]; exact List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **SC-26 with authenticated issuers.** -/
theorem sc26_safe_authenticated (R : Roles) (cap : ℕ) (U : List ℕ) (ops : List (ℕ × Op))
    (hU : ∀ u ∈ U, u ∉ R.approvers)
    (hgate : ∀ io ∈ ops, ∀ c k tx, io.2 = .bankCall c k tx → io.1 ≠ R.gate) :
    Good R cap ((authed (raw R cap) claim).run init ops) ∧
      ∀ e ∈ ((authed (raw R cap) claim).run init ops).bank,
        ∃ a, a ∈ R.approvers ∧ a ∉ U ∧ (a, Op.approve a e.1 e.2) ∈ ops := by
  rw [authed_run, raw_run]
  have hlegal : ∀ o ∈ applied claim ops, legal R o := by
    intro o ho
    cases o with
    | bankCall c k tx =>
      have hmem := claim_issued_by claim ops _ c ho rfl
      exact hgate _ hmem c k tx rfl
    | _ => trivial
  have hgood := sc26_safe R cap (applied claim ops) hlegal
  refine ⟨hgood, ?_⟩
  intro e he
  obtain ⟨r, _, hrtx, _, a, happ, ha, _⟩ := hgood.1 e he
  rcases run_approvals R cap (applied claim ops) init _ happ with h | h
  · simp [init] at h
  · have hiss := claim_issued_by claim ops _ a h rfl
    rw [hrtx] at hiss
    exact ⟨a, ha, fun hu => hU a hu ha, hiss⟩

/-- the forged-approval trace: every operation is issued by agent 1; the `approve` claims approver 2 -/
def forged : List (ℕ × Op) :=
  [(1, .request 1 tx1), (1, .approve 2 0 tx1), (1, .execute 1 0), (1, .deliver 0), (1, .arrive 0)]

/-- **Necessity.** Without authentication (no operation claims an identity the guard checks) the forged approval
pays, and no approver issued any approval; with authentication nothing is paid. -/
theorem forged_approval_pays_without_auth :
    ((authed (raw R0 20) (fun _ => none)).run init forged).bank = [(0, tx1)] ∧
      (¬ ∃ a ∈ R0.approvers, (a, Op.approve a 0 tx1) ∈ forged) ∧
      ((authed (raw R0 20) claim).run init forged).bank = [] := by
  decide

end ControlStack.SC26Authenticated
