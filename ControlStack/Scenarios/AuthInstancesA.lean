/-
Authenticated-issuer instances (Core/Authenticated.lean, Core/AuthenticatedLog.lean), part A: SC-16, SC-25, SC-28,
SC-17, SC-19.

Each scenario model reads an operation's caller field as the act of that principal. Here every operation is issued by
a TRUE issuer (the platform-reported identity, e.g. SO_PEERCRED or a workload identity). An operation claiming an
identity is applied only if issued by it (`claimNN`). Gate-internal and environment events claim nothing. For each
scenario, `scNN_safe_authenticated` states:
- the scenario's safety theorem on the authenticated run (`authRun = run` on the authenticated sub-trace), and
- every trusted act the safety property cites (review, approval, verdict, lease, verification) was ISSUED by a
  principal holding the trusted role. Under `U ∩ role = ∅` that issuer is not the adversary.
`forged_*` (where cheap, by `decide`): necessity. An adversary issuing every operation itself, with forged identity
claims, causes the effect without authentication and nothing with it.

Adversary class TRACE_ARBITRARY over issued traces; the adversary chooses any operations with issuers in U.
What remains a premise: that the platform-reported identity is the issuer. Not claimed: anything about genuine but
coerced or deceived trusted principals. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.AuthenticatedLog
import ControlStack.Scenarios.SC16Deploy
import ControlStack.Scenarios.SC25Audit
import ControlStack.Scenarios.SC28Budget
import ControlStack.Scenarios.SC17Infra
import ControlStack.Scenarios.SC19Prod

namespace ControlStack.AuthInstances

open ControlStack.Gate ControlStack.Authenticated ControlStack.AuthenticatedLog

/-! ## SC-16: reviewer and approver -/

section SC16
open ControlStack.SC16

def claim16 : SC16.Op → Option ℕ
  | .stage c _ => some c
  | .writeSlot c _ _ => some c
  | .review c _ => some c
  | .approve c _ _ _ _ => some c
  | .deploy c _ _ _ => some c
  | .halt c => some c

theorem sc16_review_step (R : Roles) (h : ℕ → ℕ) (s : SC16.St) (o : SC16.Op) (x : Review)
    (hx : x ∈ (SC16.step R h full s o).reviews) :
    x ∈ s.reviews ∨ ∃ c, claim16 o = some c ∧ (o = .review c x.d ∧ c = x.reviewer ∧ c ∈ R.reviewers) := by
  cases o <;> simp only [SC16.step, doDeploy] at hx <;> (repeat' split at hx) <;> simp_all [claim16]
  rcases hx with hx | rfl <;> simp_all

theorem sc16_appr_step (R : Roles) (h : ℕ → ℕ) (s : SC16.St) (o : SC16.Op) (x : Appr)
    (hx : x ∈ (SC16.step R h full s o).approvals) :
    x ∈ s.approvals ∨ ∃ c, claim16 o = some c ∧
      (o = .approve c x.n x.d x.target x.slot ∧ c = x.approver ∧ c ∈ R.approvers) := by
  cases o <;> simp only [SC16.step, doDeploy] at hx <;> (repeat' split at hx) <;> simp_all [claim16]
  rcases hx with hx | rfl <;> simp_all

/-- **SC-16 with authenticated issuers.** -/
theorem sc16_safe_authenticated (R : Roles) (h : ℕ → ℕ) (U : List ℕ) (ops : List (ℕ × SC16.Op))
    (hUr : ∀ u ∈ U, u ∉ R.reviewers) (hUa : ∀ u ∈ U, u ∉ R.approvers) :
    Good R h (authRun (SC16.step R h full) claim16 SC16.init ops) ∧
    (∀ rv ∈ (authRun (SC16.step R h full) claim16 SC16.init ops).reviews, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .review c rv.d ∧ c = rv.reviewer ∧ c ∈ R.reviewers)) ∧
    (∀ ap ∈ (authRun (SC16.step R h full) claim16 SC16.init ops).approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .approve c ap.n ap.d ap.target ap.slot ∧ c = ap.approver ∧ c ∈ R.approvers)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [authRun_eq]; exact sc16_safe R h _
  · exact issued_trusted _ claim16 SC16.St.reviews _ R.reviewers U (sc16_review_step R h)
      (fun _ _ _ hp => hp.2.2) hUr SC16.init rfl ops
  · exact issued_trusted _ claim16 SC16.St.approvals _ R.approvers U (sc16_appr_step R h)
      (fun _ _ _ hp => hp.2.2) hUa SC16.init rfl ops

/-- agent 1 issues everything, forging the review (as reviewer 2) and the approval (as approver 3) -/
def forged16 : List (ℕ × SC16.Op) := [(1, .stage 1 7), (1, .review 2 7), (1, .approve 3 0 7 5 0), (1, .deploy 1 0 5 7)]

/-- **Necessity (SC-16).** Without authentication the forged review and approval deploy; with it nothing deploys. -/
theorem forged16_deploys_without_auth :
    (authRun (SC16.step R0 id full) (fun _ => none) SC16.init forged16).deployed = [⟨0, 5, 7⟩] ∧
    (authRun (SC16.step R0 id full) claim16 SC16.init forged16).deployed = [] := by
  decide

end SC16

/-! ## SC-25: auditor and approver -/

section SC25
open ControlStack.SC25

def claim25 : SC25.Op → Option ℕ
  | .submit c _ _ _ => some c
  | .amend c _ _ => some c
  | .audit c _ _ => some c
  | .approve c _ => some c
  | .halt c => some c
  | .timeout _ => none
  | .check _ => none
  | .fire _ => none
  | .crash => none

theorem sc25_verdict_step (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : SC25.St) (o : SC25.Op) (x : Verdict)
    (hx : x ∈ (SC25.step R h cls full s o).verdicts) :
    x ∈ s.verdicts ∨ ∃ c, claim25 o = some c ∧ (o = .audit c x.id x.pass ∧ x.by_ = some c ∧ c ∈ R.auditors) := by
  cases o <;> simp only [SC25.step] at hx <;> (repeat' split at hx) <;> simp_all [claim25, full]
  rcases hx with hx | rfl <;> simp_all

theorem sc25_appr_step (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : SC25.St) (o : SC25.Op) (x : SC25.Appr)
    (hx : x ∈ (SC25.step R h cls full s o).approvals) :
    x ∈ s.approvals ∨ ∃ c, claim25 o = some c ∧ (o = .approve c x.id ∧ c = x.approver ∧ c ∈ R.approvers) := by
  cases o <;> simp only [SC25.step] at hx <;> (repeat' split at hx) <;> simp_all [claim25, full]
  rcases hx with hx | rfl <;> simp_all

/-- **SC-25 with authenticated issuers.** -/
theorem sc25_safe_authenticated (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (U : List ℕ) (ops : List (ℕ × SC25.Op))
    (hUv : ∀ u ∈ U, u ∉ R.auditors) (hUa : ∀ u ∈ U, u ∉ R.approvers) :
    Good R h cls (authRun (SC25.step R h cls full) claim25 SC25.init ops) ∧
    (∀ v ∈ (authRun (SC25.step R h cls full) claim25 SC25.init ops).verdicts, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .audit c v.id v.pass ∧ v.by_ = some c ∧ c ∈ R.auditors)) ∧
    (∀ ap ∈ (authRun (SC25.step R h cls full) claim25 SC25.init ops).approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .approve c ap.id ∧ c = ap.approver ∧ c ∈ R.approvers)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [authRun_eq]; exact sc25_safe R h cls _
  · exact issued_trusted _ claim25 SC25.St.verdicts _ R.auditors U (sc25_verdict_step R h cls)
      (fun _ _ _ hp => hp.2.2) hUv SC25.init rfl ops
  · exact issued_trusted _ claim25 SC25.St.approvals _ R.approvers U (sc25_appr_step R h cls)
      (fun _ _ _ hp => hp.2.2) hUa SC25.init rfl ops

/-- agent 1 submits a reversible operation and forges the auditor's PASS (as auditor 2) -/
def forged25 : List (ℕ × SC25.Op) := [(1, .submit 1 0 7 false), (1, .audit 2 0 true), (1, .check 0), (1, .fire 0)]

/-- **Necessity (SC-25).** Without authentication the forged verdict executes the operation; with it nothing runs. -/
theorem forged25_executes_without_auth :
    ((authRun (SC25.step R0 id cls0 full) (fun _ => none) SC25.init forged25).executed.map Exec.id) = [0] ∧
    (authRun (SC25.step R0 id cls0 full) claim25 SC25.init forged25).executed = [] := by
  decide

end SC25

/-! ## SC-28: admin issues leases -/

section SC28
open ControlStack.SC28

def claim28 : SC28.Op → Option ℕ
  | .issue c _ _ => some c
  | .assignTo c _ _ => some c
  | .fork c _ _ _ => some c
  | .revoke c _ => some c
  | .work w _ _ => some w
  | .restart => none
  | .rollback _ => none
  | .halt c => some c

theorem sc28_lease_step (admins : List ℕ) (G : ℕ) (s : SC28.St) (o : SC28.Op) (x : ℕ × ℕ)
    (hx : x ∈ (SC28.step admins G full s o).leases) :
    x ∈ s.leases ∨ ∃ c, claim28 o = some c ∧ (o = .issue c x.1 x.2 ∧ c ∈ admins) := by
  cases o <;> simp only [SC28.step, forkUpd_full_leases] at hx <;> (repeat' split at hx) <;>
    simp_all [claim28]
  rcases hx with hx | rfl <;> simp_all

theorem sc28_revoke_step (admins : List ℕ) (G : ℕ) (s : SC28.St) (o : SC28.Op) (x : ℕ)
    (hx : x ∈ (SC28.step admins G full s o).revoked) :
    x ∈ s.revoked ∨ ∃ c, claim28 o = some c ∧ (o = .revoke c x ∧ c ∈ admins) := by
  cases o <;> simp only [SC28.step] at hx <;> (repeat' split at hx) <;> simp_all [claim28]
  rcases hx with hx | rfl <;> simp_all

/-- **SC-28 with authenticated issuers.** The rollback exclusion (`legal`) is still a premise on every operation. -/
theorem sc28_safe_authenticated (admins : List ℕ) (G : ℕ) (U : List ℕ) (ops : List (ℕ × SC28.Op))
    (hU : ∀ u ∈ U, u ∉ admins) (hlegal : ∀ io ∈ ops, SC28.legal io.2) :
    Good G (authRun (SC28.step admins G full) claim28 SC28.init ops) ∧
    (∀ l ∈ (authRun (SC28.step admins G full) claim28 SC28.init ops).leases, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .issue c l.1 l.2 ∧ c ∈ admins)) ∧
    (∀ l ∈ (authRun (SC28.step admins G full) claim28 SC28.init ops).revoked, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .revoke c l ∧ c ∈ admins)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [authRun_eq]
    exact sc28_safe admins G _ (fun o ho => by
      obtain ⟨i, hi⟩ := mem_of_applied claim28 ops o ho
      exact hlegal _ hi)
  · exact issued_trusted _ claim28 SC28.St.leases _ admins U (sc28_lease_step admins G)
      (fun _ _ _ hp => hp.2) hU SC28.init rfl ops
  · exact issued_trusted _ claim28 SC28.St.revoked _ admins U (sc28_revoke_step admins G)
      (fun _ _ _ hp => hp.2) hU SC28.init rfl ops

/-- agent 1 forges the admin's lease issue and assignment (as admin 9), then works -/
def forged28 : List (ℕ × SC28.Op) := [(1, .issue 9 0 100), (1, .assignTo 9 1 0), (1, .work 1 5 5)]

/-- **Necessity (SC-28).** Without authentication the agent grants itself a budget and consumes it; with it nothing. -/
theorem forged28_consumes_without_auth :
    (authRun (SC28.step [9] 1000 full) (fun _ => none) SC28.init forged28).usage = [(1, 0, 5)] ∧
    (authRun (SC28.step [9] 1000 full) claim28 SC28.init forged28).usage = [] := by
  decide

end SC28

/-! ## SC-17: reviewer (and author identity) -/

section SC17
open ControlStack.SC17

def claim17 : SC17.Op → Option ℕ
  | .propose c _ _ => some c
  | .amend c _ _ => some c
  | .approve c _ => some c
  | .halt c => some c
  | .oob _ => none
  | .reconcile => none
  | .apply _ => none

theorem sc17_appr_step (E : Env) (s : SC17.St) (o : SC17.Op) (x : Ap)
    (hx : x ∈ (SC17.step E full s o).approvals) :
    x ∈ s.approvals ∨ ∃ c, claim17 o = some c ∧ (o = .approve c x.id ∧ c = x.reviewer ∧ c ∈ E.reviewers) := by
  cases o <;> simp only [SC17.step] at hx <;> (repeat' split at hx) <;> simp_all [claim17]
  rcases hx with hx | rfl <;> simp_all

theorem sc17_prop_step (E : Env) (s : SC17.St) (o : SC17.Op) (x : Pr)
    (hx : x ∈ (SC17.step E full s o).props) :
    x ∈ s.props ∨ ∃ c, claim17 o = some c ∧ (c = x.author ∧ (o = .propose c x.id x.diff ∨ o = .amend c x.id x.diff)) := by
  cases o <;> simp only [SC17.step] at hx <;> (repeat' split at hx) <;> simp_all [claim17]
  all_goals (rcases hx with rfl | hx <;> simp_all)

/-- **SC-17 with authenticated issuers.** Every applied change's approval was issued by a reviewer, and every
proposal's author is the issuer of that proposal, so "reviewer ≠ author" compares two issuers. -/
theorem sc17_safe_authenticated (E : Env) (g0 : List SC17.G) (U : List ℕ) (ops : List (ℕ × SC17.Op))
    (hU : ∀ u ∈ U, u ∉ E.reviewers) :
    Good E (authRun (SC17.step E full) claim17 (SC17.init g0) ops) ∧
    (∀ a ∈ (authRun (SC17.step E full) claim17 (SC17.init g0) ops).approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .approve c a.id ∧ c = a.reviewer ∧ c ∈ E.reviewers)) ∧
    (∀ p ∈ (authRun (SC17.step E full) claim17 (SC17.init g0) ops).props, ∃ c o, (c, o) ∈ ops ∧
      (c = p.author ∧ (o = .propose c p.id p.diff ∨ o = .amend c p.id p.diff))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [authRun_eq]; exact sc17_safe E g0 _
  · exact issued_trusted _ claim17 SC17.St.approvals _ E.reviewers U (sc17_appr_step E)
      (fun _ _ _ hp => hp.2.2) hU (SC17.init g0) rfl ops
  · exact issued_of_mem_log _ claim17 SC17.St.props _ (sc17_prop_step E) (SC17.init g0) rfl ops

/-- author 1 proposes and forges the reviewer's approval (as reviewer 2) -/
def forged17 : List (ℕ × SC17.Op) := [(1, .propose 1 0 dA), (1, .approve 2 0), (1, .apply 0)]

/-- **Necessity (SC-17).** Without authentication the self-approved change is applied; with it nothing is. -/
theorem forged17_applies_without_auth :
    (authRun (SC17.step E0 full) (fun _ => none) (SC17.init []) forged17).live = [(1, 1, 1)] ∧
    (authRun (SC17.step E0 full) claim17 (SC17.init []) forged17).applied = [] := by
  decide

end SC17

/-! ## SC-19: approver and verifier -/

section SC19
open ControlStack.SC19

def claim19 : SC19.Op → Option ℕ
  | .verify c _ => some c
  | .prepare c _ _ => some c
  | .approve c _ => some c
  | .halt c => some c
  | .write _ _ => none
  | .snapshot _ => none
  | .commit _ _ => none

theorem sc19_appr_step (E : Env) (s : SC19.St) (o : SC19.Op) (x : ℕ × ℕ × ℕ)
    (hx : x ∈ (SC19.step E full s o).approvals) :
    x ∈ s.approvals ∨ ∃ c, claim19 o = some c ∧ (o = .approve c x.1 ∧ c = x.2.1 ∧ c ∈ E.approvers) := by
  cases o <;> simp only [SC19.step] at hx <;> (repeat' split at hx) <;> simp_all [claim19]
  rcases hx with hx | rfl <;> simp_all

theorem sc19_verify_step (E : Env) (s : SC19.St) (o : SC19.Op) (x : ℕ)
    (hx : x ∈ (SC19.step E full s o).verified) :
    x ∈ s.verified ∨ ∃ c, claim19 o = some c ∧ (o = .verify c x ∧ c ∈ E.verifiers) := by
  cases o <;> simp only [SC19.step] at hx <;> (repeat' split at hx) <;> simp_all [claim19]
  rcases hx with hx | rfl <;> simp_all

/-- **SC-19 with authenticated issuers.** -/
theorem sc19_safe_authenticated (E : Env) (U : List ℕ) (ops : List (ℕ × SC19.Op))
    (hUa : ∀ u ∈ U, u ∉ E.approvers) (hUv : ∀ u ∈ U, u ∉ E.verifiers) :
    Good E (authRun (SC19.step E full) claim19 SC19.init ops) ∧
    (∀ a ∈ (authRun (SC19.step E full) claim19 SC19.init ops).approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .approve c a.1 ∧ c = a.2.1 ∧ c ∈ E.approvers)) ∧
    (∀ i ∈ (authRun (SC19.step E full) claim19 SC19.init ops).verified, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .verify c i ∧ c ∈ E.verifiers)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [authRun_eq]; exact sc19_safe E _
  · exact issued_trusted _ claim19 SC19.St.approvals _ E.approvers U (sc19_appr_step E)
      (fun _ _ _ hp => hp.2.2) hUa SC19.init rfl ops
  · exact issued_trusted _ claim19 SC19.St.verified _ E.verifiers U (sc19_verify_step E)
      (fun _ _ _ hp => hp.2) hUv SC19.init rfl ops

/-- author 1 issues everything, forging the restore verification (as verifier 3) and the approval (as approver 2) -/
def forged19 : List (ℕ × SC19.Op) :=
  [(1, .write 7 5), (1, .snapshot 7), (1, .verify 3 0), (1, .prepare 1 0 7), (1, .approve 2 0), (1, .commit 0 0)]

/-- **Necessity (SC-19).** Without authentication the destructive change commits; with it nothing is destroyed. -/
theorem forged19_destroys_without_auth :
    (authRun (SC19.step E0 full) (fun _ => none) SC19.init forged19).destroyed = [⟨0, 1, 7, 1, 5, 0⟩] ∧
    (authRun (SC19.step E0 full) claim19 SC19.init forged19).destroyed = [] := by
  decide

end SC19

end ControlStack.AuthInstances

#print axioms ControlStack.AuthInstances.sc16_safe_authenticated
#print axioms ControlStack.AuthInstances.forged16_deploys_without_auth
#print axioms ControlStack.AuthInstances.sc25_safe_authenticated
#print axioms ControlStack.AuthInstances.forged25_executes_without_auth
#print axioms ControlStack.AuthInstances.sc28_safe_authenticated
#print axioms ControlStack.AuthInstances.forged28_consumes_without_auth
#print axioms ControlStack.AuthInstances.sc17_safe_authenticated
#print axioms ControlStack.AuthInstances.forged17_applies_without_auth
#print axioms ControlStack.AuthInstances.sc19_safe_authenticated
#print axioms ControlStack.AuthInstances.forged19_destroys_without_auth
