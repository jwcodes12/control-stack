/-
Authenticated-issuer instances, part B: SC-15, SC-20, SC-23, SC-12, SC-18 (see AuthInstancesA.lean for the pattern).

Notes per scenario:
- SC-15: CI results (`runCI`) carry no principal (an environment event). Their trustworthiness is a separate premise.
  Reviews and authorship are authenticated.
- SC-18: the model's `legal` premise ("an admin sets only the trusted sink") is now needed only for operations
  issued OUTSIDE the adversary set. Forged admin claims are refused by authentication, and the adversary's own claims
  are refused by the gate's admin check.
-/
import Mathlib.Tactic
import ControlStack.Core.AuthenticatedLog
import ControlStack.Scenarios.SC15Review
import ControlStack.Scenarios.SC20Data
import ControlStack.Scenarios.SC23Injection
import ControlStack.Scenarios.SC12Persistence
import ControlStack.Scenarios.SC18Logging

namespace ControlStack.AuthInstances

open ControlStack.Gate ControlStack.Authenticated ControlStack.AuthenticatedLog

/-! ## SC-15: reviewer (and author identity) -/

section SC15
open ControlStack.SC15

def claim15 : SC15.Op → Option ℕ
  | .propose a _ _ _ _ => some a
  | .amend a _ _ _ => some a
  | .review r _ _ => some r
  | .halt a => some a
  | .runCI _ => none
  | .merge _ => none

theorem roleOk_mem (E : Env) (sec : Bool) (r : ℕ) (h : roleOk E sec r = true) : r ∈ E.reviewers ++ E.security := by
  unfold roleOk at h
  split at h <;> simp_all

theorem sc15_review_step (E : Env) (s : SC15.St) (o : SC15.Op) (x : Rev)
    (hx : x ∈ (SC15.step E full s o).reviews) :
    x ∈ s.reviews ∨ ∃ c, claim15 o = some c ∧ (o = .review c x.id x.sec ∧ c = x.reviewer ∧ roleOk E x.sec c = true) := by
  cases o <;> simp only [SC15.step] at hx <;> (repeat' split at hx) <;> simp_all [claim15]
  rcases hx with hx | rfl <;> simp_all

/-- **SC-15 with authenticated issuers.** Every review cited by a merge was issued by a principal with the
reviewer (or security) role; the change author is the issuer of the proposal. -/
theorem sc15_safe_authenticated (E : Env) (U : List ℕ) (ops : List (ℕ × SC15.Op))
    (hU : ∀ u ∈ U, u ∉ E.reviewers ++ E.security) :
    (∀ c ∈ (authRun (SC15.step E full) claim15 SC15.init ops).merged,
      MergeOk E (authRun (SC15.step E full) claim15 SC15.init ops) c) ∧
    (∀ r ∈ (authRun (SC15.step E full) claim15 SC15.init ops).reviews, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .review c r.id r.sec ∧ c = r.reviewer ∧ roleOk E r.sec c = true)) := by
  refine ⟨?_, ?_⟩
  · rw [authRun_eq]; exact sc15_safe E _
  · exact issued_trusted _ claim15 SC15.St.reviews _ (E.reviewers ++ E.security) U (sc15_review_step E)
      (fun c _ x hp => roleOk_mem E x.sec c hp.2.2) hU SC15.init rfl ops

/-- author 1 proposes and forges the review (as reviewer 2) -/
def forged15 : List (ℕ × SC15.Op) :=
  [(1, .propose 1 0 7 [5] [5]), (1, .review 2 0 false), (1, .runCI 0), (1, .merge 0)]

/-- **Necessity (SC-15).** Without authentication the self-reviewed change merges; with it nothing merges. -/
theorem forged15_merges_without_auth :
    (authRun (SC15.step E0 full) (fun _ => none) SC15.init forged15).merged = [⟨0, 1, 7, [5], [5]⟩] ∧
    (authRun (SC15.step E0 full) claim15 SC15.init forged15).merged = [] := by
  decide

end SC15

/-! ## SC-20: promoting reviewer -/

section SC20
open ControlStack.SC20

def claim20 : SC20.Op → Option ℕ
  | .agentWrite c _ _ => some c
  | .promote c _ => some c
  | .freeze c _ => some c
  | .halt c => some c
  | .ingest _ _ _ => none
  | .edit _ _ => none
  | .train => none

theorem sc20_promote_step (E : Env) (s : SC20.St) (o : SC20.Op) (x : ℕ × ℕ × ℕ)
    (hx : x ∈ (SC20.step E full s o).promoted) :
    x ∈ s.promoted ∨ ∃ c, claim20 o = some c ∧ (o = .promote c x.1 ∧ c = x.2.1 ∧ c ∈ E.reviewers) := by
  cases o <;> simp only [SC20.step] at hx <;> (repeat' split at hx) <;> simp_all [claim20]
  rcases hx with hx | rfl <;> simp_all

/-- **SC-20 with authenticated issuers.** Every promotion was issued by a reviewer. -/
theorem sc20_safe_authenticated (E : Env) (U : List ℕ) (ops : List (ℕ × SC20.Op)) (hU : ∀ u ∈ U, u ∉ E.reviewers) :
    Good E (authRun (SC20.step E full) claim20 SC20.init ops) ∧
    (∀ p ∈ (authRun (SC20.step E full) claim20 SC20.init ops).promoted, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .promote c p.1 ∧ c = p.2.1 ∧ c ∈ E.reviewers)) := by
  refine ⟨?_, ?_⟩
  · rw [authRun_eq]; exact sc20_safe E _
  · exact issued_trusted _ claim20 SC20.St.promoted _ E.reviewers U (sc20_promote_step E)
      (fun _ _ _ hp => hp.2.2) hU SC20.init rfl ops

/-- agent 1 writes an example and forges the promotion (as reviewer 2) and the freeze (as admin 9) -/
def forged20 : List (ℕ × SC20.Op) := [(1, .agentWrite 1 1 66), (1, .promote 2 1), (1, .freeze 9 [1]), (1, .train)]

/-- **Necessity (SC-20).** Without authentication the agent's own example is trained on; with it nothing trains. -/
theorem forged20_trains_without_auth :
    (authRun (SC20.step E0 full) (fun _ => none) SC20.init forged20).trained = [[(1, 66)]] ∧
    (authRun (SC20.step E0 full) claim20 SC20.init forged20).trained = [] := by
  decide

end SC20

/-! ## SC-23: confirming user -/

section SC23
open ControlStack.SC23

def claim23 : SC23.Op → Option ℕ
  | .confirm c _ _ _ => some c
  | .halt c => some c
  | .userInput _ _ => none
  | .toolResult _ _ => none
  | .derive _ _ _ => none
  | .act _ _ _ => none

theorem sc23_conf_step (P : Policy) (s : SC23.St) (o : SC23.Op) (x : Conf)
    (hx : x ∈ (SC23.step P full s o).confs) :
    x ∈ s.confs ∨ ∃ c, claim23 o = some c ∧ (o = .confirm c x.n x.tool x.vals ∧ c = x.by_ ∧ c ∈ P.users) := by
  cases o <;> simp only [SC23.step, doExec] at hx <;> (repeat' split at hx) <;> simp_all [claim23]
  rcases hx with hx | rfl <;> simp_all

/-- **SC-23 with authenticated issuers.** Every confirmation a sensitive action relies on was issued by a user. -/
theorem sc23_safe_authenticated (P : Policy) (U : List ℕ) (ops : List (ℕ × SC23.Op)) (hU : ∀ u ∈ U, u ∉ P.users) :
    Good P (authRun (SC23.step P full) claim23 SC23.init ops) ∧
    (∀ cf ∈ (authRun (SC23.step P full) claim23 SC23.init ops).confs, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .confirm c cf.n cf.tool cf.vals ∧ c = cf.by_ ∧ c ∈ P.users)) := by
  refine ⟨?_, ?_⟩
  · rw [authRun_eq]; exact sc23_safe P _
  · exact issued_trusted _ claim23 SC23.St.confs _ P.users U (sc23_conf_step P)
      (fun _ _ _ hp => hp.2.2) hU SC23.init rfl ops

/-- an injected principal 7 delivers a tool result and forges the user's confirmation (as user 1) -/
def forged23 : List (ℕ × SC23.Op) := [(7, .toolResult 0 66), (7, .confirm 1 7 5 [66]), (7, .act 5 [0] 7)]

/-- **Necessity (SC-23).** Without authentication the tainted sensitive action runs; with it nothing runs. -/
theorem forged23_acts_without_auth :
    (authRun (SC23.step P0 full) (fun _ => none) SC23.init forged23).executed = [⟨5, [66], true, some 7⟩] ∧
    (authRun (SC23.step P0 full) claim23 SC23.init forged23).executed = [] := by
  decide

end SC23

/-! ## SC-12: admin sessions -/

section SC12
open ControlStack.SC12

def claim12 : SC12.Op → Option ℕ
  | .start c _ => some c
  | .endSession c _ => some c
  | .halt c => some c
  | .spawn _ _ _ _ => none
  | .bypass _ _ _ => none
  | .fire _ => none

theorem sc12_active_step (admins : List ℕ) (s : SC12.St) (o : SC12.Op) (x : ℕ)
    (hx : x ∈ (SC12.step admins full s o).active) :
    x ∈ s.active ∨ ∃ c, claim12 o = some c ∧ (o = .start c x ∧ c ∈ admins) := by
  cases o <;> simp only [SC12.step] at hx <;> (repeat' split at hx) <;> simp_all [claim12]
  all_goals (try (rcases hx with hx | rfl <;> simp_all))

/-- **SC-12 with authenticated issuers.** Every live entity's origin session was started by an admin. -/
theorem sc12_safe_authenticated (admins : List ℕ) (U : List ℕ) (ops : List (ℕ × SC12.Op))
    (hU : ∀ u ∈ U, u ∉ admins) :
    Good (authRun (SC12.step admins full) claim12 SC12.init ops) ∧
    (∀ e ∈ (authRun (SC12.step admins full) claim12 SC12.init ops).live, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .start c e.origin ∧ c ∈ admins)) := by
  have hg : Good (authRun (SC12.step admins full) claim12 SC12.init ops) := by
    rw [authRun_eq]; exact sc12_safe admins _
  refine ⟨hg, fun e he => ?_⟩
  exact issued_trusted _ claim12 SC12.St.active _ admins U (sc12_active_step admins)
    (fun _ _ _ hp => hp.2) hU SC12.init rfl ops e.origin (hg e he).2.1

/-- agent 1 forges an admin session start (as admin 9) -/
def forged12 : List (ℕ × SC12.Op) := [(1, .start 9 5), (1, .spawn 5 6 true 0)]

/-- **Necessity (SC-12).** Without authentication the agent gets a registered live session and helper; with it
nothing is live. -/
theorem forged12_spawns_without_auth :
    (authRun (SC12.step [9] full) (fun _ => none) SC12.init forged12).live.length = 2 ∧
    (authRun (SC12.step [9] full) claim12 SC12.init forged12).live = [] := by
  decide

end SC12

/-! ## SC-18: admin sink configuration -/

section SC18
open ControlStack.SC18

def claim18 : SC18.Op → Option ℕ
  | .setSink c _ => some c
  | .halt c => some c
  | .request _ => none
  | .logWrite _ => none
  | .release _ => none
  | .sinkDown => none
  | .sinkRestore => none
  | .tick => none

/-- **SC-18 with authenticated issuers.** The configuration premise is needed only for operations issued outside
the adversary set U; forged admin claims never apply. -/
theorem sc18_safe_authenticated (admins : List ℕ) (trusted T : ℕ) (U : List ℕ) (ops : List (ℕ × SC18.Op))
    (hU : ∀ u ∈ U, u ∉ admins) (htrusted : ∀ io ∈ ops, io.1 ∉ U → SC18.legal admins trusted io.2) :
    Good T (authRun (SC18.step admins trusted T full) claim18 (SC18.init trusted) ops) := by
  rw [authRun_eq]
  refine sc18_safe admins trusted T _ (fun o ho => ?_)
  cases o with
  | setSink c v =>
    intro hc
    have hiss := claim_issued_by claim18 ops _ c ho rfl
    exact htrusted _ hiss (fun hu => hU c hu hc) hc
  | _ => trivial

/-- agent 1 forges the admin's sink change (as admin 9) to an untrusted sink 66 -/
def forged18 : List (ℕ × SC18.Op) := [(1, .setSink 9 66)]

/-- **Necessity (SC-18).** Without authentication the sink is redirected; with it the trusted sink stays. -/
theorem forged18_redirects_without_auth :
    (authRun (SC18.step [9] 0 5 full) (fun _ => none) (SC18.init 0) forged18).cfg = 66 ∧
    (authRun (SC18.step [9] 0 5 full) claim18 (SC18.init 0) forged18).cfg = 0 := by
  decide

end SC18

end ControlStack.AuthInstances

#print axioms ControlStack.AuthInstances.sc15_safe_authenticated
#print axioms ControlStack.AuthInstances.forged15_merges_without_auth
#print axioms ControlStack.AuthInstances.sc20_safe_authenticated
#print axioms ControlStack.AuthInstances.forged20_trains_without_auth
#print axioms ControlStack.AuthInstances.sc23_safe_authenticated
#print axioms ControlStack.AuthInstances.forged23_acts_without_auth
#print axioms ControlStack.AuthInstances.sc12_safe_authenticated
#print axioms ControlStack.AuthInstances.forged12_spawns_without_auth
#print axioms ControlStack.AuthInstances.sc18_safe_authenticated
#print axioms ControlStack.AuthInstances.forged18_redirects_without_auth
