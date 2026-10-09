/-
SC-16 with disjoint roles: closes review finding 7 (REVIEW-PACKET-2026-10-09.md §0.7).

`SC16.sc16_safe` and `SC16.sc16_reviewed_content` say every deployed content was reviewed by a reviewer id that is
not the content's stager id. Roles may overlap, so that reviewer can itself be an agent (review witness W4). This file
adds the SC-26-style disjoint variant:

- `sc16_safe_disjoint`: if no reviewer and no approver is an agent, and the hash is injective on the contents in play
  (the premise of `sc16_reviewed_content`), every deployed content was reviewed by a NON-AGENT reviewer (other than its
  stager) and deployed under an approval by a NON-AGENT approver for exactly its target;
- `overlap_reviewer_is_agent`: necessity. With overlapping roles (agent 2 is also a reviewer), content staged by agent
  1 deploys and every review of it is by an agent.

Not claimed: the ids are authenticated (that is the separate credential-separation premise; see
`Core/Authenticated.lean`). No new mathematics: a corollary of the SC-16 theorems.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC16Deploy

namespace ControlStack.SC16Disjoint

open ControlStack.SC16

/-- **SC-16 with disjoint roles.** Adversary class TRACE_ARBITRARY over SC-16 (any operations, caller ids, contents). -/
theorem sc16_safe_disjoint (R : Roles) (h : ℕ → ℕ) (ops : List Op)
    (hrev : ∀ a ∈ R.reviewers, a ∉ R.agents) (happ : ∀ a ∈ R.approvers, a ∉ R.agents)
    (hinj : Set.InjOn h {c | (∃ e ∈ (run R h full init ops).deployed, e.content = c) ∨
      ∃ rv ∈ (run R h full init ops).reviews, rv.content = c}) :
    ∀ e ∈ (run R h full init ops).deployed,
      (∃ rv ∈ (run R h full init ops).reviews, rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧
        rv.reviewer ∉ R.agents ∧ rv.reviewer ≠ rv.stager) ∧
      (∃ ap ∈ (run R h full init ops).approvals, ap.n = e.n ∧ ap.target = e.target ∧ ap.approver ∈ R.approvers ∧
        ap.approver ∉ R.agents) := by
  intro e he
  refine ⟨?_, ?_⟩
  · obtain ⟨rv, hrv, hc, hr, hs⟩ := sc16_reviewed_content R h ops hinj e he
    exact ⟨rv, hrv, hc, hr, hrev _ hr, hs⟩
  · obtain ⟨ap, hap, hn, ht, ha, -⟩ := (sc16_safe R h ops).1 e he
    exact ⟨ap, hap, hn, ht, ha, happ _ ha⟩

/-- overlapping roles: agent 2 is also a reviewer -/
def Rov : Roles := ⟨[1, 2], [2], [3], [4]⟩

/-- **Necessity (review witness W4).** With overlapping roles, content staged by agent 1 and reviewed by agent 2
deploys, and every review in the run is by an agent. -/
theorem overlap_reviewer_is_agent :
    let s := run Rov id full init [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]
    s.deployed = [⟨0, 5, 7⟩] ∧ s.reviews ≠ [] ∧ ∀ rv ∈ s.reviews, rv.reviewer ∈ Rov.agents := by
  decide

end ControlStack.SC16Disjoint
