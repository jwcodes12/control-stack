import ControlStack.Deployment.GuardNecessity
import ControlStack.Deployment.Provenance

/-!
Which of the 21 `TrustedBroker.Allowed` clauses are redundant *in the model*?

For every clause k (numbered as in `GuardNecessity.AllowedExcept`):
* **redundant on reachable states**: on every state reachable from `initial cap` by
  guarded broker steps, the other 20 clauses already imply clause k;
* **independent on reachable states**: some reachable state, request, approval and
  lease satisfy the other 20 clauses but not clause k (witnesses in
  `GuardMinimalityWitnesses`).

This is a statement about the Lean model only. Redundant on reachable states does
NOT mean the runtime check can be deleted: the implications use the model's
provenance invariants (`intact` equals `artifacts`, retained approvals reference
existing leases, reviews and artifacts), which hold because `Step` is guarded.
The live broker re-checks them against the filesystem and the database, where
external tampering is possible. Property-relative necessity (`GuardNecessity`)
is a different, complementary notion.
-/
namespace ControlStack.Deployment.GuardMinimality
open ControlStack
open ControlStack.TrustedBroker
open ControlStack.Deployment
open ControlStack.Deployment.GuardNecessity
open ControlStack.Deployment.Provenance

/-- `intact` is the staging mirror of `artifacts`: only `stage` writes either. -/
def StageInv (s : State) : Prop := ∀ d, s.intact d = s.artifacts d

/-- Everything the redundancy proofs use about a reachable state. -/
def ReachInv (R : Roles) (s : State) : Prop :=
  Coherent s ∧ ReviewProvenance R s ∧ ApprovalProvenance R s ∧ StageInv s

theorem reachInv_initial (R : Roles) (cap : Nat) : ReachInv R (initial cap) :=
  ⟨initial_coherent cap, initial_review R cap, initial_approval R cap,
    by intro d; simp [initial]⟩

theorem stageInv_step (R : Roles) {s t : State} (h : StageInv s)
    (step : Step R s t) : StageInv t := by
  cases step with
  | stage uid digest live role =>
      intro d
      by_cases hd : d = digest <;> simp [put, hd, h d]
  | release now r a l allowed => intro d; simpa [committed] using h d
  | deny => exact h
  | review => intro d; simpa using h d
  | issue => intro d; simpa using h d
  | approve => intro d; simpa using h d
  | revoke => intro d; simpa using h d
  | halt => intro d; simpa using h d

theorem reachInv_step (R : Roles) {s t : State} (h : ReachInv R s)
    (step : Step R s t) : ReachInv R t :=
  ⟨transaction_coherent R s t h.1 step, review_step R s t h.2.1 step,
    approval_step R s t h.2.1 h.2.2.1 step, stageInv_step R h.2.2.2 step⟩

theorem reachInv_trace (R : Roles) (cap : Nat) {s : State}
    (tr : Trace R (initial cap) s) : ReachInv R s := by
  have key : ∀ {a b : State}, Trace R a b → ReachInv R a → ReachInv R b := by
    intro a b t
    induction t with
    | nil => exact id
    | cons step _ ih => exact fun h => ih (reachInv_step R h step)
  exact key tr (reachInv_initial R cap)

/-- The clause deleted by `AllowedExcept k`. -/
def Clause (k : Nat) (R : Roles) (s : State) (now : Nat) (r : Request)
    (a : Approval) (l : Lease) : Prop :=
  match k with
  | 0 => s.halted = false
  | 1 => R.agent r.uid
  | 2 => s.approvals r.nonce = some a
  | 3 => a.used = false
  | 4 => a.digest = r.digest
  | 5 => a.destination = r.destination
  | 6 => a.agent = r.uid
  | 7 => a.lease = r.lease
  | 8 => R.approver a.signer
  | 9 => now < a.expires
  | 10 => s.leases r.lease = some l
  | 11 => l.agent = r.uid
  | 12 => l.revoked = false
  | 13 => now < l.expires
  | 14 => 0 < r.cost
  | 15 => l.used + r.cost ≤ l.budget
  | 16 => s.spent + r.cost ≤ s.cap
  | 17 => s.artifacts r.digest = true
  | 18 => s.intact r.digest = true
  | 19 => ∃ reviewer, s.reviews r.digest = some reviewer
  | 20 => r.nonce ∉ s.consumed
  | _ => True

/-- The other 20 clauses plus the deleted one are exactly `Allowed`. -/
theorem allowed_of_except_clause (k : Nat) (hk : k < 21) (R : Roles) (s : State)
    (now : Nat) (r : Request) (a : Approval) (l : Lease)
    (h : AllowedExcept k R s now r a l) (c : Clause k R s now r a l) :
    Allowed R s now r a l := by
  interval_cases k <;> simp_all [AllowedExcept, Clause, Allowed]

theorem allowed_clause (R : Roles) (s : State) (now : Nat) (r : Request)
    (a : Approval) (l : Lease) (k : Nat) (hk : k < 21)
    (h : Allowed R s now r a l) : Clause k R s now r a l := by
  interval_cases k <;> simp_all [Clause, Allowed]

theorem allowed_except (R : Roles) (s : State) (now : Nat) (r : Request)
    (a : Approval) (l : Lease) (k : Nat) (h : Allowed R s now r a l) :
    AllowedExcept k R s now r a l := by
  simp_all [Allowed, AllowedExcept]

/-- Redundancy of clause 1 (`caller_is_agent`): the approval's agent is an agent
and equals the caller. -/
theorem clause1_redundant {R : Roles} {s : State} {r : Request}
    {a : Approval} (inv : ReachInv R s)
    (h2 : s.approvals r.nonce = some a) (h6 : a.agent = r.uid) : R.agent r.uid := by
  obtain ⟨_, ag, _⟩ := inv.2.2.1 r.nonce a h2
  rwa [← h6]

theorem clause3_redundant {R : Roles} {s : State} {r : Request} {a : Approval}
    (inv : ReachInv R s) (h2 : s.approvals r.nonce = some a)
    (h20 : r.nonce ∉ s.consumed) : a.used = false := by
  by_contra used
  have hu : a.used = true := by simpa using used
  exact h20 ((inv.1 r.nonce).mpr ⟨a, h2, hu⟩)

theorem clause20_redundant {R : Roles} {s : State} {r : Request} {a : Approval}
    (inv : ReachInv R s) (h2 : s.approvals r.nonce = some a)
    (h3 : a.used = false) : r.nonce ∉ s.consumed :=
  nonce_history_redundant s inv.1 r.nonce a h2 h3

theorem clause8_redundant {R : Roles} {s : State} {r : Request} {a : Approval}
    (inv : ReachInv R s) (h2 : s.approvals r.nonce = some a) : R.approver a.signer :=
  (inv.2.2.1 r.nonce a h2).1

/-- The approval's lease is the request's lease and exists in the state, so the
stored lease equals `l`, and its agent is the approval's agent. -/
theorem lease_agent_eq {R : Roles} {s : State} {r : Request} {a : Approval}
    {l : Lease} (inv : ReachInv R s) (h2 : s.approvals r.nonce = some a)
    (h7 : a.lease = r.lease) (h10 : s.leases r.lease = some l) :
    l.agent = a.agent := by
  obtain ⟨_, _, _, _, v, hv, owner⟩ := inv.2.2.1 r.nonce a h2
  rw [h7, h10] at hv
  have : l = v := Option.some.inj hv
  subst this
  exact owner

theorem clause6_redundant {R : Roles} {s : State} {r : Request} {a : Approval}
    {l : Lease} (inv : ReachInv R s) (h2 : s.approvals r.nonce = some a)
    (h7 : a.lease = r.lease) (h10 : s.leases r.lease = some l)
    (h11 : l.agent = r.uid) : a.agent = r.uid := by
  rw [← lease_agent_eq inv h2 h7 h10]; exact h11

theorem clause11_redundant {R : Roles} {s : State} {r : Request} {a : Approval}
    {l : Lease} (inv : ReachInv R s) (h2 : s.approvals r.nonce = some a)
    (h7 : a.lease = r.lease) (h10 : s.leases r.lease = some l)
    (h6 : a.agent = r.uid) : l.agent = r.uid := by
  rw [lease_agent_eq inv h2 h7 h10]; exact h6

theorem clause17_redundant {R : Roles} {s : State} {r : Request} {a : Approval}
    (inv : ReachInv R s) (h2 : s.approvals r.nonce = some a)
    (h4 : a.digest = r.digest) : s.artifacts r.digest = true := by
  obtain ⟨_, _, art, _⟩ := inv.2.2.1 r.nonce a h2
  rwa [h4] at art

theorem clause18_redundant {R : Roles} {s : State} {r : Request}
    (inv : ReachInv R s) (h17 : s.artifacts r.digest = true) :
    s.intact r.digest = true := by
  rw [inv.2.2.2 r.digest]; exact h17

theorem clause19_redundant {R : Roles} {s : State} {r : Request} {a : Approval}
    (inv : ReachInv R s) (h2 : s.approvals r.nonce = some a)
    (h4 : a.digest = r.digest) : ∃ reviewer, s.reviews r.digest = some reviewer := by
  obtain ⟨_, _, _, ⟨reviewer, rv, _⟩, _⟩ := inv.2.2.1 r.nonce a h2
  exact ⟨reviewer, by rwa [h4] at rv⟩

/-- On reachable states each of these nine clauses is implied by the other twenty. -/
theorem reachable_redundant (R : Roles) (s : State) (now : Nat) (r : Request)
    (a : Approval) (l : Lease) (inv : ReachInv R s) (k : Nat)
    (hk : k = 1 ∨ k = 3 ∨ k = 6 ∨ k = 8 ∨ k = 11 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20)
    (h : AllowedExcept k R s now r a l) : Allowed R s now r a l := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact allowed_of_except_clause 1 (by decide) R s now r a l h
      (clause1_redundant (a := a) inv (by simp_all [AllowedExcept]) (by simp_all [AllowedExcept]))
  · exact allowed_of_except_clause 3 (by decide) R s now r a l h
      (clause3_redundant (a := a) (r := r) inv (by simp_all [AllowedExcept]) (by simp_all [AllowedExcept]))
  · exact allowed_of_except_clause 6 (by decide) R s now r a l h
      (clause6_redundant (a := a) (l := l) inv (by simp_all [AllowedExcept]) (by simp_all [AllowedExcept])
        (by simp_all [AllowedExcept]) (by simp_all [AllowedExcept]))
  · exact allowed_of_except_clause 8 (by decide) R s now r a l h
      (clause8_redundant (a := a) (r := r) inv (by simp_all [AllowedExcept]))
  · exact allowed_of_except_clause 11 (by decide) R s now r a l h
      (clause11_redundant (a := a) (l := l) inv (by simp_all [AllowedExcept]) (by simp_all [AllowedExcept])
        (by simp_all [AllowedExcept]) (by simp_all [AllowedExcept]))
  · exact allowed_of_except_clause 17 (by decide) R s now r a l h
      (clause17_redundant (a := a) inv (by simp_all [AllowedExcept]) (by simp_all [AllowedExcept]))
  · exact allowed_of_except_clause 18 (by decide) R s now r a l h
      (clause18_redundant inv (by simp_all [AllowedExcept]))
  · exact allowed_of_except_clause 19 (by decide) R s now r a l h
      (clause19_redundant (a := a) inv (by simp_all [AllowedExcept]) (by simp_all [AllowedExcept]))
  · exact allowed_of_except_clause 20 (by decide) R s now r a l h
      (clause20_redundant (a := a) inv (by simp_all [AllowedExcept]) (by simp_all [AllowedExcept]))

#print axioms reachInv_trace
#print axioms allowed_of_except_clause
#print axioms reachable_redundant
end ControlStack.Deployment.GuardMinimality
