import ControlStack.Deployment.GuardMinimality

/-!
Reachable-state independence witnesses for twelve of the 21 `Allowed` clauses:
0, 2, 4, 5, 7, 9, 10, 12, 13, 14, 15, 16. In each, the state is reached from
`initial cap` by guarded broker steps, the other twenty clauses hold, and the
named clause fails. Model witnesses only (no live broker).
-/
namespace ControlStack.Deployment.GuardMinimalityWitnesses
open ControlStack
open ControlStack.TrustedBroker
open ControlStack.Deployment
open ControlStack.Deployment.GuardNecessity
open ControlStack.Deployment.GuardMinimality

abbrev R : Roles := Witnesses.R

def lse (budget lexp : Nat) : Lease := ⟨23701, budget, 0, lexp, false⟩
def apv (aexp : Nat) : Approval := ⟨23, 1, 23701, 9, 23704, aexp, false⟩
def rq (dest cost : Nat) : Request := ⟨23701, 7, 23, dest, 9, cost⟩

def m1 (cap : Nat) : State :=
  { initial cap with artifacts := put (initial cap).artifacts 23 true,
                     intact := put (initial cap).intact 23 true }
def m2 (cap : Nat) : State := { m1 cap with reviews := put (m1 cap).reviews 23 (some 23703) }
def m3 (cap budget lexp : Nat) : State :=
  { m2 cap with leases := put (m2 cap).leases 9 (some (lse budget lexp)) }
/-- Staged, reviewed, leased and approved; nothing released. -/
def m4 (cap budget lexp aexp : Nat) : State :=
  { m3 cap budget lexp with approvals := put (m3 cap budget lexp).approvals 7 (some (apv aexp)) }

theorem m4_reach (cap budget lexp aexp : Nat) (hb : 0 < budget) (hl : 0 < lexp)
    (ha : 0 < aexp) : Trace R (initial cap) (m4 cap budget lexp aexp) := by
  refine Trace.cons (t := m1 cap) (.stage _ 23701 23 rfl (.inl rfl)) ?_
  refine Trace.cons (t := m2 cap)
    (.review _ 23703 23 rfl rfl (by simp [m1, put])) ?_
  refine Trace.cons (t := m3 cap budget lexp)
    (.issue _ 23700 9 (lse budget lexp) 0 rfl rfl (.inl rfl)
      (by simp [m2, m1, put, initial]) hb rfl rfl hl) ?_
  refine Trace.cons (t := m4 cap budget lexp aexp)
    (.approve _ 23704 7 (apv aexp) (lse budget lexp) 0 23703 rfl rfl rfl (.inl rfl)
      (by simp [m3, m2, m1, put, initial]) rfl
      (by simp [m3, m2, m1, put, apv]) rfl (by decide)
      (by simp [m3, put, apv]) rfl rfl hl ha) ?_
  exact Trace.nil _

/-- Clause k is not implied by the other twenty on a reachable state. -/
def Independent (k : Nat) : Prop :=
  ∃ (cap : Nat) (s : State) (now : Nat) (r : Request) (a : Approval) (l : Lease),
    Trace R (initial cap) s ∧ AllowedExcept k R s now r a l ∧ ¬ Allowed R s now r a l

theorem independent_of_clause {k : Nat} (hk : k < 21) {cap : Nat} {s : State}
    {now : Nat} {r : Request} {a : Approval} {l : Lease}
    (tr : Trace R (initial cap) s) (h : AllowedExcept k R s now r a l)
    (bad : ¬ Clause k R s now r a l) : Independent k :=
  ⟨cap, s, now, r, a, l, tr, h, fun hA => bad (allowed_clause R s now r a l k hk hA)⟩

set_option maxRecDepth 4000

/-- 14 `positive_cost`: a zero-cost release. -/
theorem independent_14 : Independent 14 :=
  independent_of_clause (by decide) (m4_reach 1 1 1000 1000 (by decide) (by decide) (by decide))
    (now := 0) (r := rq 1 0) (a := apv 1000) (l := lse 1 1000)
    (by simp [AllowedExcept, m4, m3, m2, m1, rq, apv, lse, R, Witnesses.R, put, initial])
    (by simp [Clause, rq])

/-- 5 `same_destination`. -/
theorem independent_5 : Independent 5 :=
  independent_of_clause (by decide) (m4_reach 1 1 1000 1000 (by decide) (by decide) (by decide))
    (now := 0) (r := rq 2 1) (a := apv 1000) (l := lse 1 1000)
    (by simp [AllowedExcept, m4, m3, m2, m1, rq, apv, lse, R, Witnesses.R, put, initial])
    (by simp [Clause, rq, apv])

/-- 15 `within_lease_budget`: cap 2, lease budget 1, cost 2. -/
theorem independent_15 : Independent 15 :=
  independent_of_clause (by decide) (m4_reach 2 1 1000 1000 (by decide) (by decide) (by decide))
    (now := 0) (r := rq 1 2) (a := apv 1000) (l := lse 1 1000)
    (by simp [AllowedExcept, m4, m3, m2, m1, rq, apv, lse, R, Witnesses.R, put, initial])
    (by simp [Clause, rq, lse])

/-- 16 `within_joint_budget`: cap 1, lease budget 2, cost 2. -/
theorem independent_16 : Independent 16 :=
  independent_of_clause (by decide) (m4_reach 1 2 1000 1000 (by decide) (by decide) (by decide))
    (now := 0) (r := rq 1 2) (a := apv 1000) (l := lse 2 1000)
    (by simp [AllowedExcept, m4, m3, m2, m1, rq, apv, lse, R, Witnesses.R, put, initial])
    (by simp [Clause, rq, m4, m3, m2, m1, initial])

/-- 9 `approval_unexpired`: now after the approval but before the lease expires. -/
theorem independent_9 : Independent 9 :=
  independent_of_clause (by decide) (m4_reach 1 1 2000 1000 (by decide) (by decide) (by decide))
    (now := 1500) (r := rq 1 1) (a := apv 1000) (l := lse 1 2000)
    (by simp [AllowedExcept, m4, m3, m2, m1, rq, apv, lse, R, Witnesses.R, put, initial])
    (by simp [Clause, apv])

/-- 13 `lease_unexpired`: now after the lease but before the approval expires. -/
theorem independent_13 : Independent 13 :=
  independent_of_clause (by decide) (m4_reach 1 1 1000 2000 (by decide) (by decide) (by decide))
    (now := 1500) (r := rq 1 1) (a := apv 2000) (l := lse 1 1000)
    (by simp [AllowedExcept, m4, m3, m2, m1, rq, apv, lse, R, Witnesses.R, put, initial])
    (by simp [Clause, lse])

/-- 10 `stored_lease`: the lease handed to the guard is not the stored one. -/
theorem independent_10 : Independent 10 :=
  independent_of_clause (by decide) (m4_reach 1 1 1000 1000 (by decide) (by decide) (by decide))
    (now := 0) (r := rq 1 1) (a := apv 1000) (l := lse 1 1001)
    (by simp [AllowedExcept, m4, m3, m2, m1, rq, apv, lse, R, Witnesses.R, put, initial])
    (by simp [Clause, rq, m4, m3, m2, m1, lse, put, initial])

/-- 2 `stored_approval`: the approval handed to the guard is not the stored one. -/
theorem independent_2 : Independent 2 :=
  independent_of_clause (by decide) (m4_reach 1 1 1000 1000 (by decide) (by decide) (by decide))
    (now := 0) (r := rq 1 1) (a := apv 1001) (l := lse 1 1000)
    (by simp [AllowedExcept, m4, m3, m2, m1, rq, apv, lse, R, Witnesses.R, put, initial])
    (by simp [Clause, rq, m4, m3, m2, m1, apv, put, initial])

theorem trace_snoc {s t u : State} (h : Trace R s t) (st : Step R t u) : Trace R s u := by
  induction h with
  | nil => exact Trace.cons st (Trace.nil _)
  | cons step _ ih => exact Trace.cons step (ih st)

/-- 0 `not_halted`: HALT after approval (a guarded `halt` step). -/
def h0 : State := { m4 1 1 1000 1000 with halted := true }
theorem independent_0 : Independent 0 :=
  independent_of_clause (by decide)
    (trace_snoc (m4_reach 1 1 1000 1000 (by decide) (by decide) (by decide))
      (Step.halt (m4 1 1 1000 1000) 23700 rfl) : Trace R (initial 1) h0)
    (now := 0) (r := rq 1 1) (a := apv 1000) (l := lse 1 1000)
    (by simp [AllowedExcept, h0, m4, m3, m2, m1, rq, apv, lse, R, Witnesses.R, put, initial])
    (by simp [Clause, h0])

/-- 12 `lease_active`: the lease is revoked after the approval (a guarded `revoke`). -/
def rv : State :=
  { m4 1 1 1000 1000 with
    leases := put (m4 1 1 1000 1000).leases 9 (some { lse 1 1000 with revoked := true }) }
theorem independent_12 : Independent 12 :=
  independent_of_clause (by decide)
    (trace_snoc (m4_reach 1 1 1000 1000 (by decide) (by decide) (by decide))
      (Step.revoke (m4 1 1 1000 1000) 23700 9 (lse 1 1000) rfl rfl
        (by simp [m4, m3, put])) : Trace R (initial 1) rv)
    (now := 0) (r := rq 1 1) (a := apv 1000) (l := { lse 1 1000 with revoked := true })
    (by simp [AllowedExcept, rv, m4, m3, m2, m1, rq, apv, lse, R, Witnesses.R, put, initial])
    (by simp [Clause])

/-- 4 `same_digest`: a second staged and reviewed digest 24, approval for 23. -/
def d6 : State :=
  { m4 1 1 1000 1000 with artifacts := put (m4 1 1 1000 1000).artifacts 24 true,
                          intact := put (m4 1 1 1000 1000).intact 24 true }
def d7 : State := { d6 with reviews := put d6.reviews 24 (some 23703) }
theorem independent_4 : Independent 4 :=
  independent_of_clause (by decide)
    (trace_snoc
      (trace_snoc (m4_reach 1 1 1000 1000 (by decide) (by decide) (by decide))
        (Step.stage (m4 1 1 1000 1000) 23701 24 rfl (.inl rfl)) : Trace R (initial 1) d6)
      (Step.review d6 23703 24 rfl rfl (by simp [d6, put])) : Trace R (initial 1) d7)
    (now := 0) (r := ⟨23701, 7, 24, 1, 9, 1⟩) (a := apv 1000) (l := lse 1 1000)
    (by simp [AllowedExcept, d7, d6, m4, m3, m2, m1, apv, lse, R, Witnesses.R, put, initial])
    (by simp [Clause, apv])

/-- 7 `same_lease`: the agent owns a second lease (key 10); the approval names lease 9. -/
def l2 : State :=
  { m4 1 1 1000 1000 with leases := put (m4 1 1 1000 1000).leases 10 (some (lse 1 1000)) }
theorem independent_7 : Independent 7 :=
  independent_of_clause (by decide)
    (trace_snoc (m4_reach 1 1 1000 1000 (by decide) (by decide) (by decide))
      (Step.issue (m4 1 1 1000 1000) 23700 10 (lse 1 1000) 0 rfl rfl (.inl rfl)
        (by simp [m4, m3, m2, m1, put, initial]) (by decide) rfl rfl (by decide))
      : Trace R (initial 1) l2)
    (now := 0) (r := ⟨23701, 7, 23, 1, 10, 1⟩) (a := apv 1000) (l := lse 1 1000)
    (by simp [AllowedExcept, l2, m4, m3, m2, m1, apv, lse, R, Witnesses.R, put, initial])
    (by simp [Clause, apv])

/-- The twelve clauses with reachable independence witnesses. -/
theorem reachable_independent (k : Nat)
    (hk : k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 10 ∨ k = 12 ∨
      k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16) : Independent k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [independent_0, independent_2, independent_4, independent_5, independent_7,
    independent_9, independent_10, independent_12, independent_13, independent_14,
    independent_15, independent_16]

/-- The two classes are disjoint: a clause redundant on reachable states cannot
have a reachable independence witness. -/
theorem redundant_not_independent (k : Nat)
    (hk : k = 1 ∨ k = 3 ∨ k = 6 ∨ k = 8 ∨ k = 11 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20) :
    ¬ Independent k := by
  rintro ⟨cap, s, now, r, a, l, tr, h, bad⟩
  exact bad (reachable_redundant R s now r a l (reachInv_trace R cap tr) k hk h)

/-- Every clause is in one of the two classes (nine redundant, twelve independent);
`redundant_not_independent` says no clause is in both. -/
theorem guard_classification (k : Nat) (hk : k < 21) :
    (k = 1 ∨ k = 3 ∨ k = 6 ∨ k = 8 ∨ k = 11 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20) ∨
    (k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 10 ∨ k = 12 ∨
      k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16) := by
  omega

#print axioms reachable_independent
#print axioms redundant_not_independent
#print axioms guard_classification
end ControlStack.Deployment.GuardMinimalityWitnesses
