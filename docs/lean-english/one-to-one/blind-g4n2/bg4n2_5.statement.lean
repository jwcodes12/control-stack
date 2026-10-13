namespace ControlStack.AuthInstances

-- U is the adversary's issuer set, represented by a predicate on principal ids.
def Back_sc19_safe_authenticated : Prop :=
  ∀ (E : ControlStack.SC19.Env) (U : ℕ → Prop)
      (ops : List (ℕ × ControlStack.SC19.Op)),
    (∀ c : ℕ, U c → c ∉ E.approvers) →
    (∀ c : ℕ, U c → c ∉ E.verifiers) →
    let s := ControlStack.AuthenticatedLog.authRun
      (ControlStack.SC19.step E ControlStack.SC19.full)
      claim19 ControlStack.SC19.init ops
    ControlStack.SC19.Good E s ∧
    (∀ a ∈ s.approvals,
      (a.2.1, ControlStack.SC19.Op.approve a.2.1 a.1) ∈ ops ∧
      a.2.1 ∈ E.approvers ∧ ¬ U a.2.1) ∧
    (∀ i ∈ s.verified,
      ∃ c : ℕ,
        (c, ControlStack.SC19.Op.verify c i) ∈ ops ∧
        c ∈ E.verifiers ∧ ¬ U c)

end ControlStack.AuthInstances

namespace PL_bg4n2_5
open ControlStack.SC19 ControlStack.AuthInstances ControlStack.AuthenticatedLog
def BackPoint (E : Env) (U : ℕ → Prop) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good E s ∧
  (∀ a ∈ s.approvals,
    (a.2.1, Op.approve a.2.1 a.1) ∈ ops ∧ a.2.1 ∈ E.approvers ∧ ¬ U a.2.1) ∧
  (∀ i ∈ s.verified, ∃ c, (c, Op.verify c i) ∈ ops ∧ c ∈ E.verifiers ∧ ¬ U c)
def OrigPredicatePoint (E : Env) (U : ℕ → Prop) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good E s ∧
  (∀ a ∈ s.approvals, ∃ c o, (c, o) ∈ ops ∧ ¬ U c ∧
    (o = Op.approve c a.1 ∧ c = a.2.1 ∧ c ∈ E.approvers)) ∧
  (∀ i ∈ s.verified, ∃ c o, (c, o) ∈ ops ∧ ¬ U c ∧ (o = Op.verify c i ∧ c ∈ E.verifiers))
def OrigPoint (E : Env) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good E s ∧
  (∀ a ∈ s.approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
    (o = Op.approve c a.1 ∧ c = a.2.1 ∧ c ∈ E.approvers)) ∧
  (∀ i ∈ s.verified, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = Op.verify c i ∧ c ∈ E.verifiers))
def Claim : Prop :=
  (∀ E U ops s, BackPoint E U ops s ↔ OrigPredicatePoint E U ops s) ∧
  (∀ E (U : List ℕ) ops s, BackPoint E (fun c => c ∈ U) ops s ↔ OrigPoint E U ops s) ∧
  (∀ E (U : ℕ → Prop) ops, ∃ V : List ℕ,
    (∀ c ∈ V, U c) ∧ (∀ s, BackPoint E U ops s ↔ OrigPoint E V ops s))
def Witness : Prop :=
  let ops : List (ℕ × Op) := [(1, .write 7 5), (1, .snapshot 7), (3, .verify 3 0),
    (1, .prepare 1 0 7), (2, .approve 2 0), (1, .commit 0 0)]
  let s := authRun (step E0 full) claim19 init ops
  (∀ c ∈ ([1] : List ℕ), c ∉ E0.approvers) ∧
  (∀ c ∈ ([1] : List ℕ), c ∉ E0.verifiers) ∧
  s.destroyed = [⟨0, 1, 7, 1, 5, 0⟩] ∧ s.approvals = [(0, 2, 1)] ∧ s.verified = [0]

end PL_bg4n2_5
