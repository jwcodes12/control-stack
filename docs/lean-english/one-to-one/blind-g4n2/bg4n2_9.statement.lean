namespace ControlStack.AuthInstances

-- U is the adversary's issuer set, represented by a predicate on principal ids.
def Back_sc20_safe_authenticated : Prop :=
  ∀ (E : ControlStack.SC20.Env) (U : ℕ → Prop)
      (ops : List (ℕ × ControlStack.SC20.Op)),
    (∀ c : ℕ, U c → c ∉ E.reviewers) →
    let s := ControlStack.AuthenticatedLog.authRun
      (ControlStack.SC20.step E ControlStack.SC20.full)
      claim20 ControlStack.SC20.init ops
    ControlStack.SC20.Good E s ∧
    (∀ p ∈ s.promoted,
      (p.2.1, ControlStack.SC20.Op.promote p.2.1 p.1) ∈ ops ∧
      p.2.1 ∈ E.reviewers ∧ ¬ U p.2.1)

end ControlStack.AuthInstances

namespace PL_bg4n2_9
open ControlStack.SC20 ControlStack.AuthInstances ControlStack.AuthenticatedLog
def BackPoint (E : Env) (U : ℕ → Prop) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good E s ∧ (∀ p ∈ s.promoted,
    (p.2.1, Op.promote p.2.1 p.1) ∈ ops ∧ p.2.1 ∈ E.reviewers ∧ ¬ U p.2.1)
def OrigPredicatePoint (E : Env) (U : ℕ → Prop) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good E s ∧ (∀ p ∈ s.promoted, ∃ c o, (c, o) ∈ ops ∧ ¬ U c ∧
    (o = Op.promote c p.1 ∧ c = p.2.1 ∧ c ∈ E.reviewers))
def OrigPoint (E : Env) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good E s ∧ (∀ p ∈ s.promoted, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
    (o = Op.promote c p.1 ∧ c = p.2.1 ∧ c ∈ E.reviewers))
def Claim : Prop :=
  (∀ E U ops s, BackPoint E U ops s ↔ OrigPredicatePoint E U ops s) ∧
  (∀ E (U : List ℕ) ops s, BackPoint E (fun c => c ∈ U) ops s ↔ OrigPoint E U ops s) ∧
  (∀ E (U : ℕ → Prop) ops, ∃ V : List ℕ,
    (∀ c ∈ V, U c) ∧ (∀ s, BackPoint E U ops s ↔ OrigPoint E V ops s))
def Witness : Prop :=
  let ops : List (ℕ × Op) := [(1, .agentWrite 1 1 66), (2, .promote 2 1), (9, .freeze 9 [1]), (1, .train)]
  let s := authRun (step E0 full) claim20 init ops
  (∀ c ∈ ([1] : List ℕ), c ∉ E0.reviewers) ∧ s.trained = [[(1, 66)]] ∧ s.promoted = [(1, 2, 66)]

end PL_bg4n2_9
