namespace PL_bg1a_9
open ControlStack.SC07Refinement

def Back_concrete_safe : Prop :=
  ∀ (K : CCfg) (ops : List COp),
    K.quotaRule = true →
    let s := runC K cinit ops
    (∀ r ∈ s.fwd, (r.ip, r.port) ∈ K.allow) ∧
      (∀ w : ℕ, payloadIn s.fwd w ≤ K.Q - 1)


def BackAt (K : CCfg) (ops : List COp) : Prop :=
  (∀ r ∈ (runC K cinit ops).fwd, (r.ip, r.port) ∈ K.allow) ∧ (∀ w : ℕ, payloadIn (runC K cinit ops).fwd w ≤ K.Q - 1)
def OrigAt (K : CCfg) (ops : List COp) : Prop :=
  (∀ r ∈ (runC K cinit ops).fwd, (r.ip, r.port) ∈ K.allow) ∧ (∀ w : ℕ, payloadIn (runC K cinit ops).fwd w ≤ K.Q - 1)

def Claim : Prop :=
  (Back_concrete_safe = (∀ (K : CCfg) (ops : List COp) (_hK : K.quotaRule = true), BackAt K ops)) ∧
  (∀ (K : CCfg) (ops : List COp) (_hK : K.quotaRule = true), BackAt K ops ↔ OrigAt K ops)

def Witness : Prop :=
  (K0 true).quotaRule = true ∧
  let s := runC (K0 true) cinit [.pkt 1 8080 4 1, .pkt 1 8080 4 1, .pkt 1 8080 1 0, .pkt 2 8080 1 0]
  payloadIn s.fwd 0 = 4 ∧ wireIn s.fwd 0 = 5 ∧ s.quotaDrop = 2 ∧ s.denyDrop = 1
end PL_bg1a_9
