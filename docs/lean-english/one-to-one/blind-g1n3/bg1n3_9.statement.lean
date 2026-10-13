namespace PL_bg1n3_9
open ControlStack.SC07Refinement

def FrozenBack : Prop :=
  ∀ (K : CCfg) (ops : List COp) (w sink tolerance : ℕ),
    K.quotaRule = true →
    sink ≤ payloadIn (runC K cinit ops).fwd w →
    sink ≤ K.Q - 1 ∧ sink ≤ K.Q + tolerance

def BackAt (K : CCfg) (ops : List COp) (w sink tolerance : ℕ) : Prop :=
  sink ≤ K.Q - 1 ∧ sink ≤ K.Q + tolerance

def OriginalAt (K : CCfg) (ops : List COp) (w sink tolerance : ℕ) : Prop :=
  sink ≤ K.Q - 1 ∧ sink ≤ K.Q + tolerance

def Claim : Prop :=
  (FrozenBack ↔ ∀ (K : CCfg) (ops : List COp) (w sink tolerance : ℕ), K.quotaRule = true → sink ≤ payloadIn (runC K cinit ops).fwd w → BackAt K ops w sink tolerance) ∧
  (∀ (K : CCfg) (ops : List COp) (w sink tolerance : ℕ), K.quotaRule = true → sink ≤ payloadIn (runC K cinit ops).fwd w → (BackAt K ops w sink tolerance ↔ OriginalAt K ops w sink tolerance))

def Witness : Prop :=
  (K0 true).quotaRule = true ∧ 0 < (4 : ℕ) ∧ 4 ≤ payloadIn (runC (K0 true) cinit [.pkt 1 8080 4 1]).fwd 0 ∧ 4 ≤ (K0 true).Q - 1 ∧ 4 ≤ (K0 true).Q + 1500

end PL_bg1n3_9
