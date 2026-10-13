namespace PL_bg1n3_7
open ControlStack.SC07Refinement

def FrozenBack : Prop :=
  ∀ (K : CCfg) (ops : List COp) (w : ℕ),
    K.quotaRule = true →
    0 < K.Q →
    wireIn (runC K cinit ops).fwd w < K.Q

def BackAt (K : CCfg) (ops : List COp) (w : ℕ) : Prop :=
  wireIn (runC K cinit ops).fwd w < K.Q

def OriginalAt (K : CCfg) (ops : List COp) (w : ℕ) : Prop :=
  wireIn (runC K cinit ops).fwd w < K.Q

def Claim : Prop :=
  (FrozenBack ↔ ∀ (K : CCfg) (ops : List COp) (w : ℕ), K.quotaRule = true → 0 < K.Q → BackAt K ops w) ∧
  (∀ (K : CCfg) (ops : List COp) (w : ℕ), K.quotaRule = true → 0 < K.Q → (BackAt K ops w ↔ OriginalAt K ops w))

def Witness : Prop :=
  (K0 true).quotaRule = true ∧ 0 < (K0 true).Q ∧ wireIn (runC (K0 true) cinit [.pkt 1 8080 4 1, .resetQuota, .pkt 1 8080 4 1]).fwd 0 = 5 ∧ wireIn (runC (K0 true) cinit [.pkt 1 8080 4 1, .resetQuota, .pkt 1 8080 4 1]).fwd 1 = 5

end PL_bg1n3_7
