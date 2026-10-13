namespace PL_bg1n3_8
open ControlStack.SC07Refinement

def FrozenBack : Prop :=
  ∀ (K : CCfg) (pre post : List COp),
    K.quotaRule = true →
    (runC K cinit pre).halted = true →
    (runC K cinit (pre ++ post)).fwd =
      (runC K cinit pre).fwd

def BackAt (K : CCfg) (pre post : List COp) : Prop :=
  (runC K cinit (pre ++ post)).fwd = (runC K cinit pre).fwd

def OriginalAt (K : CCfg) (pre post : List COp) : Prop :=
  (runC K cinit (pre ++ post)).fwd = (runC K cinit pre).fwd

def Claim : Prop :=
  (FrozenBack ↔ ∀ (K : CCfg) (pre post : List COp), K.quotaRule = true → (runC K cinit pre).halted = true → BackAt K pre post) ∧
  (∀ (K : CCfg) (pre post : List COp), K.quotaRule = true → (runC K cinit pre).halted = true → (BackAt K pre post ↔ OriginalAt K pre post))

def Witness : Prop :=
  (K0 true).quotaRule = true ∧ (runC (K0 true) cinit [.pkt 1 8080 2 1, .halt]).halted = true ∧ (runC (K0 true) cinit [.pkt 1 8080 2 1, .halt]).fwd = [⟨1, 8080, 2, 3, 0⟩] ∧ (runC (K0 true) cinit [.pkt 1 8080 2 1, .halt, .resetQuota, .pkt 1 8080 2 1]).fwd = [⟨1, 8080, 2, 3, 0⟩]

end PL_bg1n3_8
