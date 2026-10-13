import ControlStack.Scenarios.SC07Refinement

namespace ControlStack.SC07Refinement

-- NOTE
-- AMBIGUOUS: The English refers to the "same model-correspondence assumptions
-- as concrete_safe", but those assumptions are not specified in the permitted
-- excerpts. Best effort: the concrete model's runs start at cinit, and the only
-- configuration hypotheses below are quotaRule = true and 0 < Q. Additional
-- formal correspondence hypotheses, if intended, cannot be reconstructed here.
def Back_concrete_wire_lt : Prop :=
  ∀ (K : CCfg) (ops : List COp) (w : ℕ),
    K.quotaRule = true →
    0 < K.Q →
    wireIn (runC K cinit ops).fwd w < K.Q

end ControlStack.SC07Refinement
