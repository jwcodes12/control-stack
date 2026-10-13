import ControlStack.Scenarios.SC09Priv

namespace ControlStack.SC09

-- NOTE
-- AMBIGUOUS: "sub-collection" could mean membership inclusion, multiset
-- inclusion (counting repeated capabilities), or an order-preserving
-- sublist. This statement uses membership inclusion: every capability
-- held by a newly appearing process was held by the parent.
def Back_spawn_attenuates : Prop :=
  ∀ (P : Policy) (s : St) (p ch : ℕ) (q : Proc) (keep : List ℕ),
    s.halted = false →
    procOf s p = some q →
    procOf s ch = none →
    ∀ r ∈ (step P full s (.spawn p ch keep)).procs,
      r ∉ s.procs →
      r.lin = q.lin ∧ (∀ c ∈ r.caps, c ∈ q.caps)

end ControlStack.SC09
