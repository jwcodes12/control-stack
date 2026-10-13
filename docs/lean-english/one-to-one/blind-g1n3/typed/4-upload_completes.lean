import ControlStack.Scenarios.SC07Liveness

namespace ControlStack.SC07Liveness

def Back_upload_completes : Prop :=
  ∀ (E : Env) (s : St) (d : ℕ) (chunks : List ℕ),
    s.halted = false →
    d ∈ E.allow →
    s.used + chunks.sum ≤ E.q →
    (run E full s (chunks.map (fun n => Op.send d n))).log =
      s.log ++ chunks.map (fun n => (⟨d, n, s.window⟩ : Fwd))

end ControlStack.SC07Liveness
