namespace ControlStack.SC07Liveness

def Back_exfil_needs_windows : Prop :=
  ∀ (E : Env) (ops : List Op) (S : ℕ),
    0 < E.q →
    S ≤ total (run E full init ops) →
    ControlStack.SC07Exfil.ceilDiv S E.q ≤
      (run E full init ops).window + 1

end ControlStack.SC07Liveness
