import ControlStack.Scenarios.SC05Signal

namespace ControlStack.SC05

-- Bool represents the secret bit; Fin 65536 represents the output alphabet.
-- The two functions induce point-mass encoder and decoder rows.
def Back_cap_does_not_prevent : Prop :=
  ∃ (send : Bool → Fin 65536) (decode : Fin 65536 → Bool),
    ControlStack.CovertNoGo.successView
      (fun t : Fin 65536 => t)
      (fun m t => if t = send m then (1 : ℝ) else 0)
      (fun t m => if decode t = m then (1 : ℝ) else 0) = 1

end ControlStack.SC05
