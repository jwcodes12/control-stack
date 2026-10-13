namespace ControlStack.SC26

-- The nonce and haltCheck flags are unrestricted by Sound.
def Back_safe_of_sound : Prop :=
  ∀ (R : Roles) (cap : ℕ) (C : Checks) (ops : List Op),
    Sound C →
    (∀ o ∈ ops, legal R o) →
    Good R cap (run R cap C init ops)

end ControlStack.SC26
