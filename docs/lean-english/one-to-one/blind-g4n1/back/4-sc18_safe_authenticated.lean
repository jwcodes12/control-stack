namespace ControlStack.AuthInstances

-- NOTE:
-- U is represented by its membership predicate. As stipulated in the English,
-- the first component of each operation pair is interpreted as its true issuer.
-- NOT_FORMALISABLE: The excerpts have no independent ground-truth issuer or
-- predicate relating platform-reported identity to ground truth. This statement
-- captures the modelled conclusion under that external authenticity assumption;
-- it cannot express or establish the platform's fidelity to real issuers.
def Back_sc18_safe_authenticated : Prop :=
  ∀ (admins : List ℕ) (trusted T : ℕ) (U : ℕ → Prop)
    (ops : List (ℕ × ControlStack.SC18.Op)),
    (∀ a : ℕ, U a → a ∉ admins) →
    (∀ io ∈ ops, ¬ U io.1 → ControlStack.SC18.legal admins trusted io.2) →
    ControlStack.SC18.Good T
      (ControlStack.AuthenticatedLog.authRun
        (ControlStack.SC18.step admins trusted T ControlStack.SC18.full)
        claim18 (ControlStack.SC18.init trusted) ops)

end ControlStack.AuthInstances
