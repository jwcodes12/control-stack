-- EXCERPT of ControlStack/Core/CheckedTrace.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.CheckedTrace

universe u v
variable {S : Type u} {O : Type v}

/-- One full-state transition receipt; the externally attested link from real
effects to these values remains an explicit, unproved premise. -/
structure Receipt (S : Type u) (O : Type v) where
  before : S
  op : O
  after : S

def events (rs : List (Receipt S O)) : List O := rs.map Receipt.op

def recordedEnd (s : S) : List (Receipt S O) → S
  | [] => s
  | r :: rs => recordedEnd r.after rs

/-- Fail closed: replay each step under the formal policy, checking BOTH its
reported predecessor and successor. A forged/omitted real-world effect can
still evade this checker if the trusted observation premise fails. -/
def verified [DecidableEq S] (step : S → O → S) : S → List (Receipt S O) → Bool
  | _, [] => true
  | s, r :: rs =>
      decide (r.before = s ∧ r.after = step s r.op) &&
        verified step r.after rs

abbrev SC04Alphabet (templates fields levels : ℕ) :=
  Fin templates × (Fin fields → Fin levels)

end ControlStack.CheckedTrace

