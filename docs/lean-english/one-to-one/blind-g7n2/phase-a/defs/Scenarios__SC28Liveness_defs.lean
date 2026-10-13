-- EXCERPT of ControlStack/Scenarios/SC28Liveness.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC28Liveness

open ControlStack.SC28

variable (admins : List ℕ) (G : ℕ)

/-- the charges of honest work units -/
def charges (as : List ℕ) : ℕ := (as.map (fun a => charge full a a)).sum

end ControlStack.SC28Liveness

