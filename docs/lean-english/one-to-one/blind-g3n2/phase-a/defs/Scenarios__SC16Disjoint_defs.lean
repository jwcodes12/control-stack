-- EXCERPT of ControlStack/Scenarios/SC16Disjoint.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC16Disjoint

open ControlStack.SC16

/-- overlapping roles: agent 2 is also a reviewer -/
def Rov : Roles := ⟨[1, 2], [2], [3], [4]⟩

end ControlStack.SC16Disjoint

