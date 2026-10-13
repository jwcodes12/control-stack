-- EXCERPT of ControlStack/GatewayModel.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.GatewayModel

open ControlStack.Covert

/-- raw sender actions: a send attempt with an arbitrary payload, or any other action (denied) -/
inductive Act (R : Type) where
  | send : R → Act R
  | other : Act R
  deriving DecidableEq, Fintype

/-- gateway state: accepted values (in order) and whether the episode has been blanked -/
structure St (S : Type) where
  buf : List S
  blanked : Bool

/-- one gateway step -/
def step {R S : Type} (valid : R → Option S) (slots : ℕ) (st : St S) : Act R → St S
  | .other => { st with blanked := true }
  | .send r =>
    match valid r with
    | none => { st with blanked := true }
    | some v => if st.buf.length < slots then { st with buf := st.buf ++ [v] } else { st with blanked := true }

/-- run a whole trace from the empty state -/
def run {R S : Type} (valid : R → Option S) (slots : ℕ) (tr : List (Act R)) : St S :=
  tr.foldl (step valid slots) ⟨[], false⟩

/-- what the receiver sees -/
def deliver {S : Type} (slots : ℕ) (st : St S) : Fin slots → Option S :=
  fun i => if st.blanked then none else st.buf[i.val]?

/-- pushforward of a trace law to a view law -/
noncomputable def push {T V : Type} [Fintype T] [DecidableEq V] (f : T → V) (p : T → ℝ) : V → ℝ :=
  fun v => ∑ t, if f t = v then p t else 0

/-- reachable views: a prefix of j accepted values (j ≤ slots), the rest NULL -/
abbrev Prefix (S : Type) (slots : ℕ) := (j : Fin (slots + 1)) × (Fin j → S)

def toPrefix {S : Type} (slots : ℕ) (st : St S) (h : st.buf.length ≤ slots) : Prefix S slots :=
  if hb : st.blanked then ⟨0, fun i => i.elim0⟩
  else ⟨⟨st.buf.length, by omega⟩, fun i => st.buf.get ⟨i.val, i.isLt⟩⟩

def embedPrefix {S : Type} (slots : ℕ) (p : Prefix S slots) : Fin slots → Option S :=
  fun i => if h : i.val < p.1.val then some (p.2 ⟨i.val, h⟩) else none

end ControlStack.GatewayModel

