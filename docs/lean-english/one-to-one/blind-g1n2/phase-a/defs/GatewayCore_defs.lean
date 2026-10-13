-- EXCERPT of ControlStack/GatewayCore.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.GatewayCore

open ControlStack.Covert ControlStack.GatewayModel

inductive Ev (C : ℕ) (R : Type) where
  | send : Option (Fin C) → R → Ev C R
  | other : Ev C R
  | close : Ev C R

variable {C : ℕ} {R : Type} {S : Fin C → Type} {slots : Fin C → ℕ}

abbrev View (S : Fin C → Type) (slots : Fin C → ℕ) := (c : Fin C) → Fin (slots c) → Option (S c)

structure GSt (S : Fin C → Type) (slots : Fin C → ℕ) where
  buf : (c : Fin C) → List (S c)
  blanked : Bool
  snap : Option (View S slots)

/-- channel c's single-channel state -/
def chan (st : GSt S slots) (c : Fin C) : St (S c) := ⟨st.buf c, st.blanked⟩

/-- the view a close would deliver now -/
def viewOf (st : GSt S slots) : View S slots := fun c => deliver (slots c) (chan st c)

def gstep (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (e : Ev C R) : GSt S slots :=
  match st.snap with
  | some _ => st
  | none =>
    match e with
    | .other => { st with blanked := true }
    | .close => { st with snap := some (viewOf st) }
    | .send none _ => { st with blanked := true }
    | .send (some c) r =>
      if (st.buf c).length < slots c then
        match valid c r with
        | none => { st with blanked := true }
        | some v => { st with buf := Function.update st.buf c (st.buf c ++ [v]) }
      else { st with blanked := true }

def init : GSt S slots := ⟨fun _ => [], false, none⟩

def runG (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (tr : List (Ev C R)) : GSt S slots :=
  tr.foldl (gstep valid) st

/-- what the receiver gets: the snapshot, or the harness's close at the end of the trace -/
def finalView (st : GSt S slots) : View S slots := st.snap.getD (viewOf st)



/-- the all-NULL view -/
def nullView : View S slots := fun _ _ => none

/-- prefix tuples: per channel, j ≤ slots c accepted values -/
abbrev Prefixes (S : Fin C → Type) (slots : Fin C → ℕ) := (c : Fin C) → Prefix (S c) (slots c)

def embedAll (p : Prefixes S slots) : View S slots := fun c => embedPrefix (slots c) (p c)

/-- the Python `view_space_size`: ∏_c Σ_{j ≤ slots c} |S c|^j -/
def viewSpace (slots : Fin C → ℕ) (sz : Fin C → ℕ) : ℕ := ∏ c, ∑ j ∈ Finset.range (slots c + 1), sz c ^ j

def Inv (st : GSt S slots) : Prop :=
  (∀ c, (st.buf c).length ≤ slots c) ∧ ∀ v, st.snap = some v → v ∈ Set.range (embedAll (S := S) (slots := slots))

end ControlStack.GatewayCore

