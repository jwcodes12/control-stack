-- EXCERPT of ControlStack/Scenarios/SC26LossyHalt.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC26LossyHalt

open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness.Concrete
open ControlStack.SC26LossyLiveness



/-- the lossy machine with a configurable recovery (v2: `rch = false` ignores HALT) -/
def stepLH (R : Roles) (cap : ℕ) (rch : Bool) (s : CSt) : LOp → CSt
  | .base o => stepC R cap rch s o
  | o => stepL R cap true s o

def runLH (R : Roles) (cap : ℕ) (rch : Bool) (s : CSt) (ops : List LOp) : CSt := ops.foldl (stepLH R cap rch) s

/-- the lossy machine plus a tagged copy of the wire: (transmission id, message) -/
structure TSt where
  c : CSt
  tw : List (ℕ × (ℕ × Tx))
  fresh : ℕ
deriving DecidableEq, Repr

/-- fresh ids for newly transmitted messages -/
def tagNew (fresh : ℕ) (l : List (ℕ × Tx)) : List (ℕ × (ℕ × Tx)) := l.mapIdx fun i m => (fresh + i, m)

def stepT (R : Roles) (cap : ℕ) (st : TSt) : LOp → TSt
  | .base o =>
    let c' := stepC R cap true st.c o
    let nw := c'.wire.drop st.c.wire.length
    ⟨c', st.tw ++ tagNew st.fresh nw, st.fresh + nw.length⟩
  | .drop j => ⟨stepL R cap true st.c (.drop j), st.tw.eraseIdx j, st.fresh⟩
  | .dup j =>
    ⟨stepL R cap true st.c (.dup j),
      match st.tw[j]? with
      | none => st.tw
      | some e => st.tw ++ [e], st.fresh⟩
  | .deliverAt j => ⟨stepL R cap true st.c (.deliverAt j), st.tw, st.fresh⟩

def runT (R : Roles) (cap : ℕ) (st : TSt) (ops : List LOp) : TSt := ops.foldl (stepT R cap) st

def tinit : TSt := ⟨cinit, [], 0⟩

/-- the tagged invariant: the tags shadow the wire exactly, and all ids are below `fresh` -/
structure TInv (st : TSt) : Prop where
  shadow : st.c.wire = st.tw.map Prod.snd
  below : ∀ e ∈ st.tw, e.1 < st.fresh

/-- id t names message m: every copy with id t carries m, and t is already allocated -/
def TagIs (st : TSt) (t : ℕ) (m : ℕ × Tx) : Prop := (∀ e ∈ st.tw, e.1 = t → e.2 = m) ∧ t < st.fresh

/-- the copies (with their fresh ids) transmitted by one gate step -/
def batch (R : Roles) (cap : ℕ) (st : TSt) (o : LOp) : List (ℕ × (ℕ × Tx)) :=
  (stepT R cap st o).tw.drop st.tw.length

/-- the tagged copy with id t is DELIVERED within `mid`: the bank processes the in-flight copy at an index holding
id t (so not every copy of it has been dropped). Other messages may be dropped before. -/
def DeliveredIn (R : Roles) (cap : ℕ) (st : TSt) (t : ℕ) (mid : List LOp) : Prop :=
  ∃ nd j rest, mid = nd ++ .deliverAt j :: rest ∧ ((runT R cap st nd).tw[j]?).map Prod.fst = some t

/-- round r's tagged k-copy is delivered (from the round's starting state st0) -/
def DeliversT (R : Roles) (cap : ℕ) (k : ℕ) (st0 : TSt) (r : List LOp × List LOp) : Prop :=
  ∃ e ∈ batch R cap (runT R cap st0 r.1) (.base .recover), e.2.1 = k ∧
    DeliveredIn R cap (stepT R cap (runT R cap st0 r.1) (.base .recover)) e.1 r.2

/-- the logged state, tagged (empty wire) -/
def tLogged : TSt := ⟨loggedState, [], 0⟩

/-- a round: the gate transmits (copy id 0), then retransmits (copy id 1); the network drops copy 0 and delivers
copy 1 -/
def pcRound : List LOp × List LOp := ([.base (.transmit 0)], [.drop 0, .deliverAt 0])

end ControlStack.SC26LossyHalt

