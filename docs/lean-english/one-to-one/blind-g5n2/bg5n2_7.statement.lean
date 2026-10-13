namespace PL_bg5n2_7
open ControlStack ControlStack.AuthInstances ControlStack.AuthenticatedLog
def Back_sc23_safe_authenticated : Prop :=
  ∀ (P : SC23.Policy) (U : List ℕ),
    (∀ u ∈ U, u ∉ P.users) →
      ∀ (ops : List (ℕ × SC23.Op)),
        let s := authRun (SC23.step P SC23.full) claim23 SC23.init ops
        SC23.Good P s ∧
          ∀ cf ∈ s.confs,
            ∃ c : ℕ, c ∈ P.users ∧ c ∉ U ∧ c = cf.by_ ∧
              (c, SC23.Op.confirm c cf.n cf.tool cf.vals) ∈ ops

def BackAt (P : SC23.Policy) (U : List ℕ) (ops : List (ℕ × SC23.Op)) : Prop :=
  let s := authRun (SC23.step P SC23.full) claim23 SC23.init ops
  SC23.Good P s ∧ ∀ cf ∈ s.confs,
    ∃ c : ℕ, c ∈ P.users ∧ c ∉ U ∧ c = cf.by_ ∧
      (c, SC23.Op.confirm c cf.n cf.tool cf.vals) ∈ ops
def OrigAt (P : SC23.Policy) (U : List ℕ) (ops : List (ℕ × SC23.Op)) : Prop :=
  let s := authRun (SC23.step P SC23.full) claim23 SC23.init ops
  SC23.Good P s ∧ ∀ cf ∈ s.confs, ∃ c o, (c,o) ∈ ops ∧ c ∉ U ∧
    (o = SC23.Op.confirm c cf.n cf.tool cf.vals ∧ c = cf.by_ ∧ c ∈ P.users)
def Claim : Prop :=
  (Back_sc23_safe_authenticated = (∀ (P : SC23.Policy) (U : List ℕ),
    (∀ u ∈ U, u ∉ P.users) → ∀ ops, BackAt P U ops)) ∧
  (∀ (P : SC23.Policy) (U : List ℕ) (ops : List (ℕ × SC23.Op)),
    (∀ u ∈ U, u ∉ P.users) → (BackAt P U ops ↔ OrigAt P U ops))
def Witness : Prop :=
  (∀ u ∈ ([7] : List ℕ), u ∉ SC23.P0.users) ∧
  (authRun (SC23.step SC23.P0 SC23.full) claim23 SC23.init
    [(7,.toolResult 0 66),(1,.confirm 1 7 5 [66]),(7,.act 5 [0] 7)]).executed = [⟨5,[66],true,some 7⟩]
end PL_bg5n2_7
