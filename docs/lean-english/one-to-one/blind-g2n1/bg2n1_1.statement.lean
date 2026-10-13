namespace PL_bg2n1_1
open ControlStack.SC08

def Back_sc08_safe : Prop :=
  ∀ (E : Env) (files : List (ℕ × ℕ)) (ops : List Op),
    Good E (run E full (⟨files, [], false⟩ : St) ops)

def EnglishOk (E : Env) (s : St) : Prop :=
  ∀ r ∈ s.ran, E.h r.1 ∈ E.allow ∧
    (E.h r.1 ∈ E.interp → ∃ sc, r.2 = some sc ∧ E.h sc ∈ E.scripts)
def BackAt (E : Env) (files : List (ℕ × ℕ)) (ops : List Op) : Prop :=
  Good E (run E full (⟨files, [], false⟩ : St) ops)
def OrigAt (E : Env) (files : List (ℕ × ℕ)) (ops : List Op) : Prop :=
  Good E (run E full ⟨files, [], false⟩ ops)
def Claim : Prop :=
  (Back_sc08_safe = (∀ E files ops, BackAt E files ops)) ∧
  (∀ E files ops, BackAt E files ops ↔ OrigAt E files ops) ∧
  (∀ E s, EnglishOk E s ↔ Good E s)
def Witness : Prop :=
  (s0.ran = [] ∧ s0.halted = false) ∧
  (run E0 full s0 [.exec 1 none, .exec 4 (some 5)]).ran =
    [(10, none), (20, some 30)] ∧
  (run { E0 with interp := [] } full s0 [.write 2 777, .exec 4 (some 2)]).ran =
    [(20, none)]

end PL_bg2n1_1
