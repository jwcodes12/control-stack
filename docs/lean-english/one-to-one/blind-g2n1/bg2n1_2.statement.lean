namespace PL_bg2n1_2
open ControlStack.SC08

-- NOTE
-- AMBIGUOUS: "The same safety statement" could carry over claim 1's
-- initially false halted flag, whereas "with no runs" imposes no condition
-- on that flag. This statement follows the latter reading and quantifies
-- the initial halted flag freely; the initial run list is empty.
def Back_safe_of_sound : Prop :=
  ∀ (E : Env) (C : Checks) (files : List (ℕ × ℕ))
    (halted : Bool) (ops : List Op),
    Sound C → Good E (run E C (⟨files, [], halted⟩ : St) ops)

def EnglishOk (E : Env) (s : St) : Prop :=
  ∀ r ∈ s.ran, E.h r.1 ∈ E.allow ∧
    (E.h r.1 ∈ E.interp → ∃ sc, r.2 = some sc ∧ E.h sc ∈ E.scripts)
def BackAt (E : Env) (C : Checks) (files : List (ℕ × ℕ))
    (halted : Bool) (ops : List Op) : Prop :=
  Good E (run E C (⟨files, [], halted⟩ : St) ops)
def OrigAt (E : Env) (C : Checks) (files : List (ℕ × ℕ)) (ops : List Op) : Prop :=
  Good E (run E C ⟨files, [], false⟩ ops)
def OrigFamily : Prop := ∀ E C files ops, Sound C → OrigAt E C files ops
-- Domain comparison is independent of the truth of the safety conclusion.
def BackDomain (C : Checks) (_halted : Bool) : Prop := Sound C
def OrigDomain (C : Checks) (halted : Bool) : Prop := Sound C ∧ halted = false
def BackCoverage (Q : Checks → Bool → Prop) : Prop :=
  ∀ C halted, BackDomain C halted → Q C halted
def OrigCoverage (Q : Checks → Bool → Prop) : Prop :=
  ∀ C halted, OrigDomain C halted → Q C halted
def Claim : Prop :=
  (Back_safe_of_sound = (∀ E C files halted ops, Sound C → BackAt E C files halted ops)) ∧
  (Back_safe_of_sound → OrigFamily) ∧
  (∀ E C files halted ops, Sound C → halted = false →
    (BackAt E C files halted ops ↔ OrigAt E C files ops)) ∧
  (∀ C halted, OrigDomain C halted → BackDomain C halted) ∧
  (∃ C halted, BackDomain C halted ∧ ¬ OrigDomain C halted) ∧
  (∀ Q, BackCoverage Q → OrigCoverage Q) ∧
  (¬ (∀ Q, OrigCoverage Q → BackCoverage Q)) ∧
  (∀ E s, EnglishOk E s ↔ Good E s)
def Witness : Prop :=
  Sound full ∧ s0.ran = [] ∧ s0.halted = false ∧
  (run E0 full s0 [.exec 1 none, .exec 4 (some 5)]).ran =
    [(10, none), (20, some 30)] ∧
  BackDomain full true ∧ ¬ OrigDomain full true ∧
  (run E0 full (⟨s0.files, [], true⟩ : St) [.exec 1 none]).ran = []

end PL_bg2n1_2
