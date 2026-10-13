namespace PL_bg6n3_4
open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness ControlStack.SC26Liveness.Concrete ControlStack.SC26LossyLiveness ControlStack.SC26LossyHalt

def Back_lossy_rounds : Prop :=
  ∀ (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
    (rounds : List (List LOp × List LOp)),
    (∀ o ∈ ops₀, legalL R o) →
    let start := runL R cap true cinit ops₀
    (∃ d ∈ start.delivery, d.id = k) →
    (∀ o ∈ (rounds.map roundOps).flatten, legalL R o) →
    (∃ r ∈ rounds, Delivers k r) →
    let final := runL R cap true start (rounds.map roundOps).flatten
    final.halted = false →
    k ∈ final.bank.map Prod.fst ∧
      ∀ (continuation : List LOp),
        (∀ o ∈ continuation, legalL R o) →
        ((runL R cap true final continuation).bank.map Prod.fst).count k = 1


def BackLegal (R : Roles) (rounds : List (List LOp × List LOp)) : Prop :=
  ∀ o ∈ (rounds.map roundOps).flatten, legalL R o
def OrigLegal (R : Roles) (rounds : List (List LOp × List LOp)) : Prop :=
  ∀ r ∈ rounds, ∀ o ∈ r.1 ++ r.2, legalL R o
def BackFair (k : ℕ) (rounds : List (List LOp × List LOp)) : Prop :=
  ∃ r ∈ rounds, Delivers k r
def OrigFair (k : ℕ) (rounds : List (List LOp × List LOp)) : Prop :=
  ∃ j, ∃ hj : j < rounds.length, Delivers k rounds[j]

def BackAt (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
    (rounds : List (List LOp × List LOp)) (post : List LOp) : Prop :=
  let start := runL R cap true cinit ops₀
  let final := runL R cap true start (rounds.map roundOps).flatten
  k ∈ final.bank.map Prod.fst ∧ ((runL R cap true final post).bank.map Prod.fst).count k = 1

def OrigAt (R : Roles) (cap k : ℕ) (ops0 : List LOp)
    (rounds : List (List LOp × List LOp)) (post : List LOp) : Prop :=
  k ∈ (runL R cap true (runL R cap true cinit ops0) (rounds.map roundOps).flatten).bank.map Prod.fst ∧
    ((runL R cap true (runL R cap true cinit ops0) ((rounds.map roundOps).flatten ++ post)).bank.map Prod.fst).count k = 1

def Pointwise : Prop :=
  (∀ R rounds, BackLegal R rounds ↔ OrigLegal R rounds) ∧
  (∀ k rounds, BackFair k rounds ↔ OrigFair k rounds) ∧
  (∀ (R : Roles) (cap k : ℕ) (ops₀ : List LOp) (d : DRow)
      (rounds : List (List LOp × List LOp)) (post : List LOp),
    (∀ o ∈ ops₀, legalL R o) → d ∈ (runL R cap true cinit ops₀).delivery → d.id = k →
    BackLegal R rounds → (∀ o ∈ post, legalL R o) → BackFair k rounds →
    (runL R cap true (runL R cap true cinit ops₀) (rounds.map roundOps).flatten).halted = false →
    (BackAt R cap k ops₀ rounds post ↔ OrigAt R cap k ops₀ rounds post))

def rounds : List (List LOp × List LOp) := [([], [.base (.bankProcess 0)])]
def Witness : Prop :=
  (∀ o ∈ setupOps, legalL R0 o) ∧
  ⟨0, wTx, false⟩ ∈ (runL R0 10 true cinit setupOps).delivery ∧
  BackLegal R0 rounds ∧ BackFair 0 rounds ∧
  (runL R0 10 true (runL R0 10 true cinit setupOps) (rounds.map roundOps).flatten).halted = false ∧
  (∀ o ∈ ([.dup 0, .deliverAt 0] : List LOp), legalL R0 o) ∧
  BackAt R0 10 0 setupOps rounds [.dup 0, .deliverAt 0]

def BackOutcome (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
    (rounds : List (List LOp × List LOp)) : Prop :=
  let start := runL R cap true cinit ops₀
  let final := runL R cap true start (rounds.map roundOps).flatten
  k ∈ final.bank.map Prod.fst ∧ ∀ post : List LOp, (∀ o ∈ post, legalL R o) → ((runL R cap true final post).bank.map Prod.fst).count k = 1

def OriginalSignature : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops0 : List LOp) (hops0 : ∀ o ∈ ops0, legalL R o)
    (k : ℕ) (d : DRow) (hd : d ∈ (runL R cap true cinit ops0).delivery) (hk : d.id = k)
    (rounds : List (List LOp × List LOp)) (post : List LOp)
    (hleg : ∀ r ∈ rounds, ∀ o ∈ r.1 ++ r.2, legalL R o) (hpost : ∀ o ∈ post, legalL R o)
    (hfair : ∃ j, ∃ hj : j < rounds.length, Delivers k rounds[j])
    (hh : (runL R cap true (runL R cap true cinit ops0) (rounds.map roundOps).flatten).halted = false),
    k ∈ (runL R cap true (runL R cap true cinit ops0) (rounds.map roundOps).flatten).bank.map Prod.fst ∧
      ((runL R cap true (runL R cap true cinit ops0) ((rounds.map roundOps).flatten ++ post)).bank.map
        Prod.fst).count k = 1

def BackShape : Prop := Back_lossy_rounds ↔

  ∀ (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
    (rounds : List (List LOp × List LOp)),
    (∀ o ∈ ops₀, legalL R o) →
    let start := runL R cap true cinit ops₀
    (∃ d ∈ start.delivery, d.id = k) →
    (∀ o ∈ (rounds.map roundOps).flatten, legalL R o) →
    (∃ r ∈ rounds, Delivers k r) →
    let final := runL R cap true start (rounds.map roundOps).flatten
    final.halted = false →
    BackOutcome R cap k ops₀ rounds

def OriginalShape : Prop := OriginalSignature ↔
  ∀ (R : Roles) (cap : ℕ) (ops0 : List LOp) (hops0 : ∀ o ∈ ops0, legalL R o)
    (k : ℕ) (d : DRow) (hd : d ∈ (runL R cap true cinit ops0).delivery) (hk : d.id = k)
    (rounds : List (List LOp × List LOp)) (post : List LOp)
    (hleg : ∀ r ∈ rounds, ∀ o ∈ r.1 ++ r.2, legalL R o) (hpost : ∀ o ∈ post, legalL R o)
    (hfair : ∃ j, ∃ hj : j < rounds.length, Delivers k rounds[j])
    (hh : (runL R cap true (runL R cap true cinit ops0) (rounds.map roundOps).flatten).halted = false), OrigAt R cap k ops0 rounds post

def Projection : Prop := ∀ R cap k ops₀ rounds,
  BackOutcome R cap k ops₀ rounds ↔
    ∀ post, (∀ o ∈ post, legalL R o) → BackAt R cap k ops₀ rounds post

def Claim : Prop := Pointwise ∧ BackShape ∧ OriginalShape ∧ Projection

end PL_bg6n3_4
