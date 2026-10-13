namespace PL_bg6n3_6
open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness ControlStack.SC26Liveness.Concrete ControlStack.SC26LossyLiveness ControlStack.SC26LossyHalt

def Back_tagged_rounds : Prop :=
  ∀ (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
    (rounds : List (List LOp × List LOp)),
    (∀ o ∈ ops₀, legalL R o) →
    let start := runT R cap tinit ops₀
    (∀ o ∈ (rounds.map roundOps).flatten, legalL R o) →
    (∃ (before : List (List LOp × List LOp))
        (r : List LOp × List LOp) (after : List (List LOp × List LOp)),
      rounds = before ++ r :: after ∧
        DeliversT R cap k (runT R cap start (before.map roundOps).flatten) r) →
    let final := runT R cap start (rounds.map roundOps).flatten
    k ∈ final.c.bank.map Prod.fst ∧
      ∀ (continuation : List LOp),
        (∀ o ∈ continuation, legalL R o) →
        ((runT R cap final continuation).c.bank.map Prod.fst).count k = 1


def BackLegal (R : Roles) (rounds : List (List LOp × List LOp)) : Prop :=
  ∀ o ∈ (rounds.map roundOps).flatten, legalL R o
def OrigLegal (R : Roles) (rounds : List (List LOp × List LOp)) : Prop :=
  ∀ r ∈ rounds, ∀ o ∈ r.1 ++ r.2, legalL R o
def BackFair (R : Roles) (cap k : ℕ) (start : TSt)
    (rounds : List (List LOp × List LOp)) : Prop :=
  ∃ (before : List (List LOp × List LOp)) (r : List LOp × List LOp)
    (after : List (List LOp × List LOp)),
    rounds = before ++ r :: after ∧
      DeliversT R cap k (runT R cap start (before.map roundOps).flatten) r

def OrigFair (R : Roles) (cap k : ℕ) (start : TSt)
    (rounds : List (List LOp × List LOp)) : Prop :=
  ∃ j, ∃ hj : j < rounds.length,
    DeliversT R cap k (runT R cap start ((rounds.take j).map roundOps).flatten) rounds[j]

def BackAt (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
    (rounds : List (List LOp × List LOp)) (post : List LOp) : Prop :=
  let start := runT R cap tinit ops₀
  let final := runT R cap start (rounds.map roundOps).flatten
  k ∈ final.c.bank.map Prod.fst ∧ ((runT R cap final post).c.bank.map Prod.fst).count k = 1

def OrigAt (R : Roles) (cap k : ℕ) (ops0 : List LOp)
    (rounds : List (List LOp × List LOp)) (post : List LOp) : Prop :=
  k ∈ (runT R cap (runT R cap tinit ops0) (rounds.map roundOps).flatten).c.bank.map Prod.fst ∧
    ((runT R cap (runT R cap tinit ops0) ((rounds.map roundOps).flatten ++ post)).c.bank.map Prod.fst).count k = 1

def Pointwise : Prop :=
  (∀ R rounds, BackLegal R rounds ↔ OrigLegal R rounds) ∧
  (∀ R cap k start rounds, BackFair R cap k start rounds ↔ OrigFair R cap k start rounds) ∧
  (∀ (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
      (rounds : List (List LOp × List LOp)) (post : List LOp),
    (∀ o ∈ ops₀, legalL R o) → BackLegal R rounds →
    (∀ o ∈ post, legalL R o) → BackFair R cap k (runT R cap tinit ops₀) rounds →
    (BackAt R cap k ops₀ rounds post ↔ OrigAt R cap k ops₀ rounds post))

def Nonvacuity : Prop :=
  (∀ o ∈ setupOps, legalL R0 o) ∧ BackLegal R0 [pcRound] ∧
  BackFair R0 10 0 (runT R0 10 tinit setupOps) [pcRound] ∧
  (∀ o ∈ ([.dup 0, .deliverAt 0] : List LOp), legalL R0 o) ∧
  BackAt R0 10 0 setupOps [pcRound] [.dup 0, .deliverAt 0]

def BackOutcome (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
    (rounds : List (List LOp × List LOp)) : Prop :=
  let start := runT R cap tinit ops₀
  let final := runT R cap start (rounds.map roundOps).flatten
  k ∈ final.c.bank.map Prod.fst ∧ ∀ post : List LOp, (∀ o ∈ post, legalL R o) → ((runT R cap final post).c.bank.map Prod.fst).count k = 1

def OriginalSignature : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops0 : List LOp) (hops0 : ∀ o ∈ ops0, legalL R o) (k : ℕ)
    (rounds : List (List LOp × List LOp)) (post : List LOp)
    (hleg : ∀ r ∈ rounds, ∀ o ∈ r.1 ++ r.2, legalL R o) (hpost : ∀ o ∈ post, legalL R o)
    (hfair : ∃ j, ∃ hj : j < rounds.length,
      DeliversT R cap k (runT R cap (runT R cap tinit ops0) ((rounds.take j).map roundOps).flatten) rounds[j]),
    k ∈ (runT R cap (runT R cap tinit ops0) (rounds.map roundOps).flatten).c.bank.map Prod.fst ∧
      ((runT R cap (runT R cap tinit ops0) ((rounds.map roundOps).flatten ++ post)).c.bank.map Prod.fst).count k
        = 1

def BackShape : Prop := Back_tagged_rounds ↔

  ∀ (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
    (rounds : List (List LOp × List LOp)),
    (∀ o ∈ ops₀, legalL R o) →
    let start := runT R cap tinit ops₀
    (∀ o ∈ (rounds.map roundOps).flatten, legalL R o) →
    (∃ (before : List (List LOp × List LOp))
        (r : List LOp × List LOp) (after : List (List LOp × List LOp)),
      rounds = before ++ r :: after ∧
        DeliversT R cap k (runT R cap start (before.map roundOps).flatten) r) →
    BackOutcome R cap k ops₀ rounds

def OriginalShape : Prop := OriginalSignature ↔
  ∀ (R : Roles) (cap : ℕ) (ops0 : List LOp) (hops0 : ∀ o ∈ ops0, legalL R o) (k : ℕ)
    (rounds : List (List LOp × List LOp)) (post : List LOp)
    (hleg : ∀ r ∈ rounds, ∀ o ∈ r.1 ++ r.2, legalL R o) (hpost : ∀ o ∈ post, legalL R o)
    (hfair : ∃ j, ∃ hj : j < rounds.length,
      DeliversT R cap k (runT R cap (runT R cap tinit ops0) ((rounds.take j).map roundOps).flatten) rounds[j]), OrigAt R cap k ops0 rounds post

def Projection : Prop := ∀ R cap k ops₀ rounds,
  BackOutcome R cap k ops₀ rounds ↔
    ∀ post, (∀ o ∈ post, legalL R o) → BackAt R cap k ops₀ rounds post

def Claim : Prop := Pointwise ∧ BackShape ∧ OriginalShape ∧ Projection

def ackOps : List LOp := setupOps ++ [.base .recover, .base (.bankProcess 0), .base (.ack 0)]
def ackStart : TSt := runT R0 10 tinit ackOps
def oldRound : List LOp × List LOp := ([], [.base (.bankProcess 0)])
def FairnessAudit : Prop :=
  ¬ Delivers 0 pcRound ∧
  (∀ o ∈ ackOps, legalL R0 o) ∧ ackStart.c.halted = false ∧
  Delivers 0 oldRound ∧ ¬ DeliversT R0 10 0 ackStart oldRound

def Witness : Prop := Nonvacuity ∧ FairnessAudit

end PL_bg6n3_6
