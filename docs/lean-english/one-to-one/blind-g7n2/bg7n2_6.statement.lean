namespace PL_bg7n2_6
open ControlStack
open ControlStack.AuthInstances
open ControlStack ControlStack.SC28
open ControlStack.AuthenticatedLog

def BackFull : Prop :=
  let unchecked := SC28.run [9] 1000 SC28.full SC28.init
    (forged28.map Prod.snd)
  let checked := AuthenticatedLog.authRun
    (SC28.step [9] 1000 SC28.full) claim28 SC28.init forged28
  SC28.budgetOf unchecked 0 = some 100 ∧
    SC28.leaseOf unchecked 1 = some 0 ∧
    SC28.usedL unchecked 0 = 5 ∧
    Authenticated.applied claim28 forged28 = [SC28.Op.work 1 5 5] ∧
    SC28.usedT checked = 0


def BackResult (unchecked checked : St) (applied : List Op) : Prop :=
  budgetOf unchecked 0 = some 100 ∧ leaseOf unchecked 1 = some 0 ∧
    usedL unchecked 0 = 5 ∧ applied = [.work 1 5 5] ∧ usedT checked = 0
def OrigResult (unchecked checked : St) : Prop :=
  unchecked.usage = [(1, 0, 5)] ∧ checked.usage = []
def uncheckedExample : St := ⟨[(0, 100)], [(1, 0)], [], [], [(2, 0, 5)], false⟩
def checkedExample : St := { init with usage := [(1, 0, 0)] }
def origExample : St := { init with usage := [(1, 0, 5)] }

def OrigFull : Prop :=
  (authRun (SC28.step [9] 1000 full) (fun _ => none) SC28.init forged28).usage = [(1, 0, 5)] ∧
    (authRun (SC28.step [9] 1000 full) claim28 SC28.init forged28).usage = []

def BackSchema : Prop :=
    BackResult
    (run [9] 1000 full init (forged28.map Prod.snd))
    (AuthenticatedLog.authRun (step [9] 1000 full) claim28 init forged28)
    (Authenticated.applied claim28 forged28)

def OrigSchema : Prop :=
  OrigResult
    (AuthenticatedLog.authRun (SC28.step [9] 1000 full) (fun _ => none) SC28.init forged28)
    (AuthenticatedLog.authRun (SC28.step [9] 1000 full) claim28 SC28.init forged28)


def Claim : Prop :=
  (BackFull ↔ BackSchema) ∧ (OrigFull ↔ OrigSchema) ∧
  (BackResult uncheckedExample checkedExample [.work 1 5 5] ∧
    ¬ OrigResult uncheckedExample checkedExample) ∧
  (OrigResult origExample init ∧ ¬ BackResult origExample init [])

def Witness : Prop :=
  let unchecked := run [9] 1000 full init (forged28.map Prod.snd)
  let checked := AuthenticatedLog.authRun (step [9] 1000 full) claim28 init forged28
  unchecked.usage = [(1, 0, 5)] ∧ checked.usage = [] ∧
    budgetOf unchecked 0 = some 100 ∧ leaseOf unchecked 1 = some 0
end PL_bg7n2_6
