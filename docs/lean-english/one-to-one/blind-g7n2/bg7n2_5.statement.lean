namespace PL_bg7n2_5
open ControlStack
open ControlStack.AuthInstances
open ControlStack ControlStack.SC28
open ControlStack.AuthenticatedLog

def BackFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (U : Set ℕ)
    (ops : List (ℕ × SC28.Op)),
    (∀ c ∈ admins, c ∉ U) →
    (∀ io ∈ ops, SC28.legal io.2) →
    let s := AuthenticatedLog.authRun
      (SC28.step admins G SC28.full) claim28 SC28.init ops
    SC28.Good G s ∧
      (∀ lease ∈ s.leases,
        ∃ c, c ∈ admins ∧ c ∉ U ∧
          (c, SC28.Op.issue c lease.1 lease.2) ∈ ops) ∧
      (∀ lid ∈ s.revoked,
        ∃ c, c ∈ admins ∧ c ∉ U ∧
          (c, SC28.Op.revoke c lid) ∈ ops)


def BackResult (admins : List ℕ) (G : ℕ) (U : Set ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good G s ∧
    (∀ l ∈ s.leases, ∃ c, c ∈ admins ∧ c ∉ U ∧ (c, Op.issue c l.1 l.2) ∈ ops) ∧
    (∀ lid ∈ s.revoked, ∃ c, c ∈ admins ∧ c ∉ U ∧ (c, Op.revoke c lid) ∈ ops)
def OrigResult (admins : List ℕ) (G : ℕ) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good G s ∧
    (∀ l ∈ s.leases, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .issue c l.1 l.2 ∧ c ∈ admins)) ∧
    (∀ lid ∈ s.revoked, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .revoke c lid ∧ c ∈ admins))

def OrigFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (U : List ℕ) (ops : List (ℕ × SC28.Op))
    (hU : ∀ u ∈ U, u ∉ admins) (hlegal : ∀ io ∈ ops, SC28.legal io.2),
    Good G (authRun (SC28.step admins G full) claim28 SC28.init ops) ∧
    (∀ l ∈ (authRun (SC28.step admins G full) claim28 SC28.init ops).leases, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .issue c l.1 l.2 ∧ c ∈ admins)) ∧
    (∀ l ∈ (authRun (SC28.step admins G full) claim28 SC28.init ops).revoked, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .revoke c l ∧ c ∈ admins))

def BackSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (U : Set ℕ)
    (ops : List (ℕ × SC28.Op)),
    (∀ c ∈ admins, c ∉ U) →
    (∀ io ∈ ops, SC28.legal io.2) →
    let s := AuthenticatedLog.authRun (SC28.step admins G SC28.full) claim28 SC28.init ops
    BackResult admins G U ops s

def OrigSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (U : List ℕ) (ops : List (ℕ × SC28.Op))
    (hU : ∀ u ∈ U, u ∉ admins) (hlegal : ∀ io ∈ ops, SC28.legal io.2),
    OrigResult admins G U ops (AuthenticatedLog.authRun (SC28.step admins G full) claim28 SC28.init ops)


def Claim : Prop :=
  (BackFull ↔ BackSchema) ∧ (OrigFull ↔ OrigSchema) ∧
  ∀ (admins : List ℕ) (G : ℕ) (Uset : Set ℕ) (Ulist : List ℕ) (ops : List (ℕ × Op)) (s : St),
    (∀ c ∈ admins, c ∉ Uset) → (∀ u ∈ Ulist, u ∉ admins) →
    (BackResult admins G Uset ops s ↔ OrigResult admins G Ulist ops s)

def Witness : Prop :=
  let ops : List (ℕ × Op) := [(9, .issue 9 0 10), (9, .assignTo 9 1 0), (1, .work 1 2 2), (9, .revoke 9 0)]
  let s := AuthenticatedLog.authRun (step [9] 10 full) claim28 init ops
  (∀ c ∈ ([9] : List ℕ), c ∉ ({1} : Set ℕ)) ∧
    (∀ u ∈ ([1] : List ℕ), u ∉ ([9] : List ℕ)) ∧
    (∀ io ∈ ops, legal io.2) ∧ s.leases = [(0, 10)] ∧ s.revoked = [0] ∧ s.usage = [(1, 0, 2)]
end PL_bg7n2_5
