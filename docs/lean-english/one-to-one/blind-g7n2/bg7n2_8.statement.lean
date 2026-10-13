namespace PL_bg7n2_8
open ControlStack
open ControlStack.SC28Liveness
open ControlStack ControlStack.SC28

def BackFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St)
    (w lid b a reported : ℕ) (p : List Op),
    leaseOf s w = some lid →
    budgetOf s lid = some b →
    spentL s lid + charge full a reported ≤ b →
    spentT s + charge full a reported ≤ G →
    let t := run admins G full s p
    (step admins G full t (.work w a reported)).usage =
        t.usage ++ [(w, lid, a)] ∨
      t.halted = true ∨
      lid ∈ t.revoked ∨
      leaseOf t w ≠ some lid ∨
      spentL s lid < spentL t lid ∨
      spentT s < spentT t


def BackResult (admins : List ℕ) (G : ℕ) (s : St) (w lid a reported : ℕ) (p : List Op) : Prop :=
  let t := run admins G full s p
  (step admins G full t (.work w a reported)).usage = t.usage ++ [(w, lid, a)] ∨
    t.halted = true ∨ lid ∈ t.revoked ∨ leaseOf t w ≠ some lid ∨
    spentL s lid < spentL t lid ∨ spentT s < spentT t
def OrigResult (admins : List ℕ) (G : ℕ) (s : St) (w lid a : ℕ) (p : List Op) : Prop :=
  let t := run admins G full s p
  (step admins G full t (.work w a a)).usage = t.usage ++ [(w, lid, a)] ∨
    t.halted = true ∨ lid ∈ t.revoked ∨ leaseOf t w ≠ some lid ∨
    spentL s lid < spentL t lid ∨ spentT s < spentT t

def OrigFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St) (w a lid b : ℕ) (_hl : leaseOf s w = some lid) (hb : budgetOf s lid = some b)
    (hcl : spentL s lid + charge full a a ≤ b) (hcg : spentT s + charge full a a ≤ G) (p : List Op),
    let t := run admins G full s p
    (step admins G full t (.work w a a)).usage = t.usage ++ [(w, lid, a)] ∨
      t.halted = true ∨ lid ∈ t.revoked ∨ leaseOf t w ≠ some lid ∨ spentL s lid < spentL t lid ∨
      spentT s < spentT t

def BackSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St)
    (w lid b a reported : ℕ) (p : List Op),
    leaseOf s w = some lid →
    budgetOf s lid = some b →
    spentL s lid + charge full a reported ≤ b →
    spentT s + charge full a reported ≤ G →
    BackResult admins G s w lid a reported p

def OrigSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St) (w a lid b : ℕ) (_hl : leaseOf s w = some lid) (hb : budgetOf s lid = some b)
    (hcl : spentL s lid + charge full a a ≤ b) (hcg : spentT s + charge full a a ≤ G) (p : List Op),
    OrigResult admins G s w lid a p


def Claim : Prop :=
  (BackFull ↔ BackSchema) ∧ (OrigFull ↔ OrigSchema) ∧
  (∀ (s : St) (w lid b a reported G : ℕ),
    (spentL s lid + charge full a reported ≤ b ∧ spentT s + charge full a reported ≤ G) ↔
    (spentL s lid + charge full a a ≤ b ∧ spentT s + charge full a a ≤ G)) ∧
  (∀ (admins : List ℕ) (G : ℕ) (s : St) (w lid b a reported : ℕ) (p : List Op),
    leaseOf s w = some lid → budgetOf s lid = some b →
    spentL s lid + charge full a reported ≤ b → spentT s + charge full a reported ≤ G →
    (BackResult admins G s w lid a reported p ↔ OrigResult admins G s w lid a p))

def Witness : Prop :=
  let s := run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0]
  leaseOf s 1 = some 0 ∧ budgetOf s 0 = some 10 ∧
    spentL s 0 + charge full 2 999 ≤ 10 ∧ spentT s + charge full 2 999 ≤ 10 ∧
    (step [9] 10 full s (.work 1 2 999)).usage = [(1, 0, 2)]
end PL_bg7n2_8
