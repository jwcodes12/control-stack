namespace PL_bg7n2_7
open ControlStack
open ControlStack.SC28Liveness
open ControlStack ControlStack.SC28

def BackFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St)
    (w lid b : ℕ) (units : List ℕ),
    s.halted = false →
    leaseOf s w = some lid →
    budgetOf s lid = some b →
    lid ∉ s.revoked →
    spentL s lid + charges units ≤ b →
    spentT s + charges units ≤ G →
    (run admins G full s (units.map (fun a => Op.work w a a))).usage =
      s.usage ++ units.map (fun a => (w, lid, a))


def BackResult (admins : List ℕ) (G : ℕ) (s : St) (w lid : ℕ) (units : List ℕ) : Prop :=
  (run admins G full s (units.map (fun a => Op.work w a a))).usage =
    s.usage ++ units.map (fun a => (w, lid, a))
def OrigResult (admins : List ℕ) (G : ℕ) (s : St) (w lid : ℕ) (units : List ℕ) : Prop :=
  (run admins G full s (units.map (fun a => Op.work w a a))).usage =
    s.usage ++ units.map (fun a => (w, lid, a))

def OrigFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St) (w lid b : ℕ) (as : List ℕ) (hh : s.halted = false)
    (hl : leaseOf s w = some lid) (hb : budgetOf s lid = some b) (hr : lid ∉ s.revoked)
    (hcl : spentL s lid + charges as ≤ b) (hcg : spentT s + charges as ≤ G),
    (run admins G full s (as.map (fun a => .work w a a))).usage = s.usage ++ as.map (fun a => (w, lid, a))

def BackSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St)
    (w lid b : ℕ) (units : List ℕ),
    s.halted = false →
    leaseOf s w = some lid →
    budgetOf s lid = some b →
    lid ∉ s.revoked →
    spentL s lid + charges units ≤ b →
    spentT s + charges units ≤ G →
    BackResult admins G s w lid units

def OrigSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St) (w lid b : ℕ) (as : List ℕ) (hh : s.halted = false)
    (hl : leaseOf s w = some lid) (hb : budgetOf s lid = some b) (hr : lid ∉ s.revoked)
    (hcl : spentL s lid + charges as ≤ b) (hcg : spentT s + charges as ≤ G),
    OrigResult admins G s w lid as


def Claim : Prop :=
  (BackFull ↔ BackSchema) ∧ (OrigFull ↔ OrigSchema) ∧
  ∀ (admins : List ℕ) (G : ℕ) (s : St) (w lid b : ℕ) (units : List ℕ),
    s.halted = false → leaseOf s w = some lid → budgetOf s lid = some b → lid ∉ s.revoked →
    spentL s lid + charges units ≤ b → spentT s + charges units ≤ G →
    (BackResult admins G s w lid units ↔ OrigResult admins G s w lid units)

def Witness : Prop :=
  let s := run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0]
  s.halted = false ∧ leaseOf s 1 = some 0 ∧ budgetOf s 0 = some 10 ∧ 0 ∉ s.revoked ∧
    spentL s 0 + charges [2, 3, 1] ≤ 10 ∧ spentT s + charges [2, 3, 1] ≤ 10 ∧
    (run [9] 10 full s ([2, 3, 1].map (fun a => Op.work 1 a a))).usage = [(1, 0, 2), (1, 0, 3), (1, 0, 1)] ∧
    charge full 0 0 = 1 ∧
    (run [9] 1 full init [.issue 9 0 1, .assignTo 9 1 0, .work 1 0 0]).usage = [(1, 0, 0)] ∧
    (run [9] 1 full init [.issue 9 0 1, .assignTo 9 1 0, .work 1 0 0]).ledger = [(0, 1)]
end PL_bg7n2_7
