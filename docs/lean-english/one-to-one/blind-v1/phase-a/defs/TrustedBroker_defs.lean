-- EXCERPT: definitions only; theorems and the redacted declarations are removed. Not compilable on its own.
namespace ControlStack.TrustedBroker

structure Roles where
  agent : Nat → Prop
  reviewer : Nat → Prop
  approver : Nat → Prop
  admin : Nat → Prop
  separated : ∀ uid, agent uid → ¬ reviewer uid ∧ ¬ approver uid ∧ ¬ admin uid

structure Lease where
  agent : Nat
  budget : Nat
  used : Nat
  expires : Nat
  revoked : Bool

structure Approval where
  digest : Nat
  destination : Nat
  agent : Nat
  lease : Nat
  signer : Nat
  expires : Nat
  used : Bool

structure Request where
  uid : Nat
  nonce : Nat
  digest : Nat
  destination : Nat
  lease : Nat
  cost : Nat

structure State where
  cap : Nat
  spent : Nat
  releases : Nat
  halted : Bool
  artifacts : Nat → Bool
  intact : Nat → Bool
  reviews : Nat → Option Nat
  approvals : Nat → Option Approval
  leases : Nat → Option Lease
  consumed : List Nat

def put {α : Type} (m : Nat → α) (key : Nat) (value : α) : Nat → α :=
  fun k => if k = key then value else m k

def Safe (s : State) : Prop :=
  s.spent ≤ s.cap ∧ s.releases ≤ s.spent ∧ s.consumed.Nodup ∧
    ∀ k l, s.leases k = some l → l.used ≤ l.budget

def initial (cap : Nat) : State :=
  { cap := cap, spent := 0, releases := 0, halted := false,
    artifacts := fun _ => false, intact := fun _ => false,
    reviews := fun _ => none, approvals := fun _ => none,
    leases := fun _ => none, consumed := [] }

/-- The ghost nonce history agrees exactly with the concrete used flag. -/
def Coherent (s : State) : Prop :=
  ∀ nonce, nonce ∈ s.consumed ↔
    ∃ a, s.approvals nonce = some a ∧ a.used = true

/-- Exact release guard, combining approval, review, artifact and shared quota.
`consumed` is a ghost history: initially empty and inserted with each release;
the concrete one-use test is the approval's `used` column. -/
def Allowed (roles : Roles) (s : State) (now : Nat) (r : Request)
    (a : Approval) (l : Lease) : Prop :=
  s.halted = false ∧ roles.agent r.uid ∧
  s.approvals r.nonce = some a ∧ a.used = false ∧
  a.digest = r.digest ∧ a.destination = r.destination ∧
  a.agent = r.uid ∧ a.lease = r.lease ∧ roles.approver a.signer ∧
  now < a.expires ∧ s.leases r.lease = some l ∧ l.agent = r.uid ∧
  l.revoked = false ∧ now < l.expires ∧
  0 < r.cost ∧ l.used + r.cost ≤ l.budget ∧ s.spent + r.cost ≤ s.cap ∧
  s.artifacts r.digest = true ∧ s.intact r.digest = true ∧
  (∃ reviewer, s.reviews r.digest = some reviewer) ∧ r.nonce ∉ s.consumed

def committed (s : State) (r : Request) (a : Approval) (l : Lease) : State :=
  { s with
    spent := s.spent + r.cost
    releases := s.releases + 1
    leases := put s.leases r.lease (some { l with used := l.used + r.cost }),
    approvals := put s.approvals r.nonce (some { a with used := true }),
    consumed := r.nonce :: s.consumed }

/-- Provisioning is represented explicitly. `stage` abstracts INSERT OR IGNORE
of equal bytes, never permits replacement of an existing digest with other bytes.
Review is a role assertion, not a theorem about content harmlessness. -/
inductive Step (roles : Roles) : State → State → Prop
  | deny (s) : Step roles s s
  | stage (s uid digest) (live : s.halted = false) (role : roles.agent uid) :
      Step roles s { s with
        artifacts := put s.artifacts digest true
        intact := put s.intact digest true }
  | review (s uid digest) (live : s.halted = false) (role : roles.reviewer uid)
      (existsArtifact : s.artifacts digest = true) :
      Step roles s { s with reviews := put s.reviews digest (some uid) }
  | issue (s uid key l now) (live : s.halted = false) (role : roles.admin uid)
      (agent : roles.agent l.agent) (fresh : s.leases key = none)
      (budget : 0 < l.budget) (unused : l.used = 0)
      (active : l.revoked = false) (future : now < l.expires) :
      Step roles s { s with leases := put s.leases key (some l) }
  | approve (s uid nonce a l now reviewer) (live : s.halted = false)
      (role : roles.approver uid) (signer : a.signer = uid)
      (agent : roles.agent a.agent) (fresh : s.approvals nonce = none)
      (unused : a.used = false)
      (review : s.reviews a.digest = some reviewer)
      (reviewRole : roles.reviewer reviewer) (distinct : reviewer ≠ uid)
      (lease : s.leases a.lease = some l) (owner : l.agent = a.agent)
      (active : l.revoked = false) (leaseFuture : now < l.expires)
      (future : now < a.expires) :
      Step roles s { s with approvals := put s.approvals nonce (some a) }
  | revoke (s uid key l) (live : s.halted = false) (role : roles.admin uid)
      (lease : s.leases key = some l) :
      Step roles s { s with leases := put s.leases key (some { l with revoked := true }) }
  | release (s now r a l) (allowed : Allowed roles s now r a l) :
      Step roles s (committed s r a l)
  | halt (s uid) (role : roles.admin uid) :
      Step roles s { s with halted := true }

/-- Relational closure includes any serial ordering of committed concurrent
transactions. It excludes snapshot rollback and partial external effects. -/
inductive Trace (roles : Roles) : State → State → Prop
  | nil (s) : Trace roles s s
  | cons {s t u} : Step roles s t → Trace roles t u → Trace roles s u

end ControlStack.TrustedBroker

