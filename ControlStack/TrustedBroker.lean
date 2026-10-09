import Std

/-!
Joint reference-broker transaction relation. One transition is one committed
SQLite transaction, not an OS effect. Naturals abstract UID/token/digest/body
identities; `intact` represents the concrete SHA-256 recheck. Atomic storage,
authentic OS identities, faithful parsing and no rollback remain premises.
Denials and reopen are identity transitions. Arbitrary time inputs permit clock
rollback: no monotone-clock or anti-rollback guarantee is inferred.
-/
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

theorem initial_safe (cap : Nat) : Safe (initial cap) := by
  simp [Safe, initial]

/-- The ghost nonce history agrees exactly with the concrete used flag. -/
def Coherent (s : State) : Prop :=
  ∀ nonce, nonce ∈ s.consumed ↔
    ∃ a, s.approvals nonce = some a ∧ a.used = true

theorem initial_coherent (cap : Nat) : Coherent (initial cap) := by
  simp [Coherent, initial]

theorem nonce_history_redundant (s : State) (coherent : Coherent s)
    (nonce : Nat) (a : Approval) (lookup : s.approvals nonce = some a)
    (unused : a.used = false) : nonce ∉ s.consumed := by
  intro member
  obtain ⟨b, hb, used⟩ := (coherent nonce).mp member
  have eq : a = b := by simpa [lookup] using hb
  subst b
  simp_all

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

theorem committed_nonce_unusable (roles : Roles) (s : State) (r : Request)
    (a : Approval) (l : Lease) (now : Nat) (r' : Request)
    (a' : Approval) (l' : Lease) (sameNonce : r'.nonce = r.nonce) :
    ¬ Allowed roles (committed s r a l) now r' a' l' := by
  intro allowed
  obtain ⟨_, _, lookup, unused, _⟩ := allowed
  have eq : ({ a with used := true } : Approval) = a' := by
    simpa [committed, put, sameNonce] using lookup
  subst a'
  simp at unused

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

theorem transaction_preserves (roles : Roles) (s t : State)
    (safe : Safe s) (step : Step roles s t) : Safe t := by
  rcases safe with ⟨global, count, nonces, leases⟩
  cases step with
  | deny => exact ⟨global, count, nonces, leases⟩
  | stage => exact ⟨global, count, nonces, leases⟩
  | review => exact ⟨global, count, nonces, leases⟩
  | approve => exact ⟨global, count, nonces, leases⟩
  | halt => exact ⟨global, count, nonces, leases⟩
  | issue uid key l now live role agent fresh budget unused active future =>
      refine ⟨global, count, nonces, ?_⟩
      intro k v hv
      by_cases hk : k = key
      · simp [put, hk] at hv
        subst v
        omega
      · exact leases k v (by simpa [put, hk] using hv)
  | revoke uid key l live role hl =>
      refine ⟨global, count, nonces, ?_⟩
      intro k v hv
      by_cases hk : k = key
      · simp [put, hk] at hv
        subst v
        exact leases key l hl
      · exact leases k v (by simpa [put, hk] using hv)
  | release now r a l allowed =>
      rcases allowed with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, positive,
        localCap, globalCap, _, _, _, fresh⟩
      refine ⟨globalCap, ?_, List.nodup_cons.mpr ⟨fresh, nonces⟩, ?_⟩
      · change s.releases + 1 ≤ s.spent + r.cost
        omega
      · intro k v hv
        by_cases hk : k = r.lease
        · simp [committed, put, hk] at hv
          subst v
          exact localCap
        · exact leases k v (by simpa [committed, put, hk] using hv)

theorem halted_absorbing (roles : Roles) (s t : State)
    (halted : s.halted = true) (step : Step roles s t) :
    t.halted = true ∧ t.releases = s.releases := by
  cases step <;> simp_all [Allowed]

theorem transaction_coherent (roles : Roles) (s t : State)
    (coherent : Coherent s) (step : Step roles s t) : Coherent t := by
  cases step with
  | deny => exact coherent
  | stage => exact coherent
  | review => exact coherent
  | issue => exact coherent
  | revoke => exact coherent
  | halt => exact coherent
  | approve uid nonce a l now reviewer live role signer agent fresh unused
      review reviewRole distinct lease owner active leaseFuture future =>
      intro k
      by_cases hk : k = nonce
      · subst k
        have absent : nonce ∉ s.consumed := by
          intro member
          obtain ⟨b, hb, _⟩ := (coherent nonce).mp member
          simp [fresh] at hb
        simp [put, absent, unused]
      · simpa [put, hk] using coherent k
  | release now r a l allowed =>
      intro k
      by_cases hk : k = r.nonce
      · simp [committed, put, hk]
      · simpa [committed, put, hk, List.mem_cons] using coherent k

/-- Relational closure includes any serial ordering of committed concurrent
transactions. It excludes snapshot rollback and partial external effects. -/
inductive Trace (roles : Roles) : State → State → Prop
  | nil (s) : Trace roles s s
  | cons {s t u} : Step roles s t → Trace roles t u → Trace roles s u

theorem trace_preserves (roles : Roles) (s t : State)
    (safe : Safe s) (trace : Trace roles s t) : Safe t := by
  induction trace with
  | nil => exact safe
  | cons step _ ih => exact ih (transaction_preserves roles _ _ safe step)

theorem trace_coherent (roles : Roles) (s t : State)
    (coherent : Coherent s) (trace : Trace roles s t) : Coherent t := by
  induction trace with
  | nil => exact coherent
  | cons step _ ih => exact ih (transaction_coherent roles _ _ coherent step)

theorem trace_halt_absorbing (roles : Roles) (s t : State)
    (halted : s.halted = true) (trace : Trace roles s t) :
    t.halted = true ∧ t.releases = s.releases := by
  induction trace with
  | nil => exact ⟨halted, rfl⟩
  | cons step _ ih =>
      obtain ⟨ht, hc⟩ := halted_absorbing roles _ _ halted step
      obtain ⟨hu, huc⟩ := ih ht
      exact ⟨hu, huc.trans hc⟩

#print axioms transaction_preserves
#print axioms halted_absorbing
#print axioms committed_nonce_unusable
#print axioms initial_safe
#print axioms initial_coherent
#print axioms nonce_history_redundant
#print axioms transaction_coherent
#print axioms trace_coherent
#print axioms trace_preserves
#print axioms trace_halt_absorbing
end ControlStack.TrustedBroker
