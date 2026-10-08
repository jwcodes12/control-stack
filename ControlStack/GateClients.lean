/-
Clients of the shared gate interface (`Gate.lean`).

Existing gates, now instances (each reuses the gate's own step lemma; nothing is re-proved by copying):
- `dispatchSpec`: AuditDispatch, where every effect has an audit row and agent operations create no effects;
- `auditGateSpec`: AuditGate, where every recorded execution has its `workflow.execute` row;
- `egressSpec p`: EgressGate, where every socket attempt originates at the gateway and goes to a pinned peer. This is
  still under the policy-integrity premise that the model takes by definition (audit finding; see FIDELITY.md).
  `egressHaltSpec` adds the generic absorbing halt. Halting freezes new socket ATTEMPTS only: bytes through an
  already-open CONNECT tunnel are not effects in this model. EgressGate's own `crashGateway` is not absorbing, since
  `startGateway` restarts it. Nothing here proves the halt is ever processed (liveness).

New primitives:
- **F4 content-addressed artefact gate** (`Artifact`): a deploy names a hash. It succeeds only if a trusted reviewer
  reviewed content with that hash, and it deploys the stored content with that hash. `deployed_reviewed`: every
  deployed artefact's hash was reviewed. `deployed_is_reviewed`: if no two contents that appear in the run (stored
  or reviewed) collide, the deployed content IS reviewed content. Global injectivity is not assumed. The hypothesis is checked on the FINAL state, so a collision created after a
  correct deploy voids it. That is conservative, but narrower than necessary (review D11). Reviews never expire. `collision_breaks`: with a collision, unreviewed content is deployed, so
  collision resistance cannot be dropped. The agent may write arbitrary content to the store at any time; what it
  cannot do is change the content behind a reviewed hash. Not claimed: that reviewed content is harmless.
- **F7 exact-payload approval** (`Approval`): an irreversible transaction executes only if an approval for exactly that
  transaction exists, the clock has not passed its expiry, and its nonce is unused. `approval_safe`: every execution is
  approved and unexpired, and nonces never repeat (no replay). `replay_without_nonce`: dropping the nonce check lets
  one approval execute twice. `agent_cannot_approve` / `Artifact.agent_cannot_review`: the agent's own operations
  never add approvals or reviews. The theorems above range over ALL traces, including the trusted principals'
  operations. Premises (not modelled): signatures are unforgeable and the key is not the agent's; the used-nonce
  store and the clock are durable and monotone (`replay_if_nonces_lost` shows durability matters).
-/
import ControlStack.Gate
import ControlStack.AuditDispatch
import ControlStack.AuditGate
import ControlStack.EgressGate

namespace ControlStack.GateClients

open ControlStack.Gate

/-! ## AuditDispatch -/

def dispatchSys : System AuditDispatch.St AuditDispatch.Op ℕ where
  step := AuditDispatch.step
  effects := fun s => s.effects

theorem dispatch_effects_prefix (s : AuditDispatch.St) (o : AuditDispatch.Op) :
    s.effects <+: (AuditDispatch.step s o).effects := by
  cases o <;> simp only [AuditDispatch.step] <;> (try split_ifs) <;> simp [List.prefix_append]

def dispatchSpec : Spec dispatchSys where
  Inv := AuditDispatch.Inv
  ok := fun s e => e ∈ s.audits
  step_inv := AuditDispatch.step_inv
  log_prefix := dispatch_effects_prefix
  inv_ok := fun _ h e he => h.1 e he

theorem dispatch_no_agent_effects :
    NoAgentEffects dispatchSys (fun o => ∀ id, o ≠ .dispatch id) :=
  ⟨fun s o h => AuditDispatch.app_cannot_effect s o h⟩

/-! ## AuditGate -/

def auditGateSys : System AuditGate.St AuditGate.Op ℕ where
  step := AuditGate.step
  effects := fun s => s.executions

theorem auditGate_prefix (s : AuditGate.St) (o : AuditGate.Op) :
    s.executions <+: (AuditGate.step s o).executions := by
  cases o <;> simp [AuditGate.step, List.prefix_append]

def auditGateSpec : Spec auditGateSys where
  Inv := AuditGate.Inv
  ok := fun s e => (⟨"workflow.execute", e⟩ : AuditGate.Audit) ∈ s.audits
  step_inv := AuditGate.step_inv
  log_prefix := auditGate_prefix
  inv_ok := fun _ h e he => h e he

/-! ## EgressGate -/

def egressSys (p : EgressGate.Policy) : System EgressGate.State EgressGate.Action EgressGate.Effect where
  step := EgressGate.step p
  effects := fun s => s.attempts

theorem egress_prefix (p : EgressGate.Policy) (s : EgressGate.State) (a : EgressGate.Action) :
    s.attempts <+: (EgressGate.step p s a).attempts := by
  cases a with
  | request key =>
    simp only [EgressGate.step]
    split
    · cases EgressGate.lookup p key <;> simp [List.prefix_append]
    · exact List.prefix_refl _
  | directAttempt peer =>
    simp only [EgressGate.step]; split <;> simp [List.prefix_append]
  | _ => simp [EgressGate.step]

def egressSpec (p : EgressGate.Policy) : Spec (egressSys p) where
  Inv := EgressGate.Invariant p
  ok := fun _ e => e.origin = .gateway ∧ e.peer ∈ p.map EgressGate.Rule.peer
  step_inv := fun s a h => EgressGate.step_safe p s a h
  log_prefix := egress_prefix p
  inv_ok := fun _ h e he => h.2 e he

/-- the egress gate with an absorbing trusted halt: the spec lifts and halting freezes all socket attempts -/
def egressHaltSpec (p : EgressGate.Policy) : Spec (withHalt (egressSys p)) := withHalt_spec (egressSpec p)

/-! ## F4: content-addressed artefact gate -/

namespace Artifact

variable {C H : Type} [DecidableEq H]

structure St (C H : Type) where
  reviewedContent : List C   -- ghost: what the trusted reviewer actually read
  reviewed : List H          -- hashes the reviewer signed
  store : List C             -- content-addressed store; the agent writes freely
  deployed : List C          -- effect log

inductive Op (C H : Type) where
  | put (c : C)              -- agent: add any content to the store
  | review (c : C)           -- trusted reviewer: reads c, signs its hash
  | deploy (h : H)           -- agent requests deployment of hash h; the gate decides

def step (hash : C → H) (s : St C H) : Op C H → St C H
  | .put c => { s with store := s.store ++ [c] }
  | .review c => { s with reviewedContent := s.reviewedContent ++ [c], reviewed := s.reviewed ++ [hash c] }
  | .deploy h =>
    if h ∈ s.reviewed then
      match s.store.find? (fun c => hash c = h) with
      | some c => { s with deployed := s.deployed ++ [c] }
      | none => s
    else s

def sys (hash : C → H) : System (St C H) (Op C H) C where
  step := step hash
  effects := fun s => s.deployed

def Inv (hash : C → H) (s : St C H) : Prop :=
  s.reviewed = s.reviewedContent.map hash ∧ (∀ c ∈ s.deployed, hash c ∈ s.reviewed) ∧ ∀ c ∈ s.deployed, c ∈ s.store

theorem step_inv (hash : C → H) (s : St C H) (o : Op C H) (h : Inv hash s) : Inv hash (step hash s o) := by
  obtain ⟨h1, h2, h3⟩ := h
  cases o with
  | put c =>
    refine ⟨h1, h2, fun d hd => ?_⟩
    simp only [step, List.mem_append] at hd ⊢
    exact Or.inl (h3 d hd)
  | review c =>
    refine ⟨by simp [step, h1], fun d hd => ?_, fun d hd => ?_⟩
    · simp only [step, List.mem_append] at hd ⊢
      exact Or.inl (h2 d hd)
    · simp only [step] at hd ⊢; exact h3 d hd
  | deploy hh =>
    simp only [step]
    split_ifs with hr
    · cases hf : s.store.find? (fun c => hash c = hh) with
      | none => exact ⟨h1, h2, h3⟩
      | some c =>
        have hc : hash c = hh := by simpa using List.find?_some hf
        have hcs : c ∈ s.store := List.mem_of_find?_eq_some hf
        refine ⟨h1, fun d hd => ?_, fun d hd => ?_⟩
        · simp only [List.mem_append, List.mem_singleton] at hd
          rcases hd with hd | rfl
          · exact h2 d hd
          · rw [hc]; exact hr
        · simp only [List.mem_append, List.mem_singleton] at hd
          rcases hd with hd | rfl
          · exact h3 d hd
          · exact hcs
    · exact ⟨h1, h2, h3⟩

theorem prefix_step (hash : C → H) (s : St C H) (o : Op C H) : s.deployed <+: (step hash s o).deployed := by
  cases o with
  | put c => simp [step]
  | review c => simp [step]
  | deploy hh =>
    simp only [step]
    split_ifs
    · cases s.store.find? (fun c => hash c = hh) <;> simp [List.prefix_append]
    · exact List.prefix_refl _

def spec (hash : C → H) : Spec (sys hash) where
  Inv := Inv hash
  ok := fun s c => hash c ∈ s.reviewed
  step_inv := step_inv hash
  log_prefix := prefix_step hash
  inv_ok := fun _ h c hc => h.2.1 c hc

/-- **Every deployed artefact's hash was reviewed**, after any interleaving of agent and reviewer operations. -/
theorem deployed_reviewed (hash : C → H) (ops : List (Op C H)) :
    ∀ c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).deployed,
      hash c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).reviewed :=
  ((spec hash).trace_safe _ ops ⟨rfl, by simp, by simp⟩).2.2

/-- if the hash has no collision AMONG THE CONTENTS THAT APPEAR in the run (stored or reviewed), **the deployed
content is reviewed content**. Only collisions an adversary actually produced matter; no global injectivity is
assumed (a real hash compresses, so it is never globally injective). -/
theorem deployed_is_reviewed (hash : C → H) (ops : List (Op C H))
    (hinj : Set.InjOn hash {c | c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).store ∨
                                c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).reviewedContent}) :
    ∀ c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).deployed,
      c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).reviewedContent := by
  intro c hc
  have hinv := ((spec hash).trace_safe ⟨[], [], [], []⟩ ops ⟨rfl, by simp, by simp⟩).1
  have h := hinv.2.1 c hc
  rw [hinv.1] at h
  obtain ⟨c', hc', heq⟩ := List.mem_map.1 h
  have : c' = c := hinj (Or.inr hc') (Or.inl (hinv.2.2 c hc)) heq
  rwa [← this]

/-- **Collision resistance cannot be dropped**: with hash ≡ (), the reviewer reads `true`, the agent stores `false`
first, and deploying the reviewed hash ships the unreviewed `false`. -/
theorem collision_breaks :
    let s := (sys (fun _ : Bool => ())).run ⟨[], [], [], []⟩ [.put false, .review true, .deploy ()]
    false ∈ s.deployed ∧ false ∉ s.reviewedContent := by
  decide

/-- agent operations: storing content and requesting deploys (review belongs to the trusted reviewer) -/
def agentOp : Op C H → Prop
  | .put _ => True
  | .deploy _ => True
  | .review _ => False

/-- **The agent cannot review** (adversarial review D9): agent operations never change what was reviewed. -/
theorem agent_cannot_review (hash : C → H) (s : St C H) (o : Op C H) (ho : agentOp o) :
    (step hash s o).reviewed = s.reviewed ∧ (step hash s o).reviewedContent = s.reviewedContent := by
  cases o with
  | put c => simp [step]
  | deploy hh =>
    simp only [step]; split_ifs
    · cases s.store.find? (fun c => hash c = hh) <;> simp
    · simp
  | review c => simp [agentOp] at ho

end Artifact

/-! ## F7: exact-payload approval with expiry and replay protection -/

namespace Approval

variable {P : Type} [DecidableEq P]

structure Tx (P : Type) where
  payload : P
  nonce : ℕ
  expiry : ℕ
  deriving DecidableEq

structure St (P : Type) where
  now : ℕ
  approvals : List (Tx P)        -- issued only by the distinct trusted principal
  used : List ℕ
  executed : List (Tx P × ℕ)     -- effect log: transaction and execution time

inductive Op (P : Type) where
  | tick                         -- trusted clock
  | approve (t : Tx P)           -- trusted approver (distinct principal)
  | execute (t : Tx P)           -- agent requests an irreversible transaction; the gate decides

def step (s : St P) : Op P → St P
  | .tick => { s with now := s.now + 1 }
  | .approve t => { s with approvals := s.approvals ++ [t] }
  | .execute t =>
    if t ∈ s.approvals ∧ s.now ≤ t.expiry ∧ t.nonce ∉ s.used then
      { s with used := s.used ++ [t.nonce], executed := s.executed ++ [(t, s.now)] }
    else s

def sys : System (St P) (Op P) (Tx P × ℕ) where
  step := step
  effects := fun s => s.executed

def Inv (s : St P) : Prop :=
  s.used = s.executed.map (fun e => e.1.nonce) ∧ s.used.Nodup ∧
    ∀ e ∈ s.executed, e.1 ∈ s.approvals ∧ e.2 ≤ e.1.expiry

theorem step_inv (s : St P) (o : Op P) (h : Inv s) : Inv (step s o) := by
  obtain ⟨h1, h2, h3⟩ := h
  cases o with
  | tick => exact ⟨h1, h2, h3⟩
  | approve t =>
    refine ⟨h1, h2, fun e he => ?_⟩
    obtain ⟨ha, hx⟩ := h3 e he
    exact ⟨List.mem_append_left _ ha, hx⟩
  | execute t =>
    simp only [step]
    split_ifs with hc
    · refine ⟨by simp [h1], List.nodup_append.2 ⟨h2, List.nodup_singleton _, ?_⟩, fun e he => ?_⟩
      · intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; intro hab; subst hab; exact hc.2.2 ha
      · simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact h3 e he
        · exact ⟨hc.1, hc.2.1⟩
    · exact ⟨h1, h2, h3⟩

theorem prefix_step (s : St P) (o : Op P) : s.executed <+: (step s o).executed := by
  cases o with
  | tick => simp [step]
  | approve t => simp [step]
  | execute t => simp only [step]; split_ifs <;> simp [List.prefix_append]

def spec : Spec (sys (P := P)) where
  Inv := Inv
  ok := fun s e => e.1 ∈ s.approvals ∧ e.2 ≤ e.1.expiry
  step_inv := step_inv
  log_prefix := prefix_step
  inv_ok := fun _ h e he => h.2.2 e he

/-- **Approval safety.** From the initial state, after any trace: every executed transaction carries an approval for
exactly that payload, nonce and expiry, was executed no later than its expiry, and no nonce executes twice. -/
theorem approval_safe (ops : List (Op P)) :
    let s := (sys (P := P)).run ⟨0, [], [], []⟩ ops
    (∀ e ∈ s.executed, e.1 ∈ s.approvals ∧ e.2 ≤ e.1.expiry) ∧ (s.executed.map (fun e => e.1.nonce)).Nodup := by
  have h := ((spec (P := P)).trace_safe ⟨0, [], [], []⟩ ops ⟨rfl, List.nodup_nil, by simp⟩).1
  exact ⟨h.2.2, h.1 ▸ h.2.1⟩

/-- the same gate without the nonce check -/
def stepNoNonce (s : St P) : Op P → St P
  | .execute t =>
    if t ∈ s.approvals ∧ s.now ≤ t.expiry then
      { s with used := s.used ++ [t.nonce], executed := s.executed ++ [(t, s.now)] }
    else s
  | o => step s o

/-- **Replay protection cannot be dropped**: without the nonce check one approval executes twice. -/
theorem replay_without_nonce :
    let t : Tx Unit := ⟨(), 0, 5⟩
    ([Op.approve t, .execute t, .execute t].foldl stepNoNonce (⟨0, [], [], []⟩ : St Unit)).executed.length = 2 ∧
    ([Op.approve t, .execute t, .execute t].foldl step (⟨0, [], [], []⟩ : St Unit)).executed.length = 1 := by
  decide

/-- agent operations: requesting an execution (the clock and approvals belong to trusted principals) -/
def agentOp : Op P → Prop
  | .execute _ => True
  | _ => False

/-- **The agent cannot approve** (adversarial review D9): agent operations never change the approval list. -/
theorem agent_cannot_approve (s : St P) (o : Op P) (ho : agentOp o) : (step s o).approvals = s.approvals := by
  cases o with
  | execute t => simp only [step]; split_ifs <;> simp
  | _ => simp [agentOp] at ho

/-- **Nonce durability cannot be dropped** (review D9): if a restart loses the used-nonce store, one approval executes
twice. The model above has no restart. Durability of `used` is a premise, not a theorem. -/
theorem replay_if_nonces_lost :
    let t : Tx Unit := ⟨(), 0, 5⟩
    let s1 := [Op.approve t, .execute t].foldl step (⟨0, [], [], []⟩ : St Unit)
    let s2 := step { s1 with used := [] } (.execute t)
    s2.executed.length = 2 := by
  decide

end Approval

end ControlStack.GateClients

#print axioms ControlStack.GateClients.dispatchSpec
#print axioms ControlStack.GateClients.dispatch_no_agent_effects
#print axioms ControlStack.GateClients.auditGateSpec
#print axioms ControlStack.GateClients.egressSpec
#print axioms ControlStack.GateClients.egressHaltSpec
#print axioms ControlStack.GateClients.Artifact.deployed_reviewed
#print axioms ControlStack.GateClients.Artifact.deployed_is_reviewed
#print axioms ControlStack.GateClients.Artifact.collision_breaks
#print axioms ControlStack.GateClients.Approval.approval_safe
#print axioms ControlStack.GateClients.Approval.replay_without_nonce
#print axioms ControlStack.GateClients.Approval.agent_cannot_approve
#print axioms ControlStack.GateClients.Approval.replay_if_nonces_lost
#print axioms ControlStack.GateClients.Artifact.agent_cannot_review
