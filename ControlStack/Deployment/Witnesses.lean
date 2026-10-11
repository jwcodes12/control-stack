import ControlStack.Deployment.R2Contracts
namespace ControlStack.Deployment.Witnesses
open ControlStack
open ControlStack.Deployment

deriving instance DecidableEq for TrustedBroker.Lease
deriving instance DecidableEq for TrustedBroker.Approval

/-- Hand-authored abstract witnesses; these are not observed container receipts. -/
def R : TrustedBroker.Roles :=
  { agent := fun uid => uid = 23701 ∨ uid = 23702,
    reviewer := fun uid => uid = 23703, approver := fun uid => uid = 23704,
    admin := fun uid => uid = 23700,
    separated := by intro uid h; rcases h with rfl | rfl <;> decide }
def lease : TrustedBroker.Lease := ⟨23701,1,0,1000,false⟩
def approval : TrustedBroker.Approval := ⟨23,1,23701,9,23704,1000,false⟩
def request : TrustedBroker.Request := ⟨23701,7,23,1,9,1⟩
def s0 := TrustedBroker.initial 1
def s1 : TrustedBroker.State := {s0 with artifacts := TrustedBroker.put s0.artifacts 23 true, intact := TrustedBroker.put s0.intact 23 true}
def s2 : TrustedBroker.State := {s1 with reviews := TrustedBroker.put s1.reviews 23 (some 23703)}
def s3 : TrustedBroker.State := {s2 with leases := TrustedBroker.put s2.leases 9 (some lease)}
def s4 : TrustedBroker.State := {s3 with approvals := TrustedBroker.put s3.approvals 7 (some approval)}
def s5 := TrustedBroker.committed s4 request approval lease

theorem staged : TrustedBroker.Step R s0 s1 :=
  .stage s0 23701 23 (by decide) (.inl rfl)
theorem reviewed : TrustedBroker.Step R s1 s2 :=
  .review s1 23703 23 (by decide) rfl (by decide)
theorem issued : TrustedBroker.Step R s2 s3 :=
  .issue s2 23700 9 lease 0 (by decide) rfl (.inl rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide)
theorem approved : TrustedBroker.Step R s3 s4 :=
  .approve s3 23704 7 approval lease 0 23703 (by decide) rfl rfl
    (.inl rfl) (by decide) (by decide) (by decide) rfl (by decide)
    (by decide) rfl (by decide) (by decide) (by decide)
theorem release_allowed : TrustedBroker.Allowed R s4 0 request approval lease := by
  exact ⟨by decide, Or.inl rfl, by decide, by decide, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, rfl, rfl, by decide, by decide, by decide, by decide,
    by decide, by decide, ⟨23703,by decide⟩, by decide⟩
theorem released : TrustedBroker.Step R s4 s5 := .release s4 0 request approval lease release_allowed
theorem useful_broker_trace : TrustedBroker.Trace R (TrustedBroker.initial 1) s5 :=
  .cons staged (.cons reviewed (.cons issued (.cons approved (.cons released (.nil _)))))
theorem useful_broker_state : s5.spent = 1 ∧ s5.releases = 1 ∧ s5.consumed = [7] := by decide

def receiverNode : Node := ⟨3,23700,false,false,false,2,true⟩
def agentA : Node := ⟨0,23701,true,false,false,0,true⟩
def agentB : Node := ⟨1,23702,true,false,false,0,true⟩
theorem extracted : ExtractionFaithful clean receiverNode clean.edges :=
  ⟨⟨fun _ h => h⟩, by decide, rfl⟩
theorem refined : BrokerProtocolRefinement clean R 1 s5 [7] where
  transactions := useful_broker_trace
  callerBinding := by
    intro uid h
    rcases h with h | h
    · exact ⟨agentA,by decide,rfl,h⟩
    · exact ⟨agentB,by decide,rfl,h⟩
  publication := List.Sublist.refl _
theorem useful_deployment_broker :
    ¬ R.agent receiverNode.uid ∧ [7].Nodup ∧ [7].length ≤ 1 ∧
    (∀ nonce ∈ ([7] : List Nat), ∃ a, s5.approvals nonce = some a ∧ a.used = true) :=
  (deployment_broker_safe clean receiverNode R 1 s5 clean.edges [7]
    clean_accepted extracted refined).2

/-- Disable the release guard and reuse the same nonce: quota and one-use fail. -/
def unguardedReplay := TrustedBroker.committed s5 request approval lease
theorem unguarded_release_refutes : ¬ TrustedBroker.Safe unguardedReplay := by
  intro safe
  have bad : ¬ unguardedReplay.spent ≤ unguardedReplay.cap := by decide
  exact bad safe.1
theorem replay_refuted : ¬ TrustedBroker.Allowed R s5 0 request approval lease :=
  TrustedBroker.committed_nonce_unusable R s4 request approval lease 0 request approval lease rfl

def tampered : TrustedBroker.State := {s4 with intact := fun _ => false}
theorem tampered_payload_refutes : ¬ TrustedBroker.Allowed R tampered 0 request approval lease := by
  intro allowed
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,intact,_,_⟩ := allowed
  simp [tampered] at intact

def missingWriter : Edge := ⟨0,4,true,false,true⟩
theorem omitted_writer_refutes : ¬ Faithful clean [missingWriter] := by
  intro faithful
  have notCaptured : missingWriter ∉ clean.edges := by decide
  exact notCaptured (faithful.captured missingWriter (by simp))
theorem sink_duplicate_refutes : ¬ List.Sublist ([7,7] : List Nat).reverse s5.consumed := by decide

theorem path_positive : ¬ AvoidedPath clean agentA.id clean.sink ∧
    ¬ AvoidedPath clean agentA.id clean.database :=
  accepted_no_avoided_path clean clean_accepted agentA (by decide) rfl

def bypassed : IR := {clean with edges := missingWriter :: clean.edges}
theorem bypass_path_exists : AvoidedPath bypassed agentA.id bypassed.sink :=
  .step missingWriter (by simp [bypassed]) (by decide) (by decide) .refl

theorem sink_positive : (⟨3,4,true,false,true⟩ : Edge).source = clean.receiver :=
  exclusive_sink clean clean_accepted _ (by decide) rfl rfl
theorem database_positive : (⟨2,5,true,false,true⟩ : Edge).source = clean.receiver ∨
    (⟨2,5,true,false,true⟩ : Edge).source = clean.broker :=
  database_custody clean clean_accepted _ (by decide) rfl rfl
theorem runtime_positive : (⟨3,4,true,false,true⟩ : Edge).source = clean.receiver :=
  runtime_exclusive clean clean.edges clean_accepted extracted.authority _ (by decide) rfl rfl
theorem identity_positive : agentA.uid ≠ receiverNode.uid :=
  agent_not_receiver_uid clean clean_accepted receiverNode agentA (by decide) rfl (by decide) rfl
theorem uid_collision_refutes :
    ¬ Accepted {clean with nodes := {agentA with uid := 23700} :: clean.nodes.tail} := by decide
theorem database_bypass_refutes :
    ¬ Accepted {clean with edges := ⟨0,5,true,false,true⟩ :: clean.edges} := by decide

/-- Abstract replay witness only: a provisioned model request commits once. -/
def singleStep (s op : Nat) : Nat := if s = 0 ∧ op = 0 then 1 else s
def singleInterpret : Nat → TrustedBroker.State | 0 => s4 | _ => s5
theorem single_checked (s op : Nat) :
    TrustedBroker.Step R (singleInterpret s) (singleInterpret (singleStep s op)) := by
  unfold singleStep
  split_ifs with h
  · rcases h with ⟨rfl,rfl⟩; exact released
  · exact .deny _
def singleTable : IndexedBrokerTable R := ⟨singleInterpret,singleStep,single_checked⟩
theorem indexed_positive : CheckedTrace.verified singleStep 0
    ([⟨0,0,1⟩] : List (CheckedTrace.Receipt Nat Nat)) = true := by decide
theorem indexed_fabricated_post_refutes : CheckedTrace.verified singleStep 0
    ([⟨0,0,2⟩] : List (CheckedTrace.Receipt Nat Nat)) = false := by decide
theorem indexed_empty_capture_passes : CheckedTrace.verified singleStep 0
    ([] : List (CheckedTrace.Receipt Nat Nat)) = true := by decide


def modelOps : List SC26.Op := [.request 23701 payload, .approve 23703 0 payload,
  .execute 23701 0, .deliver 0, .arrive 0]
theorem model_ops_legal : ∀ o ∈ modelOps, SC26.legal twoRoles o := by
  intro o member
  simp [modelOps] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> trivial
theorem sc26_refined : ProtocolRefinement clean receiverNode twoRoles 1 modelOps [(0,payload)] where
  gateUID := rfl
  callerBinding := by intro c k tx member; simp [modelOps] at member
  unitCosts := by intro e member; simp only [List.mem_singleton] at member; subst e; rfl
  publication := by decide
theorem useful_sc26_deployment_count : ([(0,payload)] : List (Nat × SC26.Tx)).length ≤ 1 :=
  (deployment_safe clean receiverNode twoRoles 1 modelOps clean.edges [(0,payload)]
    clean_accepted extracted sc26_refined).2.2.2.2
theorem protocol_positive : SC26.Good twoRoles 1 (SC26.run twoRoles 1 SC26.full SC26.init modelOps) :=
  protocol_safe twoRoles 1 modelOps model_ops_legal
theorem one_use_positive : (SC26.run twoRoles 1 SC26.full SC26.init modelOps).reserved.Nodup :=
  one_use twoRoles 1 modelOps
theorem legal_call_positive : SC26.legal (roles clean receiverNode.uid [23703] [23704])
    (.bankCall agentA.uid 0 payload) :=
  agent_call_legal clean clean_accepted receiverNode agentA (by decide) rfl (by decide) rfl [23703] [23704] 0 payload
theorem gate_positive :
    (SC26.spec twoRoles 1).Inv ((SC26.sys twoRoles 1).run SC26.init
      [⟨.request 23701 payload,by trivial⟩,⟨.approve 23703 0 payload,by trivial⟩,
       ⟨.execute 23701 0,by trivial⟩,⟨.deliver 0,by trivial⟩,⟨.arrive 0,by trivial⟩]) :=
  (gate_contract twoRoles 1 _).1

end ControlStack.Deployment.Witnesses
#print axioms ControlStack.Deployment.Witnesses.useful_broker_trace
#print axioms ControlStack.Deployment.Witnesses.useful_broker_state
#print axioms ControlStack.Deployment.Witnesses.useful_deployment_broker
#print axioms ControlStack.Deployment.Witnesses.unguarded_release_refutes
#print axioms ControlStack.Deployment.Witnesses.replay_refuted
#print axioms ControlStack.Deployment.Witnesses.tampered_payload_refutes
#print axioms ControlStack.Deployment.Witnesses.omitted_writer_refutes
#print axioms ControlStack.Deployment.Witnesses.sink_duplicate_refutes
#print axioms ControlStack.Deployment.Witnesses.path_positive
#print axioms ControlStack.Deployment.Witnesses.bypass_path_exists
#print axioms ControlStack.Deployment.Witnesses.sink_positive
#print axioms ControlStack.Deployment.Witnesses.database_positive
#print axioms ControlStack.Deployment.Witnesses.runtime_positive
#print axioms ControlStack.Deployment.Witnesses.identity_positive
#print axioms ControlStack.Deployment.Witnesses.uid_collision_refutes
#print axioms ControlStack.Deployment.Witnesses.database_bypass_refutes
#print axioms ControlStack.Deployment.Witnesses.single_checked
#print axioms ControlStack.Deployment.Witnesses.indexed_positive
#print axioms ControlStack.Deployment.Witnesses.indexed_fabricated_post_refutes
#print axioms ControlStack.Deployment.Witnesses.indexed_empty_capture_passes
#print axioms ControlStack.Deployment.Witnesses.sc26_refined
#print axioms ControlStack.Deployment.Witnesses.useful_sc26_deployment_count
#print axioms ControlStack.Deployment.Witnesses.protocol_positive
#print axioms ControlStack.Deployment.Witnesses.one_use_positive
#print axioms ControlStack.Deployment.Witnesses.legal_call_positive
#print axioms ControlStack.Deployment.Witnesses.gate_positive
