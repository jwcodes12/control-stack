# Local file deployment slice

**CONDITIONAL**

configuration/model candidate; skipped kernel check means UNASSURED. Lean rechecks all finite configuration obligations; faithful extraction and protocol refinement remain unproved

| Premise | Status | Evidence / limitation |
|---|---|---|
| supported-roles | CONDITIONAL | two agents, one named broker and one named receiver required |
| identity-separation | CONDITIONAL | distinct agent/trusted UIDs; only broker/receiver share trusted owner; trusted-role-uid-collision on failure |
| runtime-snapshot:agent-a | CONDITIONAL | MATCH |
| runtime-snapshot:agent-b | CONDITIONAL | MATCH |
| runtime-snapshot:approver | CONDITIONAL | MATCH |
| runtime-snapshot:broker | CONDITIONAL | MATCH |
| runtime-snapshot:receiver | CONDITIONAL | MATCH |
| runtime-snapshot:reviewer | CONDITIONAL | MATCH |
| useful-sink-path | CONDITIONAL | exactly the receiver has the writable sink mount |
| shared-database | CONDITIONAL | broker and receiver must use the same pinned database |
| faithful-extraction | CONDITIONAL | snapshot exhausts actual effective authority, mounts, identities, processes and source/image correspondence; unproved |
| protocol-refinement | CONDITIONAL | ProtocolRefinement.publication : sinkEffects = model.bank assumes full model-runtime correspondence, including actual protocol transitions, exact bytes, unit costs, clock, storage and no rollback; unproved |
| Lean-contract-instances | PROVEN_IN_MODEL | 'SliceInstance.facts_checked' depends on axioms: [propext, Quot.sound] 'ControlStack.Deployment.protocol_safe' depends on axioms: [propext, Quot.sound] 'ControlStack.Deployment.one_use' depends on axioms: [propext, Quot.sound] 'ControlStack.Deployment.gate_contract' depends on axioms: [propext, Quot.sound] 'ControlStack.Deployment.broker_contract' depends on axioms: [propext, Quot.sound] 'ControlStack.Deployment.runtime_exclusive' depends on axioms: [propext, Quot.sound] 'ControlStack.Deployment.deployment_safe' depends on axioms: [propext, Quot.sound] 'SliceInstance.contract_checked' depends on axioms: [propext, Quot.sound] 'SliceInstance.one_use_checked' depends on axioms: [propext, Quot.sound]  |

Kernel configuration obligations (consult Lean-contract-instances status): direct protected-resource authority, nonzero UIDs, all agent/trusted UID separation, exact role counts, runtime match, exact sink/database writer sets, transitive bypass reachability and closure, no unknown/privileged/host-network authority, reused gate/one-use/budget contracts.

Python-only obligations: .

Result lifetime: invalidated by changed mounts, UIDs, credentials, networks, image digests, trusted source hashes, policy/budget, or runtime inventory.
