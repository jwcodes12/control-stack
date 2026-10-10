# Local file deployment slice

**UNASSURED**

Kernel-checked strict subset of finite model obligations; Python-only obligations listed in bundle. CONDITIONAL retains faithful extraction and full protocol refinement; no deployment-assured result

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
| unknown:agent-a:unknown | UNASSESSED | unlisted-host-mount: /var/tmp/sol-deployment-slice-20261010/deployment-container-state/sink -> /bypass |
| sink-authority:agent-a | REFUTED | writable-sink-mount: protected-sink-mount |
| useful-sink-path | REFUTED | exactly the receiver has the writable sink mount |
| shared-database | CONDITIONAL | broker and receiver must use the same pinned database |
| exclusive-path:agent-a | REFUTED | bypass path reaches sink |
| faithful-extraction | CONDITIONAL | snapshot exhausts actual effective authority, mounts, identities, processes and source/image correspondence; unproved |
| protocol-refinement | CONDITIONAL | RuntimeFaithful.publication : sinkEffects = model.bank assumes full model-runtime correspondence, including actual protocol transitions, exact bytes, unit costs, clock, storage and no rollback; unproved |
| Lean-contract-instances | REFUTED | 'SliceInstance.facts_refuted' does not depend on any axioms 'ControlStack.Deployment.protocol_safe' depends on axioms: [propext, Quot.sound] 'ControlStack.Deployment.one_use' depends on axioms: [propext, Quot.sound] 'ControlStack.Deployment.gate_contract' depends on axioms: [propext, Quot.sound] 'ControlStack.Deployment.broker_contract' depends on axioms: [propext, Quot.sound] 'ControlStack.Deployment.runtime_exclusive' does not depend on any axioms 'ControlStack.Deployment.deployment_safe' depends on axioms: [propext, Quot.sound] 'SliceInstance.contract_checked' depends on axioms: [propext, Quot.sound] 'SliceInstance.one_use_checked' depends on axioms: [propext, Quot.sound]  |

Lean projection subset (consult Lean-contract-instances status): direct sink authority, direct database custody, agent/receiver UID separation, nonzero service UIDs, no unknown edges, no privileged/host-network nodes, receiver writable sink witness, reused gate/one-use/budget contracts.

Python-only obligations: transitive bypass reachability excluding broker/receiver, all agent/trusted and trusted/trusted UID separation, exact role counts, runtime inventory match, exact writable database pair, exact sink writer count.

Result lifetime: invalidated by changed mounts, UIDs, credentials, networks, image digests, trusted source hashes, policy/budget, or runtime inventory.
