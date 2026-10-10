# Local file deployment slice

**UNASSURED**

Kernel-checked finite model candidate; CONDITIONAL retains runtime faithfulness; no deployment-assured result

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
| unknown:agent-a:unknown | UNASSESSED | unknown-feature: unsupported service feature: devices |
| useful-sink-path | CONDITIONAL | exactly the receiver has the writable sink mount |
| shared-database | CONDITIONAL | broker and receiver must use the same pinned database |
| IR-faithfulness | CONDITIONAL | snapshot exhausts scoped effective authority and faithfully abstracts trusted protocol, Linux identity/confinement, storage and sink publication; not proved |
| Lean-contract-instances | REFUTED | 'SliceInstance.facts_refuted' does not depend on any axioms 'ControlStack.Deployment.protocol_safe' depends on axioms: [propext, Quot.sound] 'ControlStack.Deployment.one_use' depends on axioms: [propext, Quot.sound] 'ControlStack.Deployment.gate_contract' depends on axioms: [propext, Quot.sound] 'ControlStack.Deployment.broker_contract' depends on axioms: [propext, Quot.sound] 'ControlStack.Deployment.runtime_exclusive' does not depend on any axioms 'ControlStack.Deployment.deployment_safe' depends on axioms: [propext, Quot.sound] 'SliceInstance.contract_checked' depends on axioms: [propext, Quot.sound] 'SliceInstance.one_use_checked' depends on axioms: [propext, Quot.sound]  |
| native-reference-boundary | TESTED_BOUNDARY | Independent raw sink evidence at deployment-evidence/runtime-vm/slice-runtime; confined two-agent budget/replay, HALT during publication, writable-sink and UID-collision negatives. Native Linux guest test of pinned sources; does not attest this Compose inventory. |

Result lifetime: invalidated by changed mounts, UIDs, credentials, networks, image digests, trusted source hashes, policy/budget, or runtime inventory.
