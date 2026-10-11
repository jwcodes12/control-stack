# Local file deployment slice

**UNASSURED**

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
| unknown:agent-a:unknown | UNASSESSED | unlisted-host-mount: /var/tmp/sol-deployment-slice-20261010/deployment-container-state/sink -> /bypass |
| sink-authority:agent-a | REFUTED | writable-sink-mount: protected-sink-mount |
| useful-sink-path | REFUTED | exactly the receiver has the writable sink mount |
| shared-database | CONDITIONAL | broker and receiver must use the same pinned database |
| exclusive-path:agent-a | REFUTED | bypass path reaches sink |
| faithful-extraction | CONDITIONAL | snapshot exhausts actual effective authority, mounts, identities, processes and source/image correspondence; unproved |
| protocol-refinement | CONDITIONAL | ProtocolRefinement.publication : sinkEffects = model.bank assumes full model-runtime correspondence, including actual protocol transitions, exact bytes, unit costs, clock, storage and no rollback; unproved |
| Lean-contract-instances | UNASSESSED | run tools/check_deployment_lean.py against this exact IR to kernel-check facts and contracts; source names alone are not proof |

Kernel configuration obligations (consult Lean-contract-instances status): direct protected-resource authority, nonzero UIDs, all agent/trusted UID separation, exact role counts, runtime match, exact sink/database writer sets, transitive bypass reachability and closure, no unknown/privileged/host-network authority, reused gate/one-use/budget contracts.

Python-only obligations: .

Result lifetime: invalidated by changed mounts, UIDs, credentials, networks, image digests, trusted source hashes, policy/budget, or runtime inventory.
