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
| Lean-contract-instances | REFUTED | 'certificate_0' depends on axioms: [propext, Quot.sound] 'certificate_1' depends on axioms: [propext, Quot.sound] 'certificate_2' depends on axioms: [propext, Quot.sound] 'certificate_3' depends on axioms: [propext, Quot.sound] 'certificate_4' depends on axioms: [propext, Quot.sound] 'certificate_5' depends on axioms: [propext, Quot.sound] 'certificate_6' depends on axioms: [propext, Quot.sound] 'certificate_7' depends on axioms: [propext, Quot.sound] 'certificate_8' depends on axioms: [propext, Quot.sound] 'certificate_9' depends on axioms: [propext, Quot.sound] 'certificate_10' depends on axioms: [propext, Quot.sound] 'certificate_11' depends on axioms: [propext, Quot.sound] 'certificate_12' depends on axioms: [propext, Quot.sound] 'certificate_13' depends on axioms: [propext, Quot.sound] 'certificate_14' depends on axioms: [propext, Quot.sound] 'certificate_15' depends on axioms: [propext, Quot.sound] 'certificate_16' depends on axioms: [propext, Quot.sound] 'certificate_17' depends on axioms: [propext, Quot.sound] 'certificate_18' depends on axioms: [propext, Quot.sound] 'certificate_19' depends on axioms: [propext, Quot.sound] 'certificate_20' depends on axioms: [propext, Quot.sound] 'certificate_21' depends on axioms: [propext, Quot.sound] 'certificate_22' depends on axioms: [propext, Quot.sound] 'certificate_23' depends on axioms: [propext, Quot.sound] 'certificate_24' depends on axioms: [propext, Quot.sound] 'certificate_25' depends on axioms: [propext, Quot.sound] 'certificate_26' depends on axioms: [propext, Quot.sound] 'certificate_27' depends on axioms: [propext, Quot.sound] 'certificate_28' depends on axioms: [propext, Quot.sound] 'certificate_29' depends on axioms: [propext, Quot.sound] 'certificate_30' depends on axioms: [propext, Quot.sound] 'certificate_31' depends on axioms: [propext, Quot.sound] 'certificate_32' depends on axioms: [propext, Quot.sound] 'certificate_33' depends on axioms: [propext, Quot.sound] 'certificate_34' depends on axioms: [propext, Quot.sound] 'certificate_35' depends on axioms: [propext, Quot.sound] 'certificate_36' depends on axioms: [propext, Quot.sound] 'certificate_37' depends on axioms: [propext, Quot.sound] 'certificate_38' depends on axioms: [propext, Quot.sound] 'certificate_39' depends on axioms: [propext, Quot.sound] 'certificate_40' depends on axioms: [propext, Quot.sound] 'certificate_41' depends on axioms: [propext, Quot.sound] 'certificate_42' depends on axioms: [propext, Quot.sound] 'certificate_43' depends on axioms: [propext, Quot.sound]  |

Kernel configuration obligations (consult Lean-contract-instances status): direct protected-resource authority, nonzero UIDs, all agent/trusted UID separation, exact role counts, runtime match, exact sink/database writer sets, transitive bypass reachability and closure, no unknown/privileged/host-network authority, reused gate/one-use/budget contracts.

Python-only obligations: .

Result lifetime: invalidated by changed mounts, UIDs, credentials, networks, image digests, trusted source hashes, policy/budget, or runtime inventory.
