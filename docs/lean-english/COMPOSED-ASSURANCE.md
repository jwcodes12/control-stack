# Accepted deployment: combined broker assurance

**Model-written and model-reviewed; no independent human review.**
This document adds a conditional, kernel-checkable composition rather than a deployment certification.

`ComposedAssurance.accepted_joint_claim` uses *one* shared set of hypotheses:
`Accepted d`, `ExtractionFaithful d r actualEdges`, and
`BrokerProtocolRefinement d R cap t sinkNonces`. It concludes:

1. Every *captured* actual sink edge, whether labeled authority or not, has the receiver as sole source and is a write edge.
2. The receiver UID is not a broker-model agent.
3. Published nonces have no duplicates and the nonce count is at most the joint cap.
4. Each published nonce has a **currently retained, used** broker approval; its signer and agent have the named roles; its staged digest has a currently retained reviewer role; and its lease is currently owned by that agent.

`all_hypotheses_satisfiable` and `witness_combined_nonce_and_provenance` provide one nonempty cap-1 abstract deployment witness for all hypotheses and the resulting conclusion. This is a model witness, not real container evidence.

## SC-26 vs broker role-model consistency

The SC-26-based `deployment_safe` and `TrustedBroker`-based `deployment_broker_safe` **cannot be composed as the same protocol without an additional mapping theorem**. SC-26 has `Roles` with finite lists of agent/approver/admin UIDs and a distinguished `gate`; `TrustedBroker.Roles` has four role predicates, including a reviewer, and a separation proof. A list-based identity and a predicate-based identity are not definitionally equal.

The SC-26 publication premise is **equality** of observed `List (Nat × SC26.Tx)` bank events and an SC-26 abstract bank list. The broker publication premise is an admission-order `List.Sublist sinkNonces.reverse t.consumed`; it explicitly allows admission without publication and carries **no digest/destination event record**. The cap counts SC-26 unit-amount transactions under a `unitCosts` premise, whereas `TrustedBroker` increments `spent` by positive request cost and bounds the release count by spent.

At the example `clean` witness, receiver UID 23700 and agent UIDs 23701/23702 match the intended roles, but numerical agreement of sample UIDs does **not** supply the missing state/event correspondence. Do not infer that an arbitrary SC-26 `ProtocolRefinement` proves a `TrustedBroker.BrokerProtocolRefinement`, or vice versa.

## What remains assumed, not proved

Faithful authority extraction, actual role and peer identity capture, complete mediation, atomic external effects, trust in the broker implementation, non-rollback storage, and exact released file-byte/destination provenance are **not** established. `Provenance` is a present-state claim; historical review identity or exact release destination can be lost. Theorem correctness and English one-to-one auditing are pending. G1–G7 (161 claims) have never been one-to-one checked.
