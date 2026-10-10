# IR schema v0

The executable normative schema is `validator.py::validate`. Inputs have exactly
`version`, `claim`, `sources`, `nodes`, `edges`, and `snapshot`. Version is integer
0 and claim is `local-file-two-agent-v0`. Extra or missing fields fail validation.

Every node has a unique nonempty `id`, `type` (service/sink/database/unknown),
`facts`, and `provenance`. Resources have empty facts. Services carry role, UID
(integer or null), image string, privileged/host_network booleans, env_names list,
and runtime_match (MATCH/MISSING/DRIFT). Every edge has from/to node IDs,
capability (write/read/call/escape/credential/opaque), reachability
(PRESENT/ABSENT/UNKNOWN), authorization (PERMITTED/FORBIDDEN/UNKNOWN), provenance,
and reason. Duplicate edge triples or dangling endpoints fail validation.

Every provenance has exactly source (nonempty path), sha256 (64 lowercase hex),
and kind (DECLARED/STATIC_INFERRED/RUNTIME_OBSERVED/ENFORCED_TESTED/UNKNOWN).
Node/edge provenance must resolve to a pinned source entry. UNKNOWN evidence may
only support UNKNOWN reachability. ABSENT requires STATIC_INFERRED or
ENFORCED_TESTED evidence; absence of observations cannot establish absence of a
path. Authorization never removes a reachable path. Contradictory duplicate
edges are rejected rather than choosing the favorable assertion.

Snapshot pins Compose, runtime inventory, broker and receiver hashes, a positive
shared budget and absolute protected sink/database sources. The collector uses
hashes of exact input bytes and trusted files, no timestamps or nondeterministic
identifiers. Identical inputs with identical source path names give identical
outputs. It reads environment keys only and emits no environment values. Runtime
facts are selected caller-provided records; the label does not attest authenticity.
The residual faithfulness premise covers source path aliases and dishonest input.

Golden fixtures live here; source fixtures and planted changes live in
`examples/compose-two-agent`. Regenerate with `python3 tools/build_deployment_fixtures.py`.
