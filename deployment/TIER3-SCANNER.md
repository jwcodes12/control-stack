# Fresh scanner profile

`python3 tools/cstack.py scan --help` documents JSON/YAML scan arguments. Supply
an actual collected runtime inventory and a dedicated output path. Scanning calls
`docker compose config --format json`; it never starts the supplied deployment.
YAML must contain an explicit top-level `x-cstack.roles` service-to-role mapping
because Compose drops service extension keys. JSON service `x-cstack-role` remains
supported. Roles are never inferred from names or environment.

The sibling input directory preserves Compose version, input byte pin, CLI output
hash, canonical semantic inputs, host realpath/stat facts and offline image facts.
Original whitespace and key order are retained as acquisition provenance outside
IR, while canonical semantic inputs determine the IR and bundle. Image export
archive hash is separate because tar timestamps are not semantic authority facts.
The output directory identity and captured observations must be the same when
comparing bytes. A later scan with changed host observations is a new assessment.

Image auditing creates a stopped disposable cstack-r2 container, with network
none, UID 23705 and harmless overridden entrypoint, exports its filesystem and
removes it. It never starts it. Docker-derived observations are not attestation.
The known reference principal policy uses admin 23700, agents 23701/23702,
reviewer 23703 and approver 23704. Different code or principals are UNKNOWN.

Schema 0.1 retains the strict v0 field structure and introduces the version tag
"0.1". `security_ir.migrate.to_v01` validates a v0 object and changes only this tag;
it cannot invent observations or upgrade the assurance of a legacy snapshot.
Both versions reject unknown fields. A kernel certificate is still required for
CONDITIONAL; the Python verifier alone returns UNASSURED with a pending check.

The static dangerous fixtures are never launched. See the gaps document for
unsupported features and the two residual correspondence premises.
