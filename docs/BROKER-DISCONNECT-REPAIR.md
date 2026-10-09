# Trusted broker disconnect repair (2026-10-09)

Reconstructed from PR #8 onto current main, without its conflicting generated indexes or unreviewed joint Lean model.

* The Unix socket service now catches a failed reply write after the request has been processed; it does not terminate or reverse an already committed SQLite release.
* Bootstrap connections and failed-open connections are explicitly closed.
* Linux peer-credential regression exercises eight malformed clients closing before response, then a valid release whose acknowledgment is lost; checks the durable release count and denial of nonce replay.

**Assurance scope:** this repairs a crash/availability gap in the reference process only. Release is a SQLite record, not an effect on a real external system. Actual-effect exclusivity, crash durability under real power loss, UID/kernel trust, SQL-to-Lean simulation, and independent human review remain unresolved. The original PR #8's joint model and mutation suite still require a separate conflict-free integration and must not be silently marked completed.
