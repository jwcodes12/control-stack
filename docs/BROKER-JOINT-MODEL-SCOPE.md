# Joint broker model — clean Lean-only integration
**Source:** Reconstructed from draft PR #8, limited to `ControlStack/TrustedBroker.lean` and pinned checks, with no runtime/frozen-reference modifications.

## Boundaries
The joint model represents a reference SQLite broker transaction relation for artifacts, reviews, user approvals, nonce consumption, leases, quotas, revocation, and absorbing HALT. It uses source-level predicates for authentic UID identity, digest integrity and atomic commit. Ten Lean lemmas/theorems cover safety, nonce history coherence, denial of nonce reuse, preservation and HALT under relational closure.

**Critical gaps:** No verified Python-to-Lean/SQL correspondence, OS/kernel identity proof, comprehensive real-effect mediation, trusted clock or rollback handling, human review quality, or operational catastrophe bound. The protected harnesses, preregistrations, evidence and `ControlStack/EgressGate.lean` remain untouched. Record the model as SOURCE_ONLY until independently reviewed.

Broker disconnect and SQLite mutation tests from old PR #8 were separately reconstructed and merged via #32 and #34. This branch only preserves the distinct formal joint model. Run GitHub Actions at exact new head before merging.
