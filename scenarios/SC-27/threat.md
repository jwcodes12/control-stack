# SC-27: Tampered evidence and assurance manifests

**Bad event:** An attacker alters or fabricates an assurance record so that an unsupported guarantee is accepted.

**Adversary:** Agent capable of changing workspace files, reports or CI evidence absent protected signing and immutable refs.

**Boundary/scope:** Research proposal for source-bound independent attestations; existing static SHA check is not trusted provenance.

**What would refute the claim:** Substitute a manifest, reuse a receipt from another source revision, forge a recorded proof status, or change the verifier while retaining a green label.

Relevant families: F3, F4. The manifest is an evidence ledger, not a deployment certificate.
