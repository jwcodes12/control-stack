# SC-27 correspondence and residual premises

**Narrow model claim:** Only the append-only audit dispatch subclaim is currently modeled. Signed, hash-bound manifest attestation and independent source verification for assurance bundles are NOT proved or enforced.

Original evidence and implementation remain in their existing paths; this bundle is a stable index, not a renamed executable.

| Applicability axis | Recorded state | Missing correspondence or scope |
|---|---|---|
| threat_coverage | UNRESOLVED | Artifact forgery is not equivalent to database audit dispatch. |
| runtime_correspondence | UNRESOLVED | No independently verified attestation chain. |
| environment_boundary | UNRESOLVED | CI signing/isolation and immutable evidence storage not established. |
| lifetime_and_composition | UNRESOLVED | No cross-commit append-only binding theorem. |
| usefulness | UNRESOLVED | No representative evidence generation utility measure. |
| independent_review | UNRESOLVED | No independent chain-of-custody review. |

Evidence digests are pinned by `manifest.json`; matching bytes establish identity only, not empirical independence, comprehensive coverage or trusted provenance.
