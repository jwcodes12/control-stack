# SC-13 correspondence and residual premises

**Narrow model claim:** Recorded dispatcher effects have an audit row appended before or with the effect in the model. Does not protect every monitoring configuration, authenticate originator identity, or prove all workflow execution is mediated.

Original evidence and implementation remain in their existing paths; this bundle is a stable index, not a renamed executable.

| Applicability axis | Recorded state | Missing correspondence or scope |
|---|---|---|
| threat_coverage | UNRESOLVED | Does not assert all logging and shutdown surfaces are outside adversary control. |
| runtime_correspondence | UNRESOLVED | PG test matrix is finite; model-to-executable refinement not established. |
| environment_boundary | ASSUMED | Broker credentials and DB-role isolation must hold in actual environment. |
| lifetime_and_composition | SUPPORTED | Arbitrary modeled interleavings and crashes preserve the audit invariant. |
| usefulness | UNRESOLVED | No representative end-user workload usefulness lower bound. |
| independent_review | UNRESOLVED | Only model and fixture have been examined; independent deployment review missing. |

Evidence digests are pinned by `manifest.json`; matching bytes establish identity only, not empirical independence, comprehensive coverage or trusted provenance.
