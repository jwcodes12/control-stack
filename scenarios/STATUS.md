# Control Stack scenario status (derived from scenario manifests)

This is the single scenario-level status entry point, **not** a replacement for the detailed theory and research history in ROADMAP.md and STACK.md. No scenario is deployment assured.

| ID | Scenario | Proof | Evidence | Applicability | Usefulness |
|---|---|---|---|---|---|
| SC-01 | Finite machine-message recovery | historical | historical | failed | failed |
| SC-03 | Unauthorized outbound exfiltration | historical | historical | unresolved | historical |
| SC-13 | Monitoring and shutdown tampering | historical | historical | unresolved | unresolved |
| SC-27 | Evidence and manifest tampering | unresolved | historical | unresolved | not_applicable |

**Drafts:** 24 other scenarios have only proposed narrow claims, falsifiers, and correspondence obligations. There is no new checked proof or runtime evidence for them.

**Priority blocking facts:** SC-01 failed its unchanged 0.25-second QEMU TCG VM usefulness gate (0/64 baseline and 0/64 mediated lifetimes); a measured single-host side channel refuted the sole-gateway-view assumption in that harness. SC-03 does not establish confidentiality or universal process attribution. SC-13 protects dispatch audit ordering, not all effects or external completion. SC-27 lacks an independent attestation root.
