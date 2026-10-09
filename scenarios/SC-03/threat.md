# SC-03: Pinned immediate-peer egress confinement

**Bad event:** An untrusted agent initiates an unauthorized immediate outbound peer connection.

**Adversary:** Untrusted sandbox process with attempted direct socket and tool requests, subject to modeled Linux isolation.

**Boundary/scope:** Pinned test-only loopback topology; immediate TCP peer, not confidentiality or tunnel contents.

**What would refute the claim:** One unaccounted destination, inherited socket, policy-tamper effect, host deputy, or gateway-bypass connection disproves the specific boundary.

Relevant families: F1, F3. The manifest is an evidence ledger, not a deployment certificate.
