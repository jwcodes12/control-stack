# Deployment R2 queue

Source: `/var/tmp/sol-eval/HANDOFF-SOL-TO-R2.md`. This supersedes the earlier follow-up.
Tier 1 base: `a3bab7574e477f1ce7e130a7f81b845267efd99e`, draft PR #45, 25 CI successes / 2 expected skips.
No merging. Frozen artifacts and scenario statuses remain unchanged.

ID | status | evidence path or reason
---|---|---
T1.1 | DONE | Existing tested mount/verdict regression in tools/test_deployment_slice.py and deployment-evidence/matrix/
T1.2 | DONE | Existing tested mount/verdict regression in tools/test_deployment_slice.py and deployment-evidence/matrix/
T1.3 | DONE | Existing tested mount/verdict regression in tools/test_deployment_slice.py and deployment-evidence/matrix/
T1.4 | DONE | Existing tested mount/verdict regression in tools/test_deployment_slice.py and deployment-evidence/matrix/
T1.5 | DONE | Existing tested mount/verdict regression in tools/test_deployment_slice.py and deployment-evidence/matrix/
T1.6 | DONE | ControlStack/Deployment/Contracts.lean; lean-build-attempt2.txt PASS
T1.7 | DONE | deployment/evidence/tier1/differential.json: 26 fixtures + 250 mutations, zero differences, 276 kernel certificates
T1.8 | DONE | deployment/evidence/tier1/monotonicity.json: 520 seeded strict additions, zero false improvements
T1.9 | DONE | ExtractionFaithful and ProtocolRefinement in Contracts.lean; claim/status/report updated
T1.10 | DONE | Existing tested mount/verdict regression in tools/test_deployment_slice.py and deployment-evidence/matrix/
T2.1 | TODO | Not yet started; tier order applies
T2.2 | TODO | Not yet started; tier order applies
T2.3 | TODO | Not yet started; tier order applies
T2.4 | TODO | Not yet started; tier order applies
T2.5 | TODO | Not yet started; tier order applies
T2.6 | TODO | Not yet started; tier order applies
T2.7 | TODO | Not yet started; tier order applies
T3.1 | TODO | Not yet started; tier order applies
T3.2 | TODO | Not yet started; tier order applies
T3.3 | TODO | Not yet started; tier order applies
T3.4 | TODO | Not yet started; tier order applies
T3.5 | TODO | Not yet started; tier order applies
T3.6 | TODO | Not yet started; tier order applies
T4.1 | TODO | Not yet started; tier order applies
T4.2 | TODO | Not yet started; tier order applies
T4.3 | TODO | Not yet started; tier order applies
T4.4 | TODO | Not yet started; tier order applies
T4.5 | TODO | Not yet started; tier order applies
T5.1 | TODO | Not yet started; tier order applies
T5.2 | TODO | Not yet started; tier order applies
T5.3 | TODO | Not yet started; tier order applies
T6.1 | TODO | Not yet started; tier order applies
T6.2 | TODO | Not yet started; tier order applies
T6.3 | TODO | Not yet started; tier order applies
T7.1 | TODO | Not yet started; tier order applies
T7.2 | TODO | Not yet started; tier order applies
T7.3 | TODO | Not yet started; tier order applies
T7.4 | TODO | Not yet started; tier order applies
T8.1 | TODO | Not yet started; tier order applies
T8.2 | TODO | Not yet started; tier order applies
T8.3 | TODO | Not yet started; tier order applies
T8.4 | TODO | Not yet started; tier order applies
T8.5 | TODO | Not yet started; tier order applies
T8.6 | TODO | Not yet started; tier order applies
G1 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G2 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G3 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G4 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G5 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G6 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G7 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G8 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G9 | GATED | Owner/resource prerequisite listed in handoff; not attempted

Tier 1 local checks: exact-fixture Lean + full differential 2 PASS (362.740s); slice 13 PASS; runtime 17 with 2 host-Landlock skips; evidence 3 PASS; generated registry/catalog/overview/results/ledger/trust-root checks PASS. Frozen EgressGate SHA remains b491ec0accf6be75e7355667012b173760c5278b7180a31f4c4990ffad9f2af6. Final-head CI pending; no R2 claim.
