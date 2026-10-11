# Guard necessity and missing protection audit

**MODEL-ONLY; PARTIAL:** model-written/model-reviewed; no independent human review. The single-guard mutation predicate `AllowedExcept` retains all twenty other clauses. Five deletion witnesses and the two group-independence theorems are compiled with the root project. A negative result in this table means **no countermodel established**, not verified redundancy.

## TrustedBroker.Allowed (21 clauses)

| # | Named condition | Result against Safe / Coherent / halt | Kernel evidence / qualification |
|---|---|---|---|
| 0 | `not_halted` | necessary for halted-absorbing (guard 0; modeled release after HALT) | `GuardNecessity.no_halt_guard_breaks_absorption` plus `..._other_twenty` |
| 1 | `caller_is_agent` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 2 | `stored_approval` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 3 | `approval_unused` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 4 | `same_digest` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 5 | `same_destination` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 6 | `same_agent` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 7 | `same_lease` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 8 | `signer_is_approver` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 9 | `approval_unexpired` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 10 | `stored_lease` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 11 | `lease_owned` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 12 | `lease_active` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 13 | `lease_unexpired` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 14 | `positive_cost` | necessary for Safe: releases ≤ spent | `GuardNecessity.no_positive_cost_guard_breaks_safe` plus `..._other_twenty` |
| 15 | `within_lease_budget` | necessary for Safe: lease budget | `GuardNecessity.no_local_budget_guard_breaks_safe` plus `..._other_twenty` |
| 16 | `within_joint_budget` | necessary for Safe: joint cap | `GuardNecessity.no_joint_budget_guard_breaks_safe` plus `..._other_twenty` |
| 17 | `artifact_staged` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 18 | `artifact_intact` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 19 | `reviewed_digest` | no countermodel found: redundant for the listed invariant or protects authorization/provenance not expressed there | Not established necessary here; do not remove the guard |
| 20 | `nonce_not_consumed` | necessary for Safe: nonce Nodup (Safe-only prestate; not coherent) | `GuardNecessity.no_nonce_guard_breaks_safe` plus `..._other_twenty` |

**Qualification for nonce history:** the nonce countermodel uses a `Safe` prestate that is *not* `Coherent`. `nonce_history_redundant` proves that this explicit ghost-history guard follows from coherent used-flag bookkeeping and an unused approval. The modeled countermodel therefore tests the advertised `Safe` alone, not a reachable coherent broker trace.

**Qualification for other fields:** many check provenance and caller/role linkage that `Safe` does not express. In particular, dropping a digest match may permit inappropriate publication while leaving all numeric invariants intact. Absence of a countermodel to `Safe` is not evidence that the field can safely be deleted.

## BaseAccepted (7) and WritersChecked (6)

`GuardNecessity.avoided_paths_from_nobypass` shows that **NoBypass alone** establishes the two avoided-path conclusions, independently of *all* BaseAccepted and WritersChecked conditions. For an authority sink edge, `sink_from_base_without_writers` needs no WritersChecked field; `sink_from_writers_without_base` needs no BaseAccepted field. These are *property-relative redundancy* statements, not redundancy in the deployment acceptance gate.

| Group | Named condition | Against accepted_no_avoided_path / exclusive_sink |
|---|---|---|
| BaseAccepted | `edges_known` | no countermodel found: path follows from NoBypass; sink writer is covered by WritersChecked if this field is deleted |
| BaseAccepted | `sink_authority_only_receiver` | no countermodel found: path follows from NoBypass; sink writer is covered by WritersChecked if this field is deleted |
| BaseAccepted | `database_authority_custody` | no countermodel found: path follows from NoBypass; sink writer is covered by WritersChecked if this field is deleted |
| BaseAccepted | `no_privileged_or_host_network` | no countermodel found: path follows from NoBypass; sink writer is covered by WritersChecked if this field is deleted |
| BaseAccepted | `agents_uid_distinct_from_receiver` | no countermodel found: path follows from NoBypass; sink writer is covered by WritersChecked if this field is deleted |
| BaseAccepted | `receiver_can_write_sink` | no countermodel found: path follows from NoBypass; sink writer is covered by WritersChecked if this field is deleted |
| BaseAccepted | `positive_uids` | no countermodel found: path follows from NoBypass; sink writer is covered by WritersChecked if this field is deleted |
| WritersChecked | `sink_edges_receiver_writes` | no countermodel found: path follows from NoBypass; authority sink writer follows from BaseAccepted if this field is deleted |
| WritersChecked | `database_edges_custody` | no countermodel found: path follows from NoBypass; authority sink writer follows from BaseAccepted if this field is deleted |
| WritersChecked | `unique_sink_writer` | no countermodel found: path follows from NoBypass; authority sink writer follows from BaseAccepted if this field is deleted |
| WritersChecked | `two_database_writers` | no countermodel found: path follows from NoBypass; authority sink writer follows from BaseAccepted if this field is deleted |
| WritersChecked | `broker_database_writer_exists` | no countermodel found: path follows from NoBypass; authority sink writer follows from BaseAccepted if this field is deleted |
| WritersChecked | `receiver_database_writer_exists` | no countermodel found: path follows from NoBypass; authority sink writer follows from BaseAccepted if this field is deleted |

**Not proved:** individually generated altered-IR witness instances for all 13 graph fields; global minimality of the 21 broker clauses; runtime/SQLite necessity; provenance protection of each non-numeric broker guard. The listed group independence is stronger than their one-at-a-time redundancy for the two specifically named conclusions, but says nothing about their other acceptance obligations.
