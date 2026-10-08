# SC-14 status

**SPECIFICATION DRAFT / NOT TESTED — NOT DEPLOYMENT_ASSURED.**

Bad event: An agent exceeds cumulative compute, token, network or cost quotas.

Narrow property: A global restart-safe lease counter bounds total authorized spend across all agents.

Falsifier: Exceed budget with concurrent workers, retry after crash, or duplicate a lease.

Next: independently review the statement, select a real honest task and baseline, implement a deny-by-default pre-effect gate if appropriate, and record both bypass attempts and usefulness before promoting any evidence axis.
