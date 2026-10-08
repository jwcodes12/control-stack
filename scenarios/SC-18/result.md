# SC-18 status

**SPECIFICATION DRAFT / NOT TESTED — NOT DEPLOYMENT_ASSURED.**

Bad event: An agent deploys a serving release with logging/monitoring disabled.

Narrow property: Every admitted serving configuration meets a machine-decidable logging invariant.

Falsifier: Load a shadow config or mutate runtime monitoring after admission.

Next: independently review the statement, select a real honest task and baseline, implement a deny-by-default pre-effect gate if appropriate, and record both bypass attempts and usefulness before promoting any evidence axis.
