# SC-28 status

**SPECIFICATION DRAFT / NOT TESTED — NOT DEPLOYMENT_ASSURED.**

Bad event: Multiple agents each obey local limits but jointly exceed a global safety budget.

Narrow property: All instances use one serializable durable counter and preserve the aggregate bound.

Falsifier: Spend twice via races, split identities or rollback.

Next: independently review the statement, select a real honest task and baseline, implement a deny-by-default pre-effect gate if appropriate, and record both bypass attempts and usefulness before promoting any evidence axis.
