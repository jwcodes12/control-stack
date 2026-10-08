# SC-17 status

**SPECIFICATION DRAFT / NOT TESTED — NOT DEPLOYMENT_ASSURED.**

Bad event: An agent applies infrastructure changes that violate policy invariants.

Narrow property: Every apply to the modeled resource graph preserves a declared deny constraint.

Falsifier: Issue an unmediated apply or exploit resource kinds missing from the graph.

Next: independently review the statement, select a real honest task and baseline, implement a deny-by-default pre-effect gate if appropriate, and record both bypass attempts and usefulness before promoting any evidence axis.
