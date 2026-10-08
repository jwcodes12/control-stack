# SC-20 status

**SPECIFICATION DRAFT / NOT TESTED — NOT DEPLOYMENT_ASSURED.**

Bad event: An agent changes a training dataset or hidden evaluation labels.

Narrow property: Only content-addressed approved dataset versions can be consumed; semantic purity is not implied.

Falsifier: Train on an unreviewed shard or inject harmful samples into approved input.

Next: independently review the statement, select a real honest task and baseline, implement a deny-by-default pre-effect gate if appropriate, and record both bypass attempts and usefulness before promoting any evidence axis.
