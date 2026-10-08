# SC-02 status

**SPECIFICATION DRAFT / NOT TESTED — NOT DEPLOYMENT_ASSURED.**

Bad event: A persistent receiver combines fragments across episodes to reconstruct a supposedly bounded secret.

Narrow property: If every message in one receiver lineage is charged against an atomic durable lifetime budget and no rollback is possible, cumulative views remain bounded.

Falsifier: Run parallel writers or restore a ledger snapshot and obtain more than the declared lifetime transmissions.

Next: independently review the statement, select a real honest task and baseline, implement a deny-by-default pre-effect gate if appropriate, and record both bypass attempts and usefulness before promoting any evidence axis.
