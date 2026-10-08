# SC-04 status

**SPECIFICATION DRAFT / NOT TESTED — NOT DEPLOYMENT_ASSURED.**

Bad event: A receiver learns a secret from logs, errors, status, scheduling or wall-clock timing outside the nominated message schema.

Narrow property: If all receiver-visible diagnostics/timing are constant or included in a finite observation alphabet, the full transcript bound counts them.

Falsifier: Encode a secret bit through a diagnostic exit code, page-cache timing or heartbeat arrival.

Next: independently review the statement, select a real honest task and baseline, implement a deny-by-default pre-effect gate if appropriate, and record both bypass attempts and usefulness before promoting any evidence axis.
