# SC-08 status

**SPECIFICATION DRAFT / NOT TESTED — NOT DEPLOYMENT_ASSURED.**

Bad event: A worker executes unauthorized code or downloaded malware.

Narrow property: Only hash-approved executables can be started by the mediated exec transition.

Falsifier: Execute a shell, interpreter, mutable symlink target or inherited binary outside the allowlist.

Next: independently review the statement, select a real honest task and baseline, implement a deny-by-default pre-effect gate if appropriate, and record both bypass attempts and usefulness before promoting any evidence axis.
