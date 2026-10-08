# SC-01 status

**EXISTING WORK / CONDITIONAL — NOT DEPLOYMENT_ASSURED.**

Bad event: A machine receiver exactly reconstructs a uniform 32-bit secret over its whole five-episode lifetime.

Narrow property: For a complete receiver-visible view with certified cardinality or bounded side-kernel domination, exact recovery is bounded by view mass / 2^32.

Falsifier: Any non-transcript receiver-visible shared-cache/timing signal above the certified side mass refutes the gateway-only premise.

Next: independently review the statement, select a real honest task and baseline, implement a deny-by-default pre-effect gate if appropriate, and record both bypass attempts and usefulness before promoting any evidence axis.

**Preserved negative result:** on the QEMU TCG pair the unchanged 0.25-second gate completed 0/64 baseline and 0/64 mediated lifetimes. The single-host shared-cache counterexample is not nullified by VM resource checks. See `gateway/vm/STATUS.md`.
