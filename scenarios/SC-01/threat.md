# SC-01: Lifetime-bounded exact secret recovery

**Bad event:** A machine receiver recovers a uniform 32-bit secret beyond the specified 2^-16 exact-recovery bound.

**Adversary:** Adaptive colluding sender and machine receiver with shared seed; persistent lineage and potentially side observations.

**Boundary/scope:** Five-episode eight-fault repair fixture; single-host and VM experimental environments are distinct.

**What would refute the claim:** Exhibit a receiver-visible channel absent from the finite transcript, a ledger rollback, variable episode count, or statistically supported recovery beyond the budget.

Relevant families: F2, F8. The manifest is an evidence ledger, not a deployment certificate.
