# Remaining F6/F8 review-scoped formal cases

`reviews/family-strengthening/Remaining.lean` adds two **conditional, kernel-checked** classes of arguments that complement `F6F8.lean`.

**F6 (MonitorHistory):** an explicit finite history-indexed distribution of nonnegative outcome weights; attacks, alarms, miss mass, false-alarm mass, and a per-history miss cap. The cumulative miss bound follows only if the conditional miss bound is established **for every history in the finite covered set**. No independence of detectors is claimed or assumed. This is intentionally not a measured calibrated monitor, not an all-histories security theorem, and does not assert normalization or cover unavailable evidence. Per-history probabilities and sampling policy must eventually be grounded by a data/monitor protocol.

**F8 (JointAdmission):** models arbitrary interleavings of requests by multiple numeric agent IDs, a global capacity, a shared spent counter, absorbing HALT, and a count of admitted requests. The budget-preservation and no-post-HALT-admission claims are proved from explicit transition rules rather than using the generic `hJoint` invariant-preservation premise. The positive request witness prevents the trivial reject-all model. Still absent: proof that the Python broker, local filesystem publication, a future OS effect adapter, crashes, other roles, and arbitrary delegated effects follow the abstract transition. HALT during file publication is not modeled as atomic reversal.

Run `lake env lean reviews/family-strengthening/Remaining.lean` with pinned `lean-toolchain`. Printed standard Lean axioms and a green CI test are necessary but insufficient for independent claim-fidelity or runtime assurance.
