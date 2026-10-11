**SUPERSEDED (Tier 9, T4.4 finished): see `deployment/TIER4-TRANSCRIPT.md`.** The text below is the original blocked report, kept because the three failed attempts are evidence.

# Concrete transcript replay did not pass

The generic IndexedBrokerTable and indexed_receipts_sound theorem passed the
kernel. Finite state identifiers reference complete model states and every table
transition must have a TrustedBroker proof. This avoids a false decidable-equality
instance for function-valued broker states.

The attempted concrete instantiation used the ten recorded clean-case Tier 2
requests/responses and Compose numeric callers. Digest mapping checked the actual
staged bytes. Timestamp 0 was only an abstract feasible clock witness, not a
reported server clock; neither completeness nor authentic timing was established.

Three compilation attempts failed. Attempt 1 could not synthesize role predicates'
decidability; attempt 2's tactic expansion failed on unchanged or already-solved
goals; attempt 3 left transition guards unsolved, including s0.halted = false,
lease used/budget and release quota checks. Exact diagnostics and failed generated
source/generator are retained under deployment/runs/tier4. The kernel diagnostic
mentions sorryAx because Lean substitutes error terms after failed elaboration;
no failed theorem is installed in ControlStack or claimed as verified.

T4.4 is BLOCKED under the handoff's three-attempt limit. No concrete transcript,
omitted-event demonstration or receipt acceptance is claimed. Existing abstract
CheckedTrace omission examples remain source-only and do not complete this task.
