# SC-01 falsification plan (NOT RUN)

1. Preserve the exact threat contract and baseline first.
2. Create a negative control: Exhibit a receiver-visible channel absent from the finite transcript, a ledger rollback, variable episode count, or statistically supported recovery beyond the budget.
3. Check that the policy detects/blocks it *before* its effect, where applicable.
4. Probe restarts, concurrent agents, inherited authority, alternate channels and policy tampering where in scope.
5. Record independent source/configuration hashes, outcomes, failures and honest usefulness, without turning a null test result into a proof.

Existing historical tests remain in the referenced implementation directories. No experiments are triggered by this plan.
