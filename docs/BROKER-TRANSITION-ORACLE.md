# Broker transition differential test and adversarial mutations

Reconstructed from the Python-only oracle and mutation components of old draft PR #8, on a modern main already containing the separately merged dropped-acknowledgment repair (#32).

The independent Python oracle compares admission outcomes and all persisted SQLite table states after bounded transitions and restart. Six weakened authorization guards are tested as negatives. The seventh mutation removes disconnect-error isolation from the broker and is exercised through live Linux peer credentials.

**Not a Lean/SQL refinement or a deployed-system proof:** the oracle shares some modeling choices with the implementation; bounded traces do not cover all possible executions, malicious kernel identities, rollback, power loss or real external effects. Keep the broader joint-state Lean theorem of PR #8 as a separate unmerged obligation until kernel checking and index regeneration on current main.
