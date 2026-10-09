# Joint reference-broker Lean model — source-only scope

Reconstructed from draft PR #8 after its disconnected-client repair was separately integrated as PR #32 and its full-state Python oracle/mutation tests were integrated or proposed via PR #34.

`ControlStack/TrustedBroker.lean` defines one abstract shared-state relation for stage, content review, lease issue/revoke, approval, committed SQLite release record and absorbing HALT. Its ten kernel-checked-source candidates cover quota invariants, nonce and used-flag coherence, denial/replay, and arbitrary finite transitions including HALT.

**Precise limitation:** A `release` means adding a SQLite row **only**; it is not an OS syscall, network request, payment, model execution or guaranteed external outcome. Authentication, separated and honest roles, serialized atomic SQL transactions, trusted time, no database rollback, no compromised kernel/agent bypass and a faithful source-runtime simulation are *assumptions*, not proven consequences. A permitted deny operation can reject a legitimate action, so no total usefulness guarantee is claimed.

This clean PR retains the 10 proved statements in a source-only generated registry until they have independent statement-fidelity review and scoped evidence. It does **not** import the old PR's generated hashes, frozen receipts or archived CI artifacts. The runtime bridge to `trusted_stack` still needs independent formalization and falsification tests.
