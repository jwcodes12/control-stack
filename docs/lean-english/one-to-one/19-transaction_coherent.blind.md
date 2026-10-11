# Blind semantic target 19: ControlStack.TrustedBroker.transaction_coherent

∀ R s t, Coherent s → Step R s t → Coherent t

## English under test

`ControlStack.TrustedBroker.transaction_coherent`  — `ControlStack/TrustedBroker.lean:201`
- **Says (plain English):** Call a broker state "coherent" when a nonce is in the consumed-history list exactly when the approval stored under that nonce exists and is marked used. A single model step preserves coherence.
- **Under these hypotheses:** `Coherent s` and `Step roles s t`. For the approve step the proof uses that the nonce was fresh and the new approval is unused; for release both the history and the flag are updated together.

