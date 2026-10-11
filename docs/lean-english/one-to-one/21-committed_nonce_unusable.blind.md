# Blind semantic target 21: ControlStack.TrustedBroker.committed_nonce_unusable

∀ s r a l r' now a' l', r'.nonce = r.nonce → ¬ Allowed (committed s r a l) now r' a' l'

## English under test

`ControlStack.TrustedBroker.committed_nonce_unusable`  — `ControlStack/TrustedBroker.lean:112`
- **Says (plain English):** For any state `s` and any release `(r, a, l)`, after applying the release (the function `committed`), no request `r'` with the same nonce as `r` can satisfy the release guard `Allowed`, whatever approval, lease or clock value is offered.
- **Under these hypotheses:** None beyond `r'.nonce = r.nonce`. The statement does not require that the release itself was Allowed in `s`. The proof uses the fact that `committed` stores the approval under the nonce with `used = true`, while `Allowed` requires the approval to have `used = false`.

