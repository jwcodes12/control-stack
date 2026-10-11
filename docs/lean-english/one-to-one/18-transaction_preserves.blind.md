# Blind semantic target 18: ControlStack.TrustedBroker.transaction_preserves

∀ R s t, Safe s → Step R s t → Safe t

## English under test

`ControlStack.TrustedBroker.transaction_preserves`  — `ControlStack/TrustedBroker.lean:158`
- **Says (plain English):** If a broker state `s` is Safe (spent at most cap; releases at most spent; consumed nonces distinct; every lease used at most its budget) and `t` is obtained from `s` by one model step, then `t` is Safe.
- **Under these hypotheses:** `Safe s` and `Step roles s t`. The step guards (role checks, `Allowed` for release, lease validity on issue) are conditions of the model; they are the content of the proof. The proof for release uses that `Allowed` demands a positive cost, `used + cost <= budget`, `spent + cost <= cap` and that the nonce is not in the consumed list.

