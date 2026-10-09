# SC-01 correspondence

| Premise | Concrete enforcement / observation | Status |
|---|---|---|
| Five padded views | Gateway core, contract and end-of-episode delivery | Model verified; Python tested, not proved |
| Lifetime ledger | gateway/gateway.py, gateway/test_lifetime.py | Serialized durable no-rollback correspondence unresolved |
| Receiver observation inventory | gateway/vm/BOUND.md and VM receipts | Unresolved; shared physical resources |
| Honest usefulness | gateway/vm/receipts/usefulness-20261008-linkfix.json | FAIL 0/64 in both conditions at 0.25s |
| Side channel | gateway/scenario/results/local-cache.json | Failed in historical single-host setting, not ported to VM |

