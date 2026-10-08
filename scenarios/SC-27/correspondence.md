# SC-27 correspondence

| Premise | Concrete mechanism | Status |
|---|---|---|
| Manifest file integrity | SHA bindings in tools/check_scenarios.py | Static check only; attacker can edit source and digest together |
| Trusted proof provenance | Protected CI identity and signed artifact | NOT IMPLEMENTED |
| Receipt authenticity | Run IDs + execution environment + independent signature | NOT IMPLEMENTED |
| Reviewer promotion | Independent explicit decision | REQUIRED, never automated |

