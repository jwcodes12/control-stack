# SC-03 correspondence

| Premise | Enforcement/evidence | Status |
|---|---|---|
| Authorized peer table | EgressGate lookup + egress/proxy.py | Model theorem; runtime fidelity conditional |
| Process authority | Namespace validator, launch controls | Fixture observed; general host assumption |
| Socket attribution | Host tracing and packet mirrors | Bounded loopback calibration only |
| Tamper resistance | EgressGate.tamperPolicy is a no-op | **Assumed by the model, not enforced by definition at runtime** |

