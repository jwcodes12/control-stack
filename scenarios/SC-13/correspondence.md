# SC-13 correspondence

| Premise | Evidence / enforcement | Status |
|---|---|---|
| Audit before effect record | AuditDispatch theorem and setup_v1.sql | Model verified; SQL tested historically |
| Exclusive dispatcher | Broker/worker origin separation | UNRESOLVED; application source may retain credentials |
| Completion vs dispatch | Both event timestamps/records | Completion-time property NOT PROVED |
| Exactly-once external action | Replay/reconciliation | NOT PROVED; record uniqueness is weaker |

