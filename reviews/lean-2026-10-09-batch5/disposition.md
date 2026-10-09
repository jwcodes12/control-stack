# Disposition: Gemini 3.1 Pro review of Measured, EscrowBudgetMsg, SC26LossyLiveness and TrustRoot

| File | Finding | Disposition |
|---|---|---|
| EscrowBudgetMsg | None ("sound"). | — |
| SC26LossyLiveness | None ("sound"). | — |
| Measured | The sampling-model premise in `ofMeasured` has Lean content `True`. | **By design, stated here.** Correspondence premises name real-world links that Lean cannot express; they are carried in the ledger so they cannot be hidden, and are not discharged. The model's own independence (a product space) is formal in `measured_prod`. No change. |
| Measured | `measuredRecallLedger` is hand-typed, not derived from `ofMeasured`. | **Valid; fix in progress.** The ledger will be proved equal (by `rfl`) to the ledger that `ofMeasured` produces for the instance, following `Cert.stack_ledger_eq`. |
| TrustRoot | `model_runtime_correspondence` is discharged by SC-26's refinement for every scenario. | **Valid; fix in progress.** Each scenario's discharge will cite its own refinement (SC-16/18/25/26/27/28). Scenarios without one reduce to `implementation_conformance` only. Root sets are expected to be unchanged, since theorem edges don't add roots, but citations become scenario-specific. |
| Cross-cutting | Ledgers sometimes carry `True`-content premises. | **Agreed that this is the boundary.** Every such premise is typed (correspondence/measurement/environment/organisational) and listed in `ASSURANCE-LEDGER.md` and the trust-root tables. None is presented as proved. |
