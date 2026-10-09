### ControlStack/Core/Measured.lean
Verdict: Contains defects (vacuity, overclaims).
Defects:
1. Location: `ProbCert.ofMeasured`
   Problem: Vacuous premise. The certificate string claims the measurement samples i.i.d. from the deployment law and is independent of deployment, but the formal proposition bound to this `.correspondence` premise is exactly `True`. It requires no proof and is trivially satisfied by any checker.
   Instance: `⟨"sampling model: " ++ procedure ++ " samples i.i.d. from the deployment law, independent of deployment", .correspondence, True⟩`
   Fix: Replace `True` with a formal proposition linking the abstract measurement measure `μm` and the deployment measure `μd`, or formulate it as an explicit unproved hypothesis that the deployment environment must supply.
2. Location: `measuredRecallLedger`
   Problem: Faked ledger / Overclaim. The header explicitly claims this ledger is "`ofMeasured` applied to the recall measurement", but it is actually a manually typed, hardcoded list of strings. It bypasses the `ProbCert.ofMeasured` function entirely and is formally disconnected from the `measured_recall_example` theorem.
   Instance: `def measuredRecallLedger : List (String × PremiseKind) := [("measured recall bound..."), ...]`
   Fix: Construct the ledger programmatically by applying `ProbCert.ofMeasured` to the `measured_recall_example` proof to ensure the recorded strings are mathematically bound to the verified theorem.

### ControlStack/Families/F5/EscrowBudgetMsg.lean
Verdict: Sound / No defects found.
Defects: None. The models for message passing, clock skew, duplicate delivery, and crashes accurately reflect the header claims. The invariant (`Inv`) correctly restricts safety exclusively to the skew-aware configuration, leaving the unaware configuration vulnerable exactly as proven by the witnesses. Duplicate deliveries correctly and idempotently settle at the true spend.

### ControlStack/Scenarios/SC26LossyLiveness.lean
Verdict: Sound / No defects found.
Defects: None. The network operations (`drop`, `dup`, `deliverAt`) properly model a lossy, duplicating, and reordering environment. The forward simulation correctly maps the abstract network to the durable intent log (`s.delivery`), elegantly proving that the system's safety relies entirely on the bank's idempotency premise (`dedup = true`), which aligns perfectly with the negative witness trace. The bounded-loss fairness quantifiers and liveness progress proofs are mathematically sound.

### ControlStack/Core/TrustRoot.lean
Verdict: Contains defects (tautology / universal overclaim).
Defects:
1. Location: `depsOf .modelRuntimeCorrespondence`
   Problem: Tautology / Universal Overclaim. The dependency graph discharges the `modelRuntimeCorrespondence` premise using the `ControlStack.SC26Refinement.concrete_safe` theorem for ALL scenarios. However, this premise is required by multiple structurally distinct scenarios (e.g., 1, 13, 16, 18, 25, 26) representing completely different systems (like F5 escrow or F6 monitor). Proving refinement for SC-26 (the banking gateway) vacuously grants model-runtime correspondence to F5 and other independent systems.
   Instance: `| .modelRuntimeCorrespondence => [.thm "ControlStack.SC26Refinement.concrete_safe", .root .implementationConformance]`
   Fix: Parameterize the premises or `depsOf` function by scenario ID so each scenario must discharge against its own specific refinement theorem (e.g., `EscrowBudgetMsg.escrow_safe` for F5), or split the premise into scenario-specific variants.

### Cross-cutting
The repository exposes a critical vulnerability at the mathematical-to-metadata boundary. While the underlying abstract proofs (probability tail bounds, clock skew limits, and abstract state refinements) are exceptionally rigorous, the "ledgers" and "certificates" translating these proofs into security claims are occasionally implemented as unchecked strings or hardcoded `True` propositions. This bypasses Lean's dependent type guarantees and permits sweeping claims (e.g., universal SC-26 refinement applying to all systems, or i.i.d. sampling correspondences) to pass mechanical verification silently.
