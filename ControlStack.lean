import ControlStack.PolicyTamper
import ControlStack.GateComposition
import ControlStack.TrustedBroker
import ControlStack.HaltLiveness
import ControlStack.Core.Gate
import ControlStack.Core.Leakage
import ControlStack.Families.F1.Capability
import ControlStack.Families.F2.Observations
import ControlStack.Families.F3.Temporal
import ControlStack.Families.F4.Integrity
import ControlStack.Families.F4.GateClients
import ControlStack.Families.F5.Leases
import ControlStack.Families.F5.Lease
import ControlStack.Families.F6.Probabilistic
import ControlStack.Families.F7.Approvals
import ControlStack.Families.F8.Composition
import ControlStack.Scenarios.SC01
import ControlStack.Scenarios.SC03
import ControlStack.Scenarios.SC13
import ControlStack.Scenarios.SC27
import ControlStack.Witnesses.CovertNoGo
import ControlStack.Witnesses.Necessity
import ControlStack.Witnesses.LeakWitness
import ControlStack.Spike
import ControlStack.OutcomeProof
import ControlStack.SoftHockey
import ControlStack.StratifiedGame
import ControlStack.DeferMono
import ControlStack.UseQ
import ControlStack.AdaptiveSharp
import ControlStack.AdaptiveUMADAPT
import ControlStack.ComposeGame
import ControlStack.ComposeAvg
import ControlStack.ComposeBlindSpot
import ControlStack.CovertChannel
import ControlStack.GatewayModel
import ControlStack.CovertNoGo
import ControlStack.AuditGate
import ControlStack.AuditDispatch
import ControlStack.EgressGate
import ControlStack.ScenarioARepair
import ControlStack.SideChannel
import ControlStack.ScenarioASide
import ControlStack.ScenarioAUsefulness
import ControlStack.LifetimeLedger
import ControlStack.GatewayCore
import ControlStack.SafetyCaseSC01
import ControlStack.ComposeCoverage
import ControlStack.MultiStep
import ControlStack.ScenarioACore
import ControlStack.AuditBudget
import ControlStack.Leakage
import ControlStack.Necessity
import ControlStack.Gate
import ControlStack.GateClients
import ControlStack.Lease
import ControlStack.LeakWitness

/-!
Root module of the interface-level (VCVio) Lake project, so that `lake build` checks every proof file.

- `ControlStack/Spike.lean`: T1 for arbitrary `ProbComp` distinguishers through a `ProbComp` mediator.
- `ControlStack/HoneypotBridgeProof.lean` restates `ControlStack/HoneypotBridge.lean` (the statement file, kept
  separately and not imported here because both declare the same names) and proves it.
- `ControlStack/RefinementProof.lean` and `ControlStack/OutcomeProof.lean` import and prove the statement files
  `ControlStack/Refinement.lean` and `ControlStack/Outcome.lean`.
- `SoftSlack`/`SoftHockey`, `StratifiedGame` and `DeferGame`/`DeferMono`: game-level versions of the soft-slack,
  hockey-stick, stratified and audit-then-defer results.
- `ComposeGame`: trusted + untrusted monitoring in one game; product bound and tightness witness.
- `ComposeAvg`: composition with a general joint kernel and with the population-average trusted miss rate.
- `ComposeBlindSpot`: negative result: a population-average trusted miss rate does not bound a content-adaptive Red.
- `CovertChannel`: covert-propagation bound for mediated machine channels (the P0 catastrophe).
- `UseQ`: rational usefulness checker and its soundness bridge.
- `AdaptiveBalance`, `AdaptiveSharp`, `AdaptiveGeneric`, `AdaptiveUMADAPT`: the sharper adaptive converse core.

The axiom reports below should list only `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms ControlStack.Spike.distinguish_le_tv
#print axioms ControlStack.Spike.mediated_tv_le
#print axioms ControlStack.Bridge.bridge
#print axioms ControlStack.Refine.deployG
#print axioms ControlStack.Refine.protocol
#print axioms ControlStack.Refine.endToEnd
#print axioms ControlStack.Refine.attain
#print axioms ControlStack.Refine.witness
#print axioms ControlStack.OutcomeGame.marginal
#print axioms ControlStack.OutcomeGame.gameLaw
#print axioms ControlStack.OutcomeGame.honest
#print axioms ControlStack.OutcomeGame.pareto
#print axioms ControlStack.OutcomeGame.witness
#print axioms ControlStack.SoftSlack.softEndToEnd
#print axioms ControlStack.SoftHockey.softEndToEndHockey
#print axioms ControlStack.StratifiedGame.stratifiedProtocolEndToEnd
#print axioms ControlStack.DeferGame.defer_bridge
#print axioms ControlStack.DeferGame.defer_mono
#print axioms ControlStack.UseQ.checkUseQ_sound
#print axioms ControlStack.AdaptiveSharp.uniform_seed_risk_balanced
#print axioms ControlStack.AdaptiveUMADAPT.sharp_uniform_adProtocolCatModel
#print axioms ControlStack.Compose.composedEndToEnd
#print axioms ControlStack.Compose.composed_tight
#print axioms ControlStack.ComposeAvg.composedJ_end
#print axioms ControlStack.ComposeAvg.composedPop_end
#print axioms ControlStack.ComposeBlindSpot.pop_avg_miss
#print axioms ControlStack.ComposeBlindSpot.blind_spot_risk
#print axioms ControlStack.Covert.covert_bound
#print axioms ControlStack.Covert.design_point
#print axioms ControlStack.GatewayModel.gateway_bound
#print axioms ControlStack.CovertNoGo.controllable_leak
#print axioms ControlStack.CovertNoGo.one_bit_coordinates
#print axioms ControlStack.AuditGate.invariant_preserved
#print axioms ControlStack.AuditDispatch.trace_safe

#print axioms ControlStack.EgressGate.trace_safe
