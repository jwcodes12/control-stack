import ControlStack.Spike
import ControlStack.OutcomeProof

/-!
Root module of the interface-level (VCVio) Lake project, so that `lake build` checks every proof file.

- `ControlStack/Spike.lean`: T1 for arbitrary `ProbComp` distinguishers through a `ProbComp` mediator.
- `ControlStack/HoneypotBridgeProof.lean` restates `ControlStack/HoneypotBridge.lean` (the statement file, kept
  separately and not imported here because both declare the same names) and proves it.
- `ControlStack/RefinementProof.lean` and `ControlStack/OutcomeProof.lean` import and prove the statement files
  `ControlStack/Refinement.lean` and `ControlStack/Outcome.lean`.

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
