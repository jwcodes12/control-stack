/-
Trust roots: the portfolio's premises reduce to a small set of roots.

Almost every premise in ASSURANCE-LEDGER.md is either:
- discharged by a Lean theorem in this repository (`Dep.thm`),
- reduced to other premises (`Dep.prem`), or
- left resting on a TRUST ROOT (`Dep.root`).
This file encodes the dependency structure as a finite graph over the 29 normalised premises of
tools/portfolio_ledger.py and computes, by evaluation, which roots each scenario rests on.

Roots:
- TECHNICAL trust roots (kind environment):
  - `issuerAuthenticity`: the kernel/OS/platform identity is the issuer (Core/Authenticated);
  - `kernelMediation`: the kernel/hypervisor isolates and mediates, so there is no unmediated path;
  - `monotonicAnchor`: a trusted monotonic counter (Core/AntiRollback);
  - `independentWitness`: an independently administered anchoring witness (SC-27);
  - `trustedMeter`: resource metering the agent cannot influence (SC-28);
  - `collisionResistance`: of the content hash;
  - `keyCustody`: secrets and keys are kept out of the agent's reach.
- RESIDUAL roots (not technical trust roots; named so they are not hidden):
  - `measuredRates` (measurement): usefulness, recall, TV, skew, side-channel and determinism figures;
  - `humanJudgement` and `orgConfiguration` (organisational): reviewer competence, role and launch configuration;
  - `implementationConformance` and `externalContract` (correspondence): the runtime implements the model;
    external systems honour their contract (idempotency).

Results (all by `decide`, i.e. kernel evaluation of the finite graph):
- `allPrems_complete`, `graph_total`, `graph_discharged`: every premise has an entry, and every entry discharges it
  by something;
- `graph_reduces`: the reduction reaches a fixpoint within the fuel bound, so the graph is acyclic and every
  scenario's premise set reduces completely to roots and theorems;
- `scenario_roots_table`: the root set of each of the 28 scenarios. Dependencies are conjunctive (every listed dep is
  needed), so the reachable root set is the unique minimal set of roots that suffices;
- `portfolio_roots`: the whole portfolio rests on all 12 roots: 7 technical, 5 residual;
- `root_sharing`: the most-shared root is the residual `measured_rates` (26 of 28 scenarios); the most-shared
  technical roots are kernel mediation (21) and issuer authenticity (20).
Ledgers for tools/cert_ledger.py:
- `sc26RootLedger` ("SC-26 rests on: …");
- `scenarioRootLedger` (every scenario);
- `portfolioRootLedger`;
- `scenarioPremiseLedger` (premises per scenario; tools/test_trust_root.py checks it against
  tools/portfolio_ledger.py).

Limits:
- The dependency edges are a MODELLING JUDGEMENT. They mirror tools/portfolio_ledger.py's normalisation and the
  repository's theorems, and need review.
- A reduction to a root does not discharge the root. It says what must be trusted, measured or reviewed.
- Theorem edges name the repository theorem that discharges the formal part. Their applicability to the
  deployment is the remaining root.
- No novelty is claimed.
-/
import Mathlib.Tactic
import ControlStack.Core.Cert

namespace ControlStack.TrustRoot

open ControlStack.Cert

inductive Root where
  | issuerAuthenticity
  | kernelMediation
  | monotonicAnchor
  | independentWitness
  | trustedMeter
  | collisionResistance
  | keyCustody
  | measuredRates
  | humanJudgement
  | orgConfiguration
  | implementationConformance
  | externalContract
deriving DecidableEq, Repr

def Root.name : Root → String
  | .issuerAuthenticity => "issuer_authenticity"
  | .kernelMediation => "kernel_mediation"
  | .monotonicAnchor => "monotonic_anchor"
  | .independentWitness => "independent_witness"
  | .trustedMeter => "trusted_meter"
  | .collisionResistance => "collision_resistance"
  | .keyCustody => "key_custody"
  | .measuredRates => "measured_rates (residual)"
  | .humanJudgement => "human_judgement (residual)"
  | .orgConfiguration => "org_configuration (residual)"
  | .implementationConformance => "implementation_conformance (residual)"
  | .externalContract => "external_contract (residual)"

def Root.kind : Root → PremiseKind
  | .measuredRates => .measurement
  | .humanJudgement => .organisational
  | .orgConfiguration => .organisational
  | .implementationConformance => .correspondence
  | .externalContract => .correspondence
  | _ => .environment

def Root.technical : Root → Bool
  | .measuredRates | .humanJudgement | .orgConfiguration | .implementationConformance | .externalContract => false
  | _ => true

def allRoots : List Root :=
  [.issuerAuthenticity, .kernelMediation, .monotonicAnchor, .independentWitness, .trustedMeter, .collisionResistance,
   .keyCustody, .measuredRates, .humanJudgement, .orgConfiguration, .implementationConformance, .externalContract]

inductive Prem where
  | credentialSeparation
  | honestUsefulness
  | observationComplete
  | exclusiveEffectPath
  | semanticJudgement
  | policyIntegrity
  | modelRuntimeCorrespondence
  | canonicaliserComplete
  | collisionResistance
  | hiddenSample
  | roleSeparation
  | consumeByDigest
  | honeypotIndistinguishable
  | independentReview
  | osKernelEnforcement
  | rekeyIndependence
  | sourceAttribution
  | statisticalIndependence
  | antiRollback
  | trustedMeter
  | deterministicReexecution
  | durableAck
  | exactPayloadDisplay
  | finiteTranscript
  | independentAnchor
  | receiverIdempotency
  | revocationEffective
  | taintPropagation
  | versionedWrites
deriving DecidableEq, Repr

def Prem.name : Prem → String
  | .credentialSeparation => "credential_separation"
  | .honestUsefulness => "honest_usefulness"
  | .observationComplete => "observation_complete"
  | .exclusiveEffectPath => "exclusive_effect_path"
  | .semanticJudgement => "semantic_judgement"
  | .policyIntegrity => "policy_integrity"
  | .modelRuntimeCorrespondence => "model_runtime_correspondence"
  | .canonicaliserComplete => "canonicaliser_complete"
  | .collisionResistance => "collision_resistance"
  | .hiddenSample => "hidden_sample"
  | .roleSeparation => "role_separation"
  | .consumeByDigest => "consume_by_digest"
  | .honeypotIndistinguishable => "honeypot_indistinguishable"
  | .independentReview => "independent_review"
  | .osKernelEnforcement => "os_kernel_enforcement"
  | .rekeyIndependence => "rekey_independence"
  | .sourceAttribution => "source_attribution"
  | .statisticalIndependence => "statistical_independence"
  | .antiRollback => "anti_rollback"
  | .trustedMeter => "trusted_meter"
  | .deterministicReexecution => "deterministic_reexecution"
  | .durableAck => "durable_ack"
  | .exactPayloadDisplay => "exact_payload_display"
  | .finiteTranscript => "finite_transcript"
  | .independentAnchor => "independent_anchor"
  | .receiverIdempotency => "receiver_idempotency"
  | .revocationEffective => "revocation_effective"
  | .taintPropagation => "taint_propagation"
  | .versionedWrites => "versioned_writes"

/-- the premise kinds, as in ASSURANCE-LEDGER.md -/
def Prem.kind : Prem → PremiseKind
  | .credentialSeparation => .environment
  | .honestUsefulness => .measurement
  | .observationComplete => .measurement
  | .exclusiveEffectPath => .environment
  | .semanticJudgement => .measurement
  | .policyIntegrity => .environment
  | .modelRuntimeCorrespondence => .correspondence
  | .canonicaliserComplete => .correspondence
  | .collisionResistance => .environment
  | .hiddenSample => .correspondence
  | .roleSeparation => .organisational
  | .consumeByDigest => .correspondence
  | .honeypotIndistinguishable => .measurement
  | .independentReview => .organisational
  | .osKernelEnforcement => .environment
  | .rekeyIndependence => .correspondence
  | .sourceAttribution => .correspondence
  | .statisticalIndependence => .measurement
  | .antiRollback => .environment
  | .trustedMeter => .environment
  | .deterministicReexecution => .measurement
  | .durableAck => .environment
  | .exactPayloadDisplay => .correspondence
  | .finiteTranscript => .correspondence
  | .independentAnchor => .organisational
  | .receiverIdempotency => .correspondence
  | .revocationEffective => .environment
  | .taintPropagation => .correspondence
  | .versionedWrites => .correspondence

def allPrems : List Prem :=
  [.credentialSeparation, .honestUsefulness, .observationComplete, .exclusiveEffectPath, .semanticJudgement, .policyIntegrity, .modelRuntimeCorrespondence, .canonicaliserComplete, .collisionResistance, .hiddenSample, .roleSeparation, .consumeByDigest, .honeypotIndistinguishable, .independentReview, .osKernelEnforcement, .rekeyIndependence, .sourceAttribution, .statisticalIndependence, .antiRollback, .trustedMeter, .deterministicReexecution, .durableAck, .exactPayloadDisplay, .finiteTranscript, .independentAnchor, .receiverIdempotency, .revocationEffective, .taintPropagation, .versionedWrites]

/-- each scenario's normalised premises (from tools/portfolio_ledger.py) -/
def scenarios : List (ℕ × List Prem) :=
  [(1, [.honestUsefulness, .observationComplete, .modelRuntimeCorrespondence, .statisticalIndependence, .finiteTranscript]),
   (2, [.observationComplete, .rekeyIndependence]),
   (3, [.honestUsefulness, .exclusiveEffectPath, .policyIntegrity, .sourceAttribution]),
   (4, [.observationComplete, .canonicaliserComplete]),
   (5, [.observationComplete, .exclusiveEffectPath]),
   (6, [.credentialSeparation, .canonicaliserComplete]),
   (7, [.honestUsefulness, .observationComplete, .exclusiveEffectPath]),
   (8, [.credentialSeparation, .honestUsefulness, .exclusiveEffectPath, .consumeByDigest]),
   (9, [.credentialSeparation, .honestUsefulness, .roleSeparation, .osKernelEnforcement]),
   (10, [.credentialSeparation, .honestUsefulness, .exclusiveEffectPath, .policyIntegrity]),
   (11, [.credentialSeparation, .honestUsefulness, .policyIntegrity]),
   (12, [.credentialSeparation, .honestUsefulness, .exclusiveEffectPath, .revocationEffective]),
   (13, [.credentialSeparation, .honestUsefulness, .exclusiveEffectPath, .modelRuntimeCorrespondence]),
   (14, [.credentialSeparation, .honestUsefulness, .antiRollback, .trustedMeter]),
   (15, [.credentialSeparation, .semanticJudgement]),
   (16, [.credentialSeparation, .honestUsefulness, .exclusiveEffectPath, .modelRuntimeCorrespondence, .collisionResistance, .roleSeparation]),
   (17, [.credentialSeparation, .honestUsefulness, .exclusiveEffectPath, .semanticJudgement]),
   (18, [.credentialSeparation, .honestUsefulness, .exclusiveEffectPath, .durableAck, .modelRuntimeCorrespondence]),
   (19, [.credentialSeparation, .honestUsefulness, .versionedWrites]),
   (20, [.credentialSeparation, .semanticJudgement]),
   (21, [.credentialSeparation, .hiddenSample, .deterministicReexecution]),
   (22, [.semanticJudgement, .hiddenSample]),
   (23, [.credentialSeparation, .honestUsefulness, .exactPayloadDisplay, .taintPropagation]),
   (24, [.observationComplete, .hiddenSample, .honeypotIndistinguishable]),
   (25, [.credentialSeparation, .honestUsefulness, .exclusiveEffectPath, .semanticJudgement, .modelRuntimeCorrespondence]),
   (26, [.credentialSeparation, .honestUsefulness, .modelRuntimeCorrespondence, .roleSeparation, .independentReview, .receiverIdempotency]),
   (27, [.collisionResistance, .independentAnchor]),
   (28, [.credentialSeparation, .honestUsefulness, .antiRollback, .trustedMeter])]

/-! ## The dependency graph (a modelling judgement) -/

inductive Dep where
  | thm (name : String)
  | prem (p : Prem)
  | root (r : Root)

/-- how each premise is discharged (conjunctive: all listed deps are needed) -/
def depsOf : Prem → List Dep
  | .credentialSeparation => [.thm "ControlStack.AuthenticatedLog.issued_trusted", .root .issuerAuthenticity]
  | .honestUsefulness => [.root .measuredRates]
  | .observationComplete =>
    [.thm "ControlStack.TimedRelease.timing_noninterference", .root .kernelMediation, .root .measuredRates]
  | .exclusiveEffectPath => [.root .kernelMediation]
  | .semanticJudgement => [.root .humanJudgement, .root .measuredRates]
  | .policyIntegrity => [.prem .exclusiveEffectPath, .prem .credentialSeparation]
  | .modelRuntimeCorrespondence =>
    [.thm "ControlStack.SC26Refinement.concrete_safe", .root .implementationConformance]
  | .canonicaliserComplete => [.prem .exclusiveEffectPath, .root .implementationConformance]
  | .collisionResistance => [.root .collisionResistance]
  | .hiddenSample => [.root .keyCustody, .prem .observationComplete]
  | .roleSeparation => [.prem .credentialSeparation, .root .orgConfiguration]
  | .consumeByDigest => [.prem .collisionResistance, .prem .exclusiveEffectPath]
  | .honeypotIndistinguishable => [.root .measuredRates]
  | .independentReview => [.root .humanJudgement]
  | .osKernelEnforcement => [.root .kernelMediation]
  | .rekeyIndependence => [.prem .observationComplete]
  | .sourceAttribution => [.prem .credentialSeparation]
  | .statisticalIndependence => [.root .measuredRates]
  | .antiRollback => [.thm "ControlStack.AntiRollback.rollback_transfer", .root .monotonicAnchor]
  | .trustedMeter => [.root .trustedMeter]
  | .deterministicReexecution => [.root .measuredRates]
  | .durableAck => [.prem .antiRollback, .root .implementationConformance]
  | .exactPayloadDisplay => [.prem .exclusiveEffectPath, .root .implementationConformance]
  | .finiteTranscript => [.prem .observationComplete]
  | .independentAnchor => [.root .independentWitness]
  | .receiverIdempotency => [.prem .antiRollback, .root .externalContract]
  | .revocationEffective => [.root .kernelMediation]
  | .taintPropagation => [.prem .exclusiveEffectPath, .root .implementationConformance]
  | .versionedWrites => [.prem .antiRollback, .root .implementationConformance]

/-- roots reachable from a premise, with a fuel bound -/
def rootsF : ℕ → Prem → List Root
  | 0, _ => []
  | n + 1, p => (depsOf p).flatMap fun d => match d with
    | .root r => [r]
    | .prem q => rootsF n q
    | .thm _ => []

/-- enough fuel: the graph has 29 nodes -/
def fuel : ℕ := 30

/-- the roots a premise rests on, in canonical order -/
def rootsOf (p : Prem) : List Root := allRoots.filter fun r => decide (r ∈ rootsF fuel p)

/-- the premises of scenario `sc` -/
def premsOf (sc : ℕ) : List Prem := ((scenarios.find? (·.1 = sc)).map Prod.snd).getD []

/-- the roots scenario `sc` rests on, in canonical order -/
def scenarioRoots (sc : ℕ) : List Root := allRoots.filter fun r => decide (∃ p ∈ premsOf sc, r ∈ rootsF fuel p)

/-! ## Checks (by evaluation) -/

theorem allPrems_complete : ∀ p : Prem, p ∈ allPrems := by
  intro p; cases p <;> decide

theorem graph_total : ∀ s ∈ scenarios, ∀ p ∈ s.2, p ∈ allPrems := by decide

theorem graph_discharged : ∀ p ∈ allPrems, depsOf p ≠ [] := by decide

/-- **Every scenario's premise set reduces completely to roots** (the reduction reaches its fixpoint well within the
fuel bound, so the graph is acyclic). -/
theorem graph_reduces : ∀ p ∈ allPrems, rootsF fuel p = rootsF (fuel + 1) p ∧ rootsF 4 p = rootsF fuel p := by
  decide

/-- **The minimal root set of every scenario.** -/
theorem scenario_roots_table : scenarios.map (fun s => (s.1, scenarioRoots s.1)) =
      [(1, [.kernelMediation, .measuredRates, .implementationConformance]),
       (2, [.kernelMediation, .measuredRates]),
       (3, [.issuerAuthenticity, .kernelMediation, .measuredRates]),
       (4, [.kernelMediation, .measuredRates, .implementationConformance]),
       (5, [.kernelMediation, .measuredRates]),
       (6, [.issuerAuthenticity, .kernelMediation, .implementationConformance]),
       (7, [.kernelMediation, .measuredRates]),
       (8, [.issuerAuthenticity, .kernelMediation, .collisionResistance, .measuredRates]),
       (9, [.issuerAuthenticity, .kernelMediation, .measuredRates, .orgConfiguration]),
       (10, [.issuerAuthenticity, .kernelMediation, .measuredRates]),
       (11, [.issuerAuthenticity, .kernelMediation, .measuredRates]),
       (12, [.issuerAuthenticity, .kernelMediation, .measuredRates]),
       (13, [.issuerAuthenticity, .kernelMediation, .measuredRates, .implementationConformance]),
       (14, [.issuerAuthenticity, .monotonicAnchor, .trustedMeter, .measuredRates]),
       (15, [.issuerAuthenticity, .measuredRates, .humanJudgement]),
       (16, [.issuerAuthenticity, .kernelMediation, .collisionResistance, .measuredRates, .orgConfiguration, .implementationConformance]),
       (17, [.issuerAuthenticity, .kernelMediation, .measuredRates, .humanJudgement]),
       (18, [.issuerAuthenticity, .kernelMediation, .monotonicAnchor, .measuredRates, .implementationConformance]),
       (19, [.issuerAuthenticity, .monotonicAnchor, .measuredRates, .implementationConformance]),
       (20, [.issuerAuthenticity, .measuredRates, .humanJudgement]),
       (21, [.issuerAuthenticity, .kernelMediation, .keyCustody, .measuredRates]),
       (22, [.kernelMediation, .keyCustody, .measuredRates, .humanJudgement]),
       (23, [.issuerAuthenticity, .kernelMediation, .measuredRates, .implementationConformance]),
       (24, [.kernelMediation, .keyCustody, .measuredRates]),
       (25, [.issuerAuthenticity, .kernelMediation, .measuredRates, .humanJudgement, .implementationConformance]),
       (26, [.issuerAuthenticity, .monotonicAnchor, .measuredRates, .humanJudgement, .orgConfiguration, .implementationConformance, .externalContract]),
       (27, [.independentWitness, .collisionResistance]),
       (28, [.issuerAuthenticity, .monotonicAnchor, .trustedMeter, .measuredRates])] := by
  decide

/-- **The whole portfolio** rests on these roots. -/
theorem portfolio_roots :
    allRoots.filter (fun r => decide (∃ s ∈ scenarios, r ∈ scenarioRoots s.1)) = allRoots ∧
    (allRoots.filter Root.technical).length = 7 := by
  decide

/-- **Root sharing.** The most-shared root is the RESIDUAL `measured_rates` (26 of 28 scenarios: usefulness and recall
figures). The most-shared technical roots are kernel mediation (21) and issuer authenticity (20). -/
theorem root_sharing :
    (scenarios.filter (fun s => decide (Root.measuredRates ∈ scenarioRoots s.1))).length = 26 ∧
    (scenarios.filter (fun s => decide (Root.kernelMediation ∈ scenarioRoots s.1))).length = 21 ∧
    (scenarios.filter (fun s => decide (Root.issuerAuthenticity ∈ scenarioRoots s.1))).length = 20 ∧
    ∀ r ∈ allRoots, (scenarios.filter (fun s => decide (r ∈ scenarioRoots s.1))).length ≤ 26 := by
  decide

/-! ## Ledgers (printable with tools/cert_ledger.py) -/

def scName (sc : ℕ) : String := "SC-" ++ (if sc < 10 then "0" else "") ++ toString sc

/-- "SC-XX rests on: root" for every scenario and root -/
def scenarioRootLedger : List (String × PremiseKind) :=
  scenarios.flatMap fun s => (scenarioRoots s.1).map fun r => (scName s.1 ++ " rests on: " ++ r.name, r.kind)

/-- SC-26's roots -/
def sc26RootLedger : List (String × PremiseKind) :=
  (scenarioRoots 26).map fun r => ("SC-26 rests on: " ++ r.name, r.kind)

/-- the portfolio's roots, with how many scenarios rest on each -/
def portfolioRootLedger : List (String × PremiseKind) :=
  allRoots.map fun r =>
    (r.name ++ " (" ++ toString (scenarios.filter (fun s => decide (r ∈ scenarioRoots s.1))).length ++
      " scenarios)", r.kind)

/-- the encoded scenario premises, for the consistency check against tools/portfolio_ledger.py -/
def scenarioPremiseLedger : List (String × PremiseKind) :=
  scenarios.flatMap fun s => s.2.map fun p => (scName s.1 ++ ":" ++ p.name, p.kind)

/-- one line per scenario -/
def restsOn : List String :=
  scenarios.map fun s => scName s.1 ++ " rests on: {" ++ ", ".intercalate ((scenarioRoots s.1).map Root.name) ++ "}"

end ControlStack.TrustRoot

#eval ControlStack.TrustRoot.restsOn
#print axioms ControlStack.TrustRoot.graph_reduces
#print axioms ControlStack.TrustRoot.scenario_roots_table
#print axioms ControlStack.TrustRoot.portfolio_roots
#print axioms ControlStack.TrustRoot.root_sharing
