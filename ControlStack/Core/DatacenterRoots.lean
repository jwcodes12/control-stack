/-
The DATACENTER LAYER's premises reduced to the trust roots of `Core/TrustRoot.lean` (same `Root` type and the same
premise graph). This is kept in a separate file because `TrustRoot`'s scenario and root tables are GENERATED from
tools/portfolio_ledger.py, and the datacenter files are not portfolio scenarios.

Files and their premises:
- `F2/GPUResidue`: memory scrub between tenants; local-memory clear on context switch.
- `F1/FabricIsolation`: the NIC/fabric protection-domain check; one-sided RDMA mediated by the NIC; key rotation; key
  secrecy (for the guess bound); fabric contention (measured).
- `F4/AttestedKeyRelease` (+ `F4/AttestedLiveness`): TEE integrity and measurement correctness; attestation
  signature unforgeability; broker key custody; nonce unpredictability; allowlist hygiene; broker/TEE conformance;
  scheduling delay ≤ W (liveness).
- `F5/EscrowBudgetMsg`: the clock-skew bound σ; the durable spend counter; settle-message authenticity; settle
  delivery (liveness).
- `F3/DistributedHalt`: the rate ρ (metered); the latency L, delivery Δ and sink learning delay ε; sink fencing on
  every effect; epoch custody (`HoldsOld`).

The reduction is a modelling judgement, as in `TrustRoot.depsOf`. One judgement is flagged: the `Root` type has no
hardware-TEE root. TEE integrity is reduced to `kernel_mediation`, its closest analogue (a trusted substrate that
mediates every access). A dedicated `tee_integrity` root would split it out.

Computed results (by `decide`): `file_roots_table`, `layer_roots`, `layer_sharing`, `layer_vs_portfolio`.
No novelty is claimed.
-/
import ControlStack.Core.TrustRoot

namespace ControlStack.DatacenterRoots

open ControlStack.Cert ControlStack.TrustRoot

inductive DPrem where
  | memoryScrub
  | contextClear
  | fabricPartition
  | rdmaMediated
  | rdmaKeyRotation
  | rdmaKeySecrecy
  | fabricContention
  | teeIntegrity
  | attestationSignature
  | brokerKeyCustody
  | nonceUnpredictable
  | allowlistHygiene
  | brokerConformance
  | schedulingDelay
  | clockSkewBound
  | durableCounter
  | settleAuthenticity
  | settleDelivery
  | rateBound
  | latencyBound
  | sinkFencing
  | epochCustody
deriving DecidableEq, Repr

def DPrem.name : DPrem → String
  | .memoryScrub => "memory_scrub_between_tenants"
  | .contextClear => "local_memory_clear_on_switch"
  | .fabricPartition => "fabric_partition_enforced"
  | .rdmaMediated => "rdma_mediated"
  | .rdmaKeyRotation => "rdma_key_rotation"
  | .rdmaKeySecrecy => "rdma_key_secrecy"
  | .fabricContention => "fabric_contention_channel"
  | .teeIntegrity => "tee_integrity_and_measurement"
  | .attestationSignature => "attestation_signature_unforgeable"
  | .brokerKeyCustody => "broker_key_custody"
  | .nonceUnpredictable => "nonce_unpredictable"
  | .allowlistHygiene => "allowlist_hygiene"
  | .brokerConformance => "broker_tee_conformance"
  | .schedulingDelay => "scheduling_delay_le_W"
  | .clockSkewBound => "clock_skew_bound_sigma"
  | .durableCounter => "durable_spend_counter"
  | .settleAuthenticity => "settle_message_authenticity"
  | .settleDelivery => "settle_delivery"
  | .rateBound => "rate_bound_rho"
  | .latencyBound => "latency_delivery_bounds"
  | .sinkFencing => "sink_fencing_every_effect"
  | .epochCustody => "epoch_custody"

def DPrem.kind : DPrem → PremiseKind
  | .memoryScrub => .correspondence
  | .contextClear => .correspondence
  | .fabricPartition => .environment
  | .rdmaMediated => .environment
  | .rdmaKeyRotation => .correspondence
  | .rdmaKeySecrecy => .environment
  | .fabricContention => .measurement
  | .teeIntegrity => .environment
  | .attestationSignature => .environment
  | .brokerKeyCustody => .environment
  | .nonceUnpredictable => .environment
  | .allowlistHygiene => .organisational
  | .brokerConformance => .correspondence
  | .schedulingDelay => .measurement
  | .clockSkewBound => .measurement
  | .durableCounter => .environment
  | .settleAuthenticity => .environment
  | .settleDelivery => .measurement
  | .rateBound => .measurement
  | .latencyBound => .measurement
  | .sinkFencing => .correspondence
  | .epochCustody => .environment

/-- a datacenter premise rests on roots directly or on portfolio premises -/
inductive DDep where
  | root (r : Root)
  | prem (p : Prem)

def ddeps : DPrem → List DDep
  | .memoryScrub => [.root .implementationConformance, .root .measuredRates]
  | .contextClear => [.root .kernelMediation, .root .implementationConformance]
  | .fabricPartition => [.root .kernelMediation, .root .implementationConformance]
  | .rdmaMediated => [.prem .exclusiveEffectPath]
  | .rdmaKeyRotation => [.root .implementationConformance]
  | .rdmaKeySecrecy => [.root .keyCustody]
  | .fabricContention => [.root .measuredRates]
  | .teeIntegrity => [.root .kernelMediation]
  | .attestationSignature => [.root .issuerAuthenticity]
  | .brokerKeyCustody => [.root .keyCustody]
  | .nonceUnpredictable => [.root .collisionResistance]
  | .allowlistHygiene => [.root .orgConfiguration]
  | .brokerConformance => [.root .implementationConformance]
  | .schedulingDelay => [.root .measuredRates]
  | .clockSkewBound => [.root .measuredRates]
  | .durableCounter => [.prem .antiRollback]
  | .settleAuthenticity => [.root .issuerAuthenticity, .root .keyCustody]
  | .settleDelivery => [.root .measuredRates]
  | .rateBound => [.prem .trustedMeter, .root .measuredRates]
  | .latencyBound => [.root .measuredRates]
  | .sinkFencing => [.prem .exclusiveEffectPath, .root .implementationConformance]
  | .epochCustody => [.root .keyCustody, .root .issuerAuthenticity]

/-- the roots a datacenter premise rests on (through the portfolio graph where it reuses a portfolio premise) -/
def DDep.roots : DDep → List Root
  | .root r => [r]
  | .prem q => rootsOf q

def droots (p : DPrem) : List Root := allRoots.filter fun r => decide (r ∈ (ddeps p).flatMap DDep.roots)

/-- the datacenter files and their premises -/
def files : List (String × List DPrem) :=
  [("F2/GPUResidue", [.memoryScrub, .contextClear]),
   ("F1/FabricIsolation", [.fabricPartition, .rdmaMediated, .rdmaKeyRotation, .rdmaKeySecrecy, .fabricContention]),
   ("F4/AttestedKeyRelease", [.teeIntegrity, .attestationSignature, .brokerKeyCustody, .nonceUnpredictable,
      .allowlistHygiene, .brokerConformance, .schedulingDelay]),
   ("F5/EscrowBudgetMsg", [.clockSkewBound, .durableCounter, .settleAuthenticity, .settleDelivery]),
   ("F3/DistributedHalt", [.rateBound, .latencyBound, .sinkFencing, .epochCustody])]

def fileRoots (ps : List DPrem) : List Root := allRoots.filter fun r => decide (∃ p ∈ ps, r ∈ droots p)

def layerRoots : List Root := allRoots.filter fun r => decide (∃ f ∈ files, r ∈ fileRoots f.2)

/-- how many datacenter files rest on root r -/
def layerCount (r : Root) : ℕ := (files.filter fun f => decide (r ∈ fileRoots f.2)).length

/-- how many portfolio scenarios rest on root r -/
def portfolioCount (r : Root) : ℕ := (scenarios.filter fun s => decide (r ∈ scenarioRoots s.1)).length

/-! ## Computed tables -/

/-- **Each datacenter file's minimal root set.** -/
theorem file_roots_table : files.map (fun f => (f.1, fileRoots f.2)) =
    [("F2/GPUResidue", [.kernelMediation, .measuredRates, .implementationConformance]),
     ("F1/FabricIsolation", [.kernelMediation, .keyCustody, .measuredRates, .implementationConformance]),
     ("F4/AttestedKeyRelease", [.issuerAuthenticity, .kernelMediation, .collisionResistance, .keyCustody,
        .measuredRates, .orgConfiguration, .implementationConformance]),
     ("F5/EscrowBudgetMsg", [.issuerAuthenticity, .monotonicAnchor, .keyCustody, .measuredRates]),
     ("F3/DistributedHalt", [.issuerAuthenticity, .kernelMediation, .trustedMeter, .keyCustody, .measuredRates,
        .implementationConformance])] := by
  decide

/-- **The datacenter layer rests on 9 of the 12 roots.** It does not use independent_witness, human_judgement or
external_contract. -/
theorem layer_roots : layerRoots =
    [.issuerAuthenticity, .kernelMediation, .monotonicAnchor, .trustedMeter, .collisionResistance, .keyCustody,
     .measuredRates, .orgConfiguration, .implementationConformance] := by
  decide

/-- **Root sharing in the datacenter layer** (of 5 files): measured_rates 5; kernel_mediation, key_custody and
implementation_conformance 4 each; issuer_authenticity 3; the rest 1 or 0. -/
theorem layer_sharing : allRoots.map layerCount = [3, 4, 1, 0, 1, 1, 4, 5, 0, 1, 4, 0] := by
  decide

/-- **What the datacenter layer adds.** It introduces no root outside the portfolio's 12, but it shifts the weight.
Two roots gain more than a quarter of share:
- `key_custody`: from 3 of 28 portfolio scenarios to 4 of 5 datacenter files;
- `implementation_conformance`: from 12 of 28 to 4 of 5.
`measured_rates` stays universal: σ, ρ, L, Δ, ε, scheduling delay, residue and contention. -/
theorem layer_vs_portfolio :
    (∀ r ∈ layerRoots, r ∈ allRoots) ∧ portfolioCount .keyCustody = 3 ∧ layerCount .keyCustody = 4 ∧
    layerCount .measuredRates = files.length ∧
    allRoots.filter (fun r => decide (4 * layerCount r * scenarios.length >
        4 * portfolioCount r * files.length + files.length * scenarios.length)) =
      [.keyCustody, .implementationConformance] := by
  decide

/-! ## Ledgers -/

/-- "file rests on: root" for every datacenter file -/
def layerRootLedger : List (String × PremiseKind) :=
  files.flatMap fun f => (fileRoots f.2).map fun r => (f.1 ++ " rests on: " ++ r.name, r.kind)

/-- the datacenter premises with their kinds -/
def layerPremiseLedger : List (String × PremiseKind) :=
  files.flatMap fun f => f.2.map fun p => (f.1 ++ ":" ++ p.name, p.kind)

end ControlStack.DatacenterRoots

#print axioms ControlStack.DatacenterRoots.file_roots_table
#print axioms ControlStack.DatacenterRoots.layer_roots
#print axioms ControlStack.DatacenterRoots.layer_sharing
#print axioms ControlStack.DatacenterRoots.layer_vs_portfolio
#eval IO.println (ControlStack.Cert.ledgerJson ControlStack.DatacenterRoots.layerPremiseLedger)
