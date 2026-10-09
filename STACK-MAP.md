# STACK-MAP: the F1–F8 primitives and SC-01..SC-28 on a frontier-lab compute stack

**Status (2026-10-09):** a map and a working checklist. **Nothing here is deployed**, and no lab infrastructure was
touched or inspected. The component descriptions are generic, public knowledge of how such stacks are usually built,
and any particular lab will differ. There are no novelty claims (§5).

- Data: [`stack/components.json`](stack/components.json), with 17 components. Each row lists primitive families,
  scenarios, the trusted component, the premises it must discharge, cited repo evidence, practical tests by hardware
  tier, attack and failure literature, and a status.
- Tool: [`tools/stackmap.py`](tools/stackmap.py) (stdlib only). It validates fail-closed, joins with
  `scenarios/SC-*/manifest.json` and prints the matrix, scenario join, gaps and checklists. Tests:
  [`tools/test_stackmap.py`](tools/test_stackmap.py).
- Canonical status remains [ROADMAP.md](ROADMAP.md). This file does not change any scenario manifest.
- **Refreshed later on 2026-10-09** with work committed on this branch:
  - SC-26 evidence run-1 PASS, and SC-28 cgroup run-1 PASS;
  - the F3 `DistributedHalt` model, the F6 `DamageBound` and `MonitorCollusion` results, and F2 `ChannelInstances`;
  - the F8 `Core/Compose` and `DeputyBridge` composition results;
  - scenario models SC-08/09/10/12/16/18/23/25/26/28.
- Companion docs:
  - [docs/LAB-DEPLOYMENT-MAPPING.md](docs/LAB-DEPLOYMENT-MAPPING.md): how a lab could realise each trusted component
    (a design proposal, untested);
  - [docs/RESEARCHER-WORKFLOW.md](docs/RESEARCHER-WORKFLOW.md): the loop, with exact commands;
  - preregistration drafts `prereg/GPU1-*-DRAFT.md`, `prereg/DC1-*-DRAFT.md` and `prereg/CLOUD1-*-DRAFT.md`. These
    need owner approval and resources.

```sh
python3 tools/stackmap.py                       # component x family matrix + per-component scenario join
python3 tools/stackmap.py --gaps                # open premises, by priority score
python3 tools/stackmap.py --researcher job_scheduler   # actionable checklist
python3 tools/stackmap.py --json ...            # machine-readable
python3 -m unittest tools/test_stackmap.py
```

**Status words (derived from the cited evidence by the tool; a declared status that disagrees is rejected):**

| status | meaning |
|---|---|
| `REFERENCE_TESTED` | A **reference implementation of the trusted role** ran on a commodity host (SQLite rows, loopback namespaces, a simulated bank, distinct Linux UIDs) and has a recorded outcome. This is never a test of the production component. |
| `MODEL_ONLY` | A Lean model applies. Its premises are hypotheses, and nothing at runtime discharges them. |
| `NOT_STARTED` | Neither a model nor runtime evidence exists. No component is currently in this state, because every row reuses at least the generic gate shape. That shape alone is weak (see `gpu_interconnect`). |

**Premise states:**

| state | meaning |
|---|---|
| `REFUTED` | Some evidence failed. |
| `TESTED` | Runtime evidence passed or partially passed. |
| `BUILT_NOT_RUN` | A harness exists but no receipt does. |
| `MODELLED` | Lean or executable-model evidence only. |
| `GAP` | Nothing. Docs and preregistrations never count as evidence. |

---

## 1. How a researcher uses the project day to day

The loop has seven steps. Each produces a file that the next step and the checkers consume. Taking SC-26
("irreversible external action without consent") at a cloud control plane as the worked example:

1. **Write the threat** in `scenarios/SC-XX/threat.md`. Give the Bad event as an observable predicate, the agent's
   powers and the refutation. Pick the stack component it lives in, and run `stackmap --researcher <component>` to see
   which trusted role and premises that component brings with it.
   *SC-26:* "a bank entry without an exact, distinct, unconsumed approval". Component `cloud_control_plane`. The trusted
   role is a credential-holding API proxy.
2. **Pick the primitives** from catalog §3: F1 (one effect path), F3 (absorbing HALT), F5 (global cap) and F7 (exact
   approval). Reuse the shared gate interface (`ControlStack/Core/Gate.lean`) rather than writing new mathematics.
3. **Instantiate a Lean model.** Use one *joint* transition system per effect (the pattern of
   `ControlStack/Scenarios/SC26Transaction.lean`), with:
   - state, operations and a `legal` premise that names what the world must guarantee;
   - an invariant, and the main theorem (`sc26_safe`);
   - **one necessity witness per check**, e.g. `gate_credential_leak_breaks` and `no_dedup_retry_duplicates`.

   The witnesses are the practically useful part. Each tells an infrastructure team "if you drop this check or
   premise, here is a concrete bad trace". Build with `lake build` and record `#print axioms`.
4. **Build a harness** around a reference implementation of the trusted role:
   - OS identities (`SO_PEERCRED`) and an independent observer;
   - a trace checker that replays the runtime trace through a transliteration of the Lean `step`
     (`scenarios/SC-26/harness/check_trace.py`, `model.py`);
   - a differential test of the transliteration against the Lean model (`test_model.py`).
5. **Preregister** under `prereg/` before measuring (`prereg/SC26-TRANSACTION-GATE.md`). Record:
   - the attack battery and expected outcomes;
   - negative controls, each with exactly one check disabled, which the independent reconciliation must detect;
   - the honest-usefulness floor (≥ 58/64) and its baseline.
6. **Produce evidence** on a disposable host. Each run writes a *new* receipt directory that refuses to overwrite.
   Numbers come from `tools/ctrlcert.py`, which prints the theorem, its premises and the measurement that would
   refute it. Failures are kept: SC-01's page-cache refutation (64/64) and its 0/64 VM usefulness are both recorded.
7. **Update the manifest** (`scenarios/SC-XX/manifest.json`), only from grounded evidence:
   - each assumption on four axes (proof, evidence, applicability, usefulness), plus six `scope_axes`;
   - run `python3 tools/check_scenarios.py`;
   - get an adversarial review by a model from another family, and file a disposition
     (`reviews/sc26-2026-10-09/disposition.md`).

**What a researcher at a lab would actually do with this:**

- **Turn the premises into a design review.** Take one component they own, say the job scheduler, and run
  `stackmap --researcher job_scheduler`. Read the premise list as a design-review checklist for their own
  infrastructure. The question is "is usage of a job and all its descendants charged by a kernel-enforced hierarchy?",
  not "is it secure?".
- **Use the necessity witnesses as regression tests.** The bad traces for fork without lease accounting, rollback
  double-spends and self-review are exactly the negative controls their own CI should contain.
- **Treat the gaps as an experiment backlog.** `--gaps` is ordered so that cheap, widely blocking tests come first (§4).
- **Expect no guarantee.** The project delivers conditional accounting with named premises, refutations, and
  experiment design. It does not certify anything as safe.

---

## 2. Stack map

### 2a. Generated summary

Regenerate with `python3 tools/stackmap.py --gaps --json` and `--matrix`.

The table abbreviates scenario ids: `21` means SC-21. Column key:

- **tested premises:** premises with runtime evidence on a reference implementation;
- **open premises:** premises that are `GAP` or `REFUTED`; a `!` marks a refuted one;
- **score:** the gap score from §6.

| component | families | scenarios | role | tested premises | open premises | status | tier | score |
|---|---|---|---|---|---|---|---|---|
| researcher_workstation | F4 F6 F8 | 21 22 27 | verifier | evidence_source_binding, non_vacuous_numbers | statement_fidelity, independent_attestation | REFERENCE_TESTED | commodity | 12.0 |
| agent_sandbox | F1 F2 F3 F5 | 02 04 06 08 09 11 12 23 | gate | complete_mediation (egress slice only), creation_via_registry (partial: processes) | policy_integrity, exec_allowlist, privilege_lattice, taint_propagation, co_tenant_side_channels(!) | REFERENCE_TESTED | commodity | 88.0 |
| code_review_cicd | F1 F3 F4 F7 | 15 16 17 18 21 25 27 | gate/attester | consume_by_digest, distinct_reviewer | signing_key_custody, builder_isolation, review_semantics | REFERENCE_TESTED | commodity | 42.0 |
| secrets_kms | F1 F4 F7 | 03 07 16 26 27 | approver/attester | credential_separation, nonce_one_use | signer_unforgeability, anti_rollback | REFERENCE_TESTED | commodity | 20.0 |
| cloud_control_plane | F1 F3 F5 F7 F8 | 14 17 19 26 28 | gate/meter | credential_separation, idempotent_external_api, exact_payload_binding, meter_before_effect (partial) | no_unmediated_deputy, trusted_spend_meter | REFERENCE_TESTED | commodity | 20.0 |
| job_scheduler | F3 F5 F8 | 12 14 28 | gate/meter | kernel_enforced_hierarchical_cap, shared_global_counter, revocation_reaches_running_work | anti_rollback | REFERENCE_TESTED | commodity | 6.0 |
| gpu_multitenancy | F1 F2 F5 | 01 04 05 07 24 | gate | – | memory_scrub_between_tenants, partition_observation_boundary, timing_quantised | MODEL_ONLY | gpu | 10.0 |
| gpu_interconnect | F1 F2 F8 | 03 04 07 28 | gate | – | fabric_partition_enforced, rdma_mediated, fabric_contention_channel | MODEL_ONLY | datacenter | 2.67 |
| gpu_telemetry_meter | F3 F5 F6 | 13 14 18 28 | meter/monitor | – | meter_not_agent_writable, meter_upper_bounds_usage, meter_freshness | MODEL_ONLY | gpu | 8.0 |
| gpu_physical_side_channels | F2 F8 | 01 04 05 | gate | – | sensors_hidden_or_coarsened, physical_channel_measured | MODEL_ONLY | gpu | 4.0 |
| confidential_computing | F1 F2 F4 | 07 11 27 | attester | – | attestation_root_independent, measured_state_is_reviewed, agent_outside_tcb | MODEL_ONLY | gpu | 6.0 |
| weight_storage | F1 F4 F5 | 07 18 20 | gate/meter | – | read_scoped_to_serving, egress_byte_budget, dataset_provenance | MODEL_ONLY | commodity | 18.0 |
| network_egress | F1 F2 F3 F5 | 03 05 07 10 | gate/monitor | all_routes_through_proxy | allowed_destination_not_a_channel, policy_integrity, dlp_recall | REFERENCE_TESTED | commodity | 24.0 |
| logging_pipeline | F1 F3 F4 | 04 13 18 25 27 | monitor/attester | audit_before_effect | effects_only_via_dispatcher, log_records_canonicalised, log_anchor_external, serving_logging_invariant | REFERENCE_TESTED | commodity | 40.0 |
| trusted_monitor_audit | F2 F6 F8 | 15 21 24 25 | monitor | reserved_budget, non_vacuous_horizon (partial) | schedule_not_observable, per_history_recall, honeypots_indistinguishable, halt_on_catch, complete_observation | REFERENCE_TESTED | commodity | 40.0 |
| human_approval | F3 F5 F7 | 10 16 19 23 26 | approver | approval_channel_integrity | approver_sees_exact_payload, approver_competence | REFERENCE_TESTED | commodity | 20.0 |
| incident_halt | F3 F5 F8 | 12 13 25 26 28 | halt | halt_absorbing_runtime, inflight_effects_enumerated, kill_completeness (partial) | halt_delivery_bound, sink_fencing | REFERENCE_TESTED | datacenter | 2.22 |

Totals: 11 REFERENCE_TESTED, 6 MODEL_ONLY. Every SC-01..SC-28 maps to at least one component, and every F1–F8
family is used.
- **Joined manifests:** 17 CONDITIONAL and 11 DRAFT (`scenarios/INDEX.md`). Of the CONDITIONAL ones, only SC-01,
  SC-03, SC-13, SC-26 and SC-28 cite runtime evidence; the rest are model-only. None is deployment-assured.
- **Scores rose for several components** because the new models named premises that were previously implicit (for
  example `taint_propagation`, `sink_fencing`, `halt_on_catch`). Scores are not comparable across versions of the
  data.

### 2b. Trusted component, the premise it must discharge, and what the repo has

| component | the TRUSTED gate / meter / monitor | model premise it must discharge | repo already has |
|---|---|---|---|
| researcher workstation | Pinned Lean kernel and fail-closed checkers; an independent reviewer | statement fidelity; independently rooted evidence | `tools/check_scenarios.py`, `tools/ctrlcert.py` (+ tests), `THEOREM-REGISTRY.md` |
| agent sandbox (gVisor/Firecracker/Kata/bwrap) | Sandbox runtime + host kernel + out-of-sandbox tool broker | **complete mediation**; policy integrity; privilege lattice | `Core/Gate.lean`; `Scenarios/SC08Exec.lean`, `SC09Priv.lean`, `SC10Policy.lean`, `SC12Persistence.lean`, `SC23Injection.lean` (models with one witness per check); `ledger/SANDBOX2.lean`; `egress/` slice (62 controls); SC-28 run-1 (processes stay in their lineage); **refuted** page-cache premise (`gateway/scenario/results/local-cache.json`) |
| code review + CI/CD | Deploy admission verifier on an agent-proof builder | **consume-by-digest**, distinct reviewer, signing-key custody | `Scenarios/SC16Deploy.lean` (`sc16_safe`, `toctou_slot_breaks`); `Scenarios/SC25Audit.lean` (`sc25_safe`, `nonatomic_check_race_breaks`); `F4/GateClients.lean`; `trusted_stack/` (SQLite release row only) |
| secrets / KMS / HSM | KMS/HSM usable only by non-agent principals | **credential separation**; anti-rollback of nonce history | `tools/test_trusted_stack_broker.py` (live `SO_PEERCRED`); `gate_credential_leak_breaks`; `LifetimeLedger.restore_breaks` |
| cloud control plane & IAM | Credential-holding API proxy; provider billing as meter | credential separation; **idempotent external API**; trusted spend meter **before** the effect | `Scenarios/SC26Transaction.lean`; **SC-26 evidence run-1 PASS** (`scenarios/SC-26/evidence/run-1/`; recheck `tools/check_sc26_case.py`: CONDITIONAL on the committed tree); `Core/Compose.lean` + `Witnesses/DeputyBridge.lean` (cross-gate deputy); `SC28Budget.reported_cost_breaks` |
| schedulers (Slurm, K8s + Kueue/Volcano) | Scheduler accounting + cgroups as meter | **kernel-enforced hierarchical cap**; one global counter; revocation reaches running work | `F5/Lease.lean` (`lease_safe`, `fork_without_lease_accounting`); `SC28Budget.lean`; `gateway/test_lifetime.py`; single-host cgroup v2 meter **PASS** under `prereg/SC28-CGROUP-METER.md` (`scenarios/SC-28/evidence/run-1/`) |
| GPU multi-tenancy (MIG/MPS/time-slicing) | Driver/hypervisor partitioning + placement policy | memory scrubbed between tenants; **measured side-kernel mass** | `SideChannel.lean`; `Core/Leakage.lean`; `F2/ChannelInstances.lean` (`gpu_bound`, `gpu_partition`, `gpu_jitter`); `CovertNoGo.one_bit_coordinates`; prereg draft GPU-1 |
| NVLink/NVSwitch, IB/RoCE | Fabric/subnet manager partitions; NIC/IOMMU | **RDMA mediated at NIC/fabric**, not at host | generic gate shape only |
| DCGM telemetry | Out-of-band collector | **meter not agent-writable**, upper bound, bounded lag | `SC28Budget` assumes it; nothing measures it |
| power / thermal channels | Sensor access policy | sensors hidden or channel measured | side-channel accounting only |
| confidential computing (H100/Blackwell CC, SEV-SNP, TDX) | HW root + attestation verifier gating key release | **independent attestation root**; agent outside the TCB | F4 digest-gate shape only |
| weight storage & egress | Storage IAM + egress byte meter | **lifetime egress byte budget**; reads scoped to serving | lifetime-ledger shape (`CovertChannel.covert_bound_lifetime`) |
| egress proxies / DLP | Pinned-destination proxy; DLP as monitor only | **all routes through proxy**; allowed destination ≠ bounded channel | `EgressGate.lean`; `egress/` (CONDITIONAL, 62 controls, mutations) |
| logging / audit pipeline | Gate-written append-only audit | **audit before effect**; external anchor | `AuditDispatch.lean`, `auditgate/` (PostgreSQL, 27 cases); `Scenarios/SC18Logging.lean` (log-before-release); `F2/ChannelInstances.log_channel` (SC-04); documented no-go in `auditgate/FIDELITY.md` |
| trusted monitors (F6 audit budget) | Trusted monitor + hidden precommitted schedule | **complete observation**; per-history recall; schedule not observable | `F6/ReservedAudit.lean`, `F6/ReservedRecall.lean`, `F6/DamageBound.lean` (expected damage before halt-on-catch), `F6/MonitorCollusion.lean` (honeypot transfer ≤ TV, canonicalised channel); `trusted_stack/audit.py`; near-vacuous certificates |
| human approval | Distinct approver on exact payload digest | approver sees the exact payload; measured rejection rate | `F4/GateClients.lean` `approval_safe`; broker UID tests; SC-26 run-1 (approver's own log reconciled; distinct/payload controls fire c3/c2); `SC23Injection.paraphrase_confirmation_breaks` |
| incident response / kill switch | HALT controller outside agent authority | **sink fencing** (epochs checked at every sink); bounded HALT delivery only for unfenced sinks; kill completeness | `Core/Gate.lean`; `HaltLiveness`; **`F3/DistributedHalt.lean`** (fencing: 0 accepted after t0+ε independent of delivery); SC-26 run-1 (nothing sent after HALT, in-flight reported); SC-28 run-1 H4 (52 processes killed ≤ 1.0 s, one host) |

Attack and failure literature per component is in the JSON. It names well-known public works only: LeftoverLocals
(2024), Spectre (2018), NetSpectre (2018), Foreshadow (2018), Platypus (2020), Hertzbleed (2022), SolarWinds
(2020), RFC 6962, Hardy's confused deputy (1988), FLP (1985), Greenblatt et al. AI Control (2023), Axelsson
base-rate fallacy (2000), RAND on securing model weights (2024), Tramèr et al. on model extraction (2016) and
Pythia (RDMA, 2019). Everything else is described as a generic attack class.

---

## 3. What changes at datacenter scale

**Multi-tenant GPUs move the observation boundary below the OS.**

- On one host, SC-01 showed that the sole-transcript premise fails through a shared page cache (64/64 bits).
- On GPUs the same premise depends on the driver, firmware and partitioning mode.
  - MIG partitions memory and SMs.
  - MPS and time-slicing share far more.
  - Residue between tenants is a demonstrated class (LeftoverLocals).
- **Working rule:** assume a channel exists until a preregistered probe bounds its side-kernel mass. The bound itself
  comes from `SideChannel.side_bound` and `ctrlcert probe`.
- `F2/ChannelInstances.gpu_bound` gives the time-slicing contention channel its parameter, Σ_o max_s W(s,o) per
  quantum. Partitioning gives Σ = 1 (`gpu_partition`). `prereg/GPU1-RESIDUE-CONTENTION-DRAFT.md` would measure W.
- `CovertNoGo.one_bit_coordinates` says F2 bandwidth limits cannot stop coordination, so the control for SC-05 at
  scale is F1 on the action, plus a **placement policy** that never co-locates an agent and its monitor (SC-24) on
  one GPU.

**Fabrics bypass the host gate.**

- One-sided RDMA, GPUDirect and NVLink peer copies never traverse the host kernel. The `egress/` observers, and any
  host-side proxy, see nothing.
- The F1 gate therefore has to move to the NIC, switch or fabric manager: partition keys and restricted memory
  registration.
- NCCL collectives are a shared channel among all ranks of a job, so the "receiver" in SC-01 terms is the whole job.

**HALT becomes a distributed-systems problem.**

- `Gate.withHalt` is absorbing *by construction*, and `HaltLiveness.liveness_if_delivered` is conditional on delivery.
- At cluster scale, delivery is the hard part. Without timing assumptions there is no bounded-delay guarantee (FLP),
  and partitions leave partially halted fleets.
- `SC26.inflight_after_halt` shows that effects already in flight still complete.
- **`F3/DistributedHalt.lean`** quantifies both regimes:
  - without fencing, effects landing after t0 number ≤ n·ρ·(L + Δ) (`landed_after_le`), and a partitioned node lands
    unboundedly many (`partition_unbounded`);
  - with sinks that reject stale epochs, accepted effects after t0 + ε are **exactly 0** whatever the delivery
    (`fenced_after_eps`), provided workers cannot obtain the new epoch (`token_leak` shows that premise is needed).
- Practical consequences:
  - Measure **time-to-quiescence**: the distribution of time until no new external effect occurs, not time until
    processes die.
  - Order the HALT layers:
    1. **Bump the fencing epoch at every effect sink, and revoke credentials and leases.** This bounds effects
       independently of whether each node hears the HALT. Under F1 credential separation every external effect
       needs a credential, so revocation at the idempotent external system is the cheapest global halt.
    2. Stop scheduler admission.
    3. Kill running work.
    4. Quarantine the network.
  - Credential separation is therefore what makes HALT tractable at all.

**Telemetry becomes the trusted meter, and it is lossy and late.**

- `SC28Budget` assumes a trusted meter charging at least one unit per step, and `reported_cost_breaks` shows that
  self-reporting fails.
- At scale the meter is DCGM, cgroups or billing. These are sampled, which leaves gaps an agent can time bursts into.
  Billing is also delayed.
- So a hard cap needs **pre-authorisation**: charge before work, as SC-26 reserves before delivery. The meter then
  reconciles after the fact. The meter itself must be out-of-band (host or BMC side), never inside the tenant.

**Attestation roots replace "same-host evidence".**

- SC-27 is DRAFT precisely because self-signed same-host evidence is not independent.
- Confidential computing (GPU CC mode with SEV-SNP or TDX) gives a hardware root for *node state*. It can serve as the
  F4 gate for runtime: release weight keys only to measured, reviewed configurations.
- It protects the workload from the operator, though, and says **nothing about the agent's behaviour when the agent
  is inside the TCB**. Side channels are typically outside vendor TEE threat models.

**Audit budgets become human-hours and queues.**

- False-positive exhaustion (`Necessity.exhausted_no_audit`) is a fleet-level property. The reserved hidden schedule
  (`ReservedAudit.reserved_policy_bound`) is the positive counterpart.
- Time-to-response becomes queueing delay, which interacts with irreversible actions (SC-25): those need
  check-before-effect, not after-the-fact audit (`SC25Audit.fail_open_timeout_breaks`).
- `F6/DamageBound.damage_bound` turns audit rates into expected damage: E[damage] ≤ D·Σ_j hypMiss(N, Bh, j, r).
  It needs a per-step cap D and a halt on the first catch; `no_halt_damage` shows that logging a catch without
  halting gives no bound.
- `F6/MonitorCollusion.pass_transfer` says honeypot-measured recall transfers to real attacks only up to the total
  variation between their view laws. A steganographic flag makes that 1 (`stego_fools_honeypots`), so honeypots need a
  canonicalised monitor input.

**Composition (F8) crosses clusters.**

- A global budget (SC-28) needs one durable counter. Across regions that costs latency or availability.
- `GateComposition.confused_deputy_counterexample`, and its instance on real gates
  `DeputyBridge.payment_deputy_breaks_deploy_gate` (SC-26 × SC-16), are the reminder that individually safe gates are
  not jointly safe. `Core/Compose.admissible_of_step` gives the positive rule: a cross-domain deputy must issue the
  target gate's own operation.

---

## 4. Next 10 practical tests, ranked by value/cost

SC-26 run-1 and SC-28 run-1 were items 1 and 4 of the previous list, and both PASSED. The list below ranks what
remains:
- **Value** is the open premises discharged × the scenarios unblocked, now preferring premises that already have
  Lean necessity witnesses, which double as ready-made negative controls.
- **Cost** is hardware tier plus build effort.

Each harness should be scaffolded with `tools/new_scenario.py` and preregistered before evidence (see
[docs/RESEARCHER-WORKFLOW.md](docs/RESEARCHER-WORKFLOW.md)).

| # | test | tier | component → premises | scenarios | acceptance (preregister first; controls = Lean witnesses) |
|---|---|---|---|---|---|
| 1 | **Sandbox battery** for SC-08/09/10-11 under bubblewrap, gVisor and Firecracker, with an out-of-sandbox effect observer (auditd/eBPF) | commodity (days) | agent_sandbox → exec_allowlist, privilege_lattice, policy_integrity | SC-08, 09, 10, 11 | Zero unlogged effects. Each control fires its witness: `path_allowlist_toctou_breaks`, `interpreter_loophole_breaks`, `exec_without_attenuation_breaks`, `confused_deputy_breaks`, `stale_cache_breaks`, `path_toolchain_breaks` |
| 2 | **Cross-boundary page-cache probe**: rerun `cache_probe.py` with sender and receiver in separate gVisor and Firecracker instances | commodity (existing code) | agent_sandbox → co_tenant_side_channels (REFUTED for bwrap) | SC-01, 04 | Clopper–Pearson lower bound via `ctrlcert probe`; refutation persists (record it) or mass ≤ 1.10986; never pooled with the bwrap receipt |
| 3 | **Log-before-release proxy + canonical logs** (SC-18, SC-04) in front of a toy inference server | commodity | logging_pipeline → serving_logging_invariant, log_records_canonicalised | SC-04, 18 | No response released before a durable sink ack. Controls: `release_before_log_breaks`, `agent_writable_config_breaks`, `fail_open_outage_breaks`, `free_text_leaks` |
| 4 | **Fencing sink, one-host rehearsal of DC-1**: worker processes or VMs write to an epoch-checking sink; HALT bumps the epoch | commodity | incident_halt → sink_fencing | SC-12, 25, 26, 28 | 0 accepted writes after t0+ε; controls `partition_fenced` (blocked HALT delivery) and `token_leak` (worker given the new epoch) fire |
| 5 | **SC-25 audit-before-execute queue** with catch → HALT wiring | commodity | logging_pipeline → effects_only_via_dispatcher; trusted_monitor_audit → halt_on_catch | SC-13, 25 | Every execution has a passing verdict for its exact digest at fire time. Controls: `nonatomic_check_race_breaks`, `fail_open_timeout_breaks`, `digest_unchecked_breaks`, `no_halt_damage` |
| 6 | **Deploy admission**: local OCI registry, signer key in SoftHSM, admission webhook, against `SC16Deploy` | commodity | code_review_cicd → consume_by_digest (real deploy), signing_key_custody; secrets_kms → signer_unforgeability | SC-16, 17, 27 | The running digest equals the approved digest, checked independently. Controls: `toctou_slot_breaks`, `self_review_without_distinct_check`, `no_target_binding_breaks` |
| 7 | **SC-23 taint scaffold** with scripted (non-LLM) injected tool results and an exact-value confirmation UI | commodity | agent_sandbox → taint_propagation; human_approval → approver_sees_exact_payload | SC-23 | No sensitive action on tainted arguments without an exact one-use confirmation. Controls: `summarizer_drops_taint`, `paraphrase_confirmation_breaks`, `confirmation_reuse_breaks` |
| 8 | **Anti-rollback anchor** for the SC-26 gate DB and the SC-28 accounting store (external monotonic counter), then SC-28 under single-node Slurm or Kueue | commodity | job_scheduler, secrets_kms → anti_rollback | SC-26, 28 | A snapshot restore is detected and refused (the `rollback_double_spends` shape); jobs submitted from inside jobs are charged to the parent lease |
| 9 | **CLOUD-1**: the SC-26 gate against a provider's test-mode payment API with idempotency keys (`prereg/CLOUD1-SANDBOX-PAYMENT-DRAFT.md`) | commodity + a sandbox account; **owner approval** | cloud_control_plane → idempotent_external_api, credential_separation on a real provider | SC-26 | As in the draft: H3 32 requests × 5 retries give exactly 32 charges; the dedup control (no key) produces c5 |
| 10 | **GPU-1**: residue between tenants and the time-slicing contention channel (`prereg/GPU1-RESIDUE-CONTENTION-DRAFT.md`) | **one GPU**; **owner approval** | gpu_multitenancy → memory_scrub_between_tenants, partition_observation_boundary | SC-01, 04, 05, 07, 24 | Residue per arm with its upper bound; Σ_U per arm plugged into `gpu_bound`; positive and negative controls fire |

**Hardware tiers:**
- Tests 1–8 need one commodity Linux box or VM with root.
- Test 9 also needs an external sandbox account and an approved egress exception.
- Test 10 needs one GPU.

**Next at datacenter tier:**
- DC-1 proper on ≥ 3 hosts (`prereg/DC1-DISTRIBUTED-HALT-DRAFT.md`);
- fabric partition enforcement (IB pkeys / NVSwitch);
- attestation-gated weight-key release on CC-mode GPU nodes.

**Next commodity item after these:** the egress-limits test (encoded exfiltration through an allowed destination,
plus a Soft-RoCE RDMA write invisible to the host observer). The SC-07 egress-quota harness on this branch is still
uncommitted and is not cited.

---

## 5. Honest limits

- **No novelty claims.** Every Lean theorem cited here is an induction over a transition system or classical
  counting; the repo's own reviews say so (`reviews/sc26-2026-10-09/disposition.md`). The mechanisms named here are
  standard engineering: gVisor, MIG, idempotency keys, two-person rules, attestation and cgroups. If the project
  contributes anything, it is bookkeeping:
  - explicit premise lists;
  - necessity witnesses that make each check falsifiable;
  - a refutation loop that preserves failures.
- **No deployment claim.** Nothing is deployed, and nothing was tested against any lab's infrastructure.
  `REFERENCE_TESTED` means SQLite rows, loopback namespaces, a simulated bank and distinct Linux UIDs on a commodity
  host. No component row implies that a production system has the property.
- **Evidence outcomes are recorded claims.** `stackmap.py` checks that cited files and declarations exist, but it
  does not re-run tests or check Lean.
  - Suites run in these sessions: `trusted_stack` (18 OK) and the SC-26 model tests (10 OK).
  - `tools/check_sc26_case.py` was rerun on 2026-10-09. On a `git archive HEAD` export it rechecks PINS, EVIDENCE,
    H3, SELF_TEST and RAW as OK, and its Lean PROOFS step passed in the working tree. That makes the committed case
    CONDITIONAL.
  - **In the live working tree the same checker reports CHECK_FAILED (PINS)**, because the SC-26 harness files
    pinned in PREREG-SC26-TXGATE-v2 carry uncommitted edits. Any new run with those edits needs a new
    preregistration ID.
  - The egress, auditgate and broker outcomes are taken from their receipts and the CI records in `COMPLETED.md`.
- **Concurrent work.** This map cites only committed artifacts. SC-07's egress-quota harness and
  `prereg/SC07-EGRESS-QUOTA.md` were uncommitted when it was refreshed, so they are not cited. Rerun `stackmap.py`
  after new evidence lands.
- **Mapping judgments are mine and unreviewed.** That includes which scenarios belong to which component, what counts
  as the "decisive tier", and which artifact discharges a premise (for example, OS-UID separation as reference
  evidence for "credential separation" at a cloud API). They should be reviewed like any other statement.
- **The priority score is a heuristic** for ordering work. It is not a risk estimate.
- The ceiling from ROADMAP still applies: this produces machine-checked conditional accounting, refutations and
  experiment design for narrow protocols. It does not produce deployment guarantees for LLM agents.

---

## 6. Tool reference

- **Validation (fail-closed, exit 1).** The tool rejects:
  - unknown or missing keys, and duplicate JSON keys;
  - a family outside F1–F8, or an unknown role, tier, layer, evidence kind or outcome;
  - a scenario id without `scenarios/<id>/manifest.json`, or a manifest whose id doesn't match its folder or that
    lacks one of the four axes;
  - any cited path (evidence, model, necessity, related, or a repo-relative path inside a `researcher.run` command)
    that is missing, absolute or escapes the repo;
  - a named Lean declaration not found in its file;
  - a necessity witness without a declaration;
  - a decisive tier with no practical test text;
  - a declared status that differs from the status derived from evidence.

  Unknown `--researcher` component → exit 2.
- **Gap score:**

  ```
  score = (2·GAP + 2·REFUTED + 1·(MODELLED or BUILT_NOT_RUN)) × #scenarios / tier_cost
  ```

  `tier_cost` is commodity 1, gpu 3, datacenter 9. Ties break by id. It favours open premises that block many
  scenarios and can be tested cheaply.
- **Blocking assumptions** in the scenario join are manifest assumptions with any axis outside {proof:
  THEOREM_VERIFIED; evidence: RUNTIME_VALIDATED; applicability: ESTABLISHED; usefulness: MET_RECORDED}, where
  NOT_APPLICABLE also counts as clear for proof, evidence and usefulness. A `!` marks an OBSERVED_FAILURE or REFUTED
  axis.
- **Adding a component:** append a row to `stack/components.json`, cite only files that exist, and declare the status
  the evidence supports. Then run `python3 tools/stackmap.py --validate` and `python3 -m unittest tools/test_stackmap.py`.
  The real-data tests require every SC-01..SC-28 to stay mapped.
