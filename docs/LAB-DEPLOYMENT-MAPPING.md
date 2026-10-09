# Lab deployment mapping: realising the trusted components of the modelled scenarios

**Status: DESIGN PROPOSAL. Nothing here is tested on lab infrastructure, and nothing is deployed.**

For each scenario or family with a Lean model, this page names how a frontier lab could realise the model's TRUSTED
components with widely known infrastructure categories, and which model premise each component would discharge. Each
mapping is phrased "if configured so that … then premise P holds". It makes no claim about any product's actual
guarantees, defaults or failure modes. Those must be checked for the specific system and version, and each one is a
correspondence obligation in the sense of [RUNTIME-VM-HANDOFF.md](../RUNTIME-VM-HANDOFF.md) §10.

**Evidence column:**

| value | meaning |
|---|---|
| `model` | Lean theorem only. |
| `ref` | A single-host reference implementation passed a preregistered run in this repo (SC-26 run-1, SC-28 run-1). |
| `none` | Nothing. |

Every lab row is untested. Component ids refer to [stack/components.json](../stack/components.json). Status per
scenario is in its `scenarios/SC-XX/manifest.json`, and [ROADMAP.md](../ROADMAP.md) is canonical.

A note that applies to every section: the models are inductions over transition systems. Their value is the exact
premise list, plus the necessity witnesses that show each premise is load-bearing. A premise left undischarged makes
the theorem inapplicable; it does not make it "mostly true".

---

## SC-26: irreversible external action (payments, access changes)

Model: `ControlStack/Scenarios/SC26Transaction.lean` (`sc26_safe`, `sc26_safe_disjoint`, `sc26_once`, `halt_freezes`).
Evidence: `ref`. Run-1 passed under PREREG-SC26-TXGATE-v2 (17/17 attacks, 7/7 specific controls, 64/64 with 16
crashes). `tools/check_sc26_case.py` rechecks it as CONDITIONAL from the committed tree.

| Model premise | Lab realisation (if configured so that …) | Evidence |
|---|---|---|
| Receiver idempotency (`bankDedup`; witness `no_dedup_retry_duplicates`, `no_dedup_breaks_cap`) | A payment or cloud API that accepts **idempotency keys**: if every call carries the gate's request id as the key, and the provider deduplicates on it over the whole retry horizon, then crash/retry is exactly-once at the receiver | ref (simulated bank) |
| Receiver authentication (`bankAuth`, `legal`; `gate_credential_leak_breaks`) | **Workload identity** (short-lived, OIDC-federated service credentials): if only the gate's workload identity is authorised for the payment/IAM-mutating API, and agents' identities lack that permission, then credential separation holds | ref (OS UIDs) |
| Approver separation and role disjointness (`distinct`, `sc26_safe_disjoint`) | **Multi-party approval** in a KMS/IAM or workflow system: if approvals are issued only by principals in an approver group disjoint from agent principals, and the approval is bound to the exact request digest, then the distinct-approver premise holds | ref (OS UIDs) |
| Exact payload (`payload`; `payload_unchecked_breaks`) | Signed transaction intents: if the approver signs a digest of (destination, amount, memo, request id) and the gate verifies it against the stored request, then payload binding holds | ref |
| Cap before effect (`cap`; `no_cap_breaks`) | **Budgets and quotas** enforced at reservation time in the gate, with provider-side spending limits as a second layer: if the gate charges before sending, then the cap holds without relying on delayed billing | ref |
| HALT and in-flight (`halt_freezes`, `inflight_after_halt`) | An admin-only kill flag checked on every send, plus credential revocation: if no send happens after the flag, then only already-sent calls can land | ref |

The SC-26 model does not cover: whether a human approver understands the payload, privileged rollback of the gate
database, multiple gates sharing one credential, or effects that are not idempotent.

## SC-28: joint budget across agents and forks

Model: `ControlStack/Scenarios/SC28Budget.lean` (`sc28_safe`, `revoked_lease_stops`, `fork_shares_lease`; witnesses
`no_global_counter_breaks`, `fresh_fork_escapes_revocation`, `reported_cost_breaks`, `rollback_double_spends`).
Evidence: `ref` (SC-28 run-1, cgroup v2 on one host, H1–H5 5/5).

| Model premise | Lab realisation | Evidence |
|---|---|---|
| Trusted meter (`reported_cost_breaks`) | **cgroup v2** accounting under the scheduler (Kubernetes pods, Slurm job cgroups), and **NVIDIA DCGM**-style GPU accounting collected host-side: if usage is read from the kernel or host collector and never from the job, then cost is not under-reported | ref (CPU/pids only) |
| Fork lineage (`fork_shares_lease`) | Hierarchical cgroups and job containment: if every descendant, including daemonised ones, stays in the job's cgroup subtree, then forks share the lease | ref (H1, H5) |
| Global counter (`no_global_counter_breaks`) | **Kubernetes ResourceQuota / Kueue ClusterQueues / Slurm associations and QOS** with one accounting database: if all queues draw on one quota object or one accounting store, then the joint cap holds | none |
| Revocation reaches running work (`revoked_lease_stops`) | Preemption or eviction (`scancel`, pod eviction, `cgroup.kill`): if revocation kills the lease's cgroup rather than only stopping admission, then no further usage accrues | ref (H3) |
| No rollback (`rollback_double_spends`) | An accounting store with an external monotonic anchor (append-only or WORM log of charges): if restoring a snapshot is detectable, then double-spend by rollback is excluded | none |

## F3 distributed HALT: fencing at sinks

Model: `ControlStack/Families/F3/DistributedHalt.lean`.
- `landed_after_le`: the unfenced window is ≤ n·ρ·(L + Δ).
- `fenced_after_eps`: with fencing, 0 effects are accepted after t0 + ε, whatever the delivery delays.
- `fenced_window`, `partition_unbounded`, `token_leak`.

Evidence: `model`, plus `ref` for single-host kill (SC-28 H4).

| Model premise | Lab realisation | Evidence |
|---|---|---|
| Sink checks the epoch on every effect (`fence`) | **Lease/epoch fencing at storage and queue sinks**: storage that supports conditional writes on an epoch field, and message brokers that reject producers holding an old epoch. If every effect-bearing write carries the writer's epoch and the sink rejects stale epochs, then post-HALT effects stop at t0 + ε. | model |
| Only the controller mints epochs (`HoldsOld`; `token_leak`) | Epoch issuance by a coordination service (a consensus-backed lease store) whose write permission is held only by the HALT controller | none |
| Rate ρ and latency L bounds | Per-workload rate limits at the sink, and network timeouts | none |
| Delivery bound Δ (only for unfenced sinks) | **Credential revocation** propagated to every node, and scheduler drain/cordon. This bounds Δ only under a timing assumption (`partition_unbounded` shows what a partition does). | none |

**Practical consequence:** the cheapest cluster-wide HALT is to bump the epoch at every sink and revoke credentials,
and then kill processes. Effects that bypass every fencing sink are outside the model.

## SC-16: ship only what was reviewed

Model: `ControlStack/Scenarios/SC16Deploy.lean` (`sc16_safe`, `sc16_reviewed_content`; witnesses
`toctou_slot_breaks`, `collision_breaks`, `self_review_without_distinct_check`). Evidence: `model` (the
`trusted_stack` digest check is a SQLite reference only).

| Model premise | Lab realisation | Evidence |
|---|---|---|
| Deploy by digest, not by mutable slot (`toctou_slot_breaks`) | **OCI registries addressed by content digest**: if manifests reference `@sha256:` digests and never tags, then the deployed bytes are the approved bytes | none |
| Approval bound to digest and target (`no_target_binding_breaks`) | **Sigstore/cosign-style signing** with an attestation naming the target environment, verified by an **admission controller** | none |
| Reviewer ≠ stager (`self_review_without_distinct_check`) | Required-reviewer rules in code review, with the signing identity tied to the reviewer group, not to the author or the CI runner identity | none |
| Collision resistance on contents in play | SHA-256 digests (standard assumption) | — |

## SC-18: inference logging cannot be disabled

Model: `ControlStack/Scenarios/SC18Logging.lean` (`sc18_safe`, `config_untampered`; witnesses
`release_before_log_breaks`, `agent_writable_config_breaks`, `fail_open_outage_breaks`). Evidence: `model`.

| Model premise | Lab realisation | Evidence |
|---|---|---|
| Log-before-release | A **log-before-release proxy** in front of the serving stack: if the proxy releases a response only after the log sink acknowledges a durable write of its record, then every released response is logged | none |
| Config not agent-writable (`agent_writable_config_breaks`) | Logging configuration in a separately administered config store, or admission policy, with no write permission for agent or model-serving identities | none |
| Fail-closed watchdog (`fail_open_outage_breaks`) | A health check that stops serving when the sink has not acknowledged within T | none |
| Durable acknowledgement | Append-only or WORM-retention storage: if an acknowledgement means a durable commit, then the record survives | none |

## SC-23: prompt injection cannot trigger sensitive tool actions

Model: `ControlStack/Scenarios/SC23Injection.lean` (`sc23_safe`; witnesses `summarizer_drops_taint`,
`paraphrase_confirmation_breaks`, `confirmation_reuse_breaks`). Evidence: `model`.

| Model premise | Lab realisation | Evidence |
|---|---|---|
| Taint propagation (`summarizer_drops_taint`) | **Taint-tracking agent frameworks**, described generically. A planner that sees only trusted input issues tool calls, a separate component processes untrusted data, and every derived value inherits a taint label. If labels propagate through every derivation, including model summarisation, then untrusted influence is visible at the action. | none |
| Exact confirmation (`paraphrase_confirmation_breaks`) | A confirmation UI that renders the exact argument values that will execute, and binds a one-use nonce to them | none |
| Planner never reads untrusted data (provenance premise) | Architectural separation (distinct model contexts or processes) enforced by the scaffold, not by prompting | none |

## SC-25: audit before irreversible execution

Model: `ControlStack/Scenarios/SC25Audit.lean` (`sc25_safe`, `expired_never_executes`; witnesses
`fail_open_timeout_breaks`, `digest_unchecked_breaks`, `nonatomic_check_race_breaks`, `agent_declared_class_breaks`).
Evidence: `model`.

| Model premise | Lab realisation | Evidence |
|---|---|---|
| Executor is the only path | Workflow engines and job queues whose workers hold the only credential for the effect (as SC-26) | none |
| Atomic re-validation at fire time (`nonatomic_check_race_breaks`) | Compare-and-set on the queued item's content digest at execution (transactional dequeue) | none |
| Fail-closed timeout (`fail_open_timeout_breaks`) | A queue TTL that expires unaudited items instead of executing them | none |
| Trusted classifier (`agent_declared_class_breaks`) | An irreversibility classification owned by the platform team, not by the submitting agent | none |

## SC-12: no persistence beyond the session

Model: `ControlStack/Scenarios/SC12Persistence.lean` (`sc12_safe`, `no_fire_after_end`; witnesses
`registry_bypass_survives`, `parent_only_revocation_survives`, `foreign_registration_survives`). Evidence: `model`,
plus `ref` for processes (SC-28 H1/H3).

| Model premise | Lab realisation | Evidence |
|---|---|---|
| Every creation path goes through the registry (`registry_bypass_survives`) | Processes in a session cgroup; scheduled jobs only through a platform scheduler API; cloud resources and credentials created only via a provisioning service that tags them with the session. If agents lack direct permissions for cron/systemd, IAM user creation and resource creation, then the registry is complete. | ref (processes) |
| Revocation walks the lineage (`parent_only_revocation_survives`) | Session teardown deletes by session tag (cgroup kill, credential revocation, tagged-resource deletion) | ref (processes) |

## SC-08 / SC-09 / SC-10–11: sandbox execution, privilege and policy integrity

Models:
- `ControlStack/Scenarios/SC08Exec.lean`: `sc08_safe`;
- `ControlStack/Scenarios/SC09Priv.lean`: `sc09_safe`, `spawn_attenuates`;
- `ControlStack/Scenarios/SC10Policy.lean`: `sc10_safe`, `policy_admin_only`.

Evidence: `model`.

| Model premise | Lab realisation | Evidence |
|---|---|---|
| Exec decided on the loaded content's digest (`path_allowlist_toctou_breaks`); interpreters run only allowlisted scripts (`interpreter_loophole_breaks`, `interpreter_repl_breaks`) | Kernel-level exec integrity (IMA-style measurement/appraisal, or an LSM exec hook) and `noexec` scratch mounts. If the allowlist is checked against the file actually mapped, and interpreters are wrapped to require an allowlisted script, then SC-08 holds. | none |
| Attenuation and no setuid gain (`exec_without_attenuation_breaks`) | `no_new_privs`, nosuid mounts, dropped capability bounding sets, user namespaces without host mappings | none |
| Exact elevation rules (`unrestricted_elevation_breaks`) | sudo-style rules pinned to one exact command line, or a privileged broker with typed requests | none |
| Deputies check the caller (`confused_deputy_breaks`) | Privileged daemons that authorise on the caller's identity (peer credentials, workload identity), not on their own | none |
| Admin-only, current policy (`agent_writable_policy_breaks`, `stale_cache_breaks`, `alternate_evaluator_breaks`, `path_toolchain_breaks`) | Policy in a versioned, admin-only config store; enforcers reload by version and refuse stale versions; toolchains invoked by absolute pinned paths, from read-only mounts | none |

## F2 channel instances: GPU contention and log channels (SC-01/02/04)

The model is `ControlStack/Families/F2/ChannelInstances.lean`:
- `gpu_bound`, `gpu_partition`, `gpu_jitter`;
- `log_channel` and the witness `free_text_leaks`;
- `rekey_epoch`.

Evidence: `model`.

| Model premise | Lab realisation | Evidence |
|---|---|---|
| The receiver's view does not depend on the co-tenant (`gpu_partition`, Σ = 1) | Hardware partitioning (MIG-style instances), or never co-scheduling agent and monitor on one GPU. Whether a given mode achieves Σ ≈ 1 must be measured (`prereg/GPU1-RESIDUE-CONTENTION-DRAFT.md`). | none |
| Bounded per-quantum leakage (`gpu_jitter`) | Scheduler-injected jitter or fixed-length time slices; measured Σ_o max_s W(s, o) | none |
| Canonicalised logs (`log_channel`; `free_text_leaks`) | Structured logging with template ids and quantised numeric fields for anything another agent or receiver can read; no free-text fields on that path | none |
| Cross-epoch independence (`rekey_epoch`) | Key and secret rotation per epoch, with no persistent cache carrying old-epoch secrets | none |

## F6: audits, damage and monitor collusion (SC-15/21/24/25)

Models:
- `Families/F6/ReservedAudit.lean`: `reserved_policy_bound`;
- `Families/F6/ReservedRecall.lean`: `adaptive_recall_bound`;
- `Families/F6/DamageBound.lean`: `damage_bound`, `damage_cap_inflight`; witnesses `no_halt_damage`, `no_cap_damage`;
- `Families/F6/MonitorCollusion.lean`: `pass_transfer`, `canon_channel`, `phase_learning`; witness
  `stego_fools_honeypots`.

Evidence: `model`, plus `ref` for the reserved-slot logic in `trusted_stack/test_audit.py`.

| Model premise | Lab realisation | Evidence |
|---|---|---|
| Hidden reserved audit schedule | The schedule is drawn by the audit service from its own randomness, precommitted (for example a hash published before the run), and never visible to agents | ref (logic only) |
| Per-history recall ≥ r | Human or trusted-model auditors evaluated on held-out attacks per history class. This is not available from population ROC. | none |
| Halt on catch and a per-step cap (`no_halt_damage`, `no_cap_damage`) | Catches wired to the F3 HALT path (fencing plus revocation), and per-action caps in the gate (as SC-26) | ref (SC-26 cap) |
| Honeypots indistinguishable (`stego_fools_honeypots`) | Honeypots generated by the same pipeline as real traffic, with a trusted **canonicaliser** on the monitor's input that bounds the shared-codebook channel to log K bits per item | none |
| Complete mediated view | The monitor's input is produced by the gate from the exact action, not by the agent | none |

---

## What would move a row from "none" to evidence

Each row needs its own preregistered run against the real component, with an independent observer and specific
negative controls, on the pattern of SC-26 and SC-28. Drafts for the three runs that need resources this project does
not have:

| draft | what it tests | needs |
|---|---|---|
| [`prereg/GPU1-RESIDUE-CONTENTION-DRAFT.md`](../prereg/GPU1-RESIDUE-CONTENTION-DRAFT.md) | GPU residue and contention channels | one GPU |
| [`prereg/DC1-DISTRIBUTED-HALT-DRAFT.md`](../prereg/DC1-DISTRIBUTED-HALT-DRAFT.md) | Fencing and HALT latency | three or more hosts |
| [`prereg/CLOUD1-SANDBOX-PAYMENT-DRAFT.md`](../prereg/CLOUD1-SANDBOX-PAYMENT-DRAFT.md) | The SC-26 pattern against a provider's test-mode API | a sandbox account |

All three need owner approval and resources before they can be frozen.
