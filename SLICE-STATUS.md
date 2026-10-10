# Deployment slice status — 2026-10-10

One scoped, conditional assurance case; no merge and no scenario status promotion.
Base: `main` at `8d4bd45`. Branch: `sol/deployment-slice-20261010` in the independent
clone `/var/tmp/sol-deployment-slice-20261010`. Claim: `docs/DEPLOYMENT-CLAIM-v0.md`.

## Lean proof scope and axioms

`ControlStack.Deployment` derives `exclusive_sink`, `database_custody`,
`agent_not_receiver_uid` and `agent_call_legal` from checked finite IR facts.
`runtime_exclusive` transfers authority only under faithful runtime inclusion.
`deployment_safe` joins that inclusion, actual caller identity binding and faithful
protocol/publication abstraction with existing exact approval, deduplication and
budget safety. There is no bare CompleteMediation axiom. The runtime-faithfulness
package is substantive and unproved; it includes implementation correspondence.

`protocol_safe` reuses `SC26.sc26_safe`, `one_use` reuses `SC26.sc26_once`,
`gate_contract` reuses `Gate.Spec.trace_safe`, and `broker_contract` reuses
`TrustedBroker.trace_preserves`. `clean_accepted` and `useful_acceptance` provide
nonempty useful acceptance, including two agents contending for capacity one.
`check_disabled_counterexample` reuses the payload-check-disabled counterexample.
`writable_mount_refutes` and `unknown_refutes` falsify accepted IR facts.

The checked axiom output is in `deployment-evidence/contract-axioms.txt`; all reports
use only `propext`, `Quot.sound`, or no axioms. Each CLI matrix bundle also embeds
its generated raw IR projection, `facts_checked` or `facts_refuted`, model role and
budget contract instances, and nine axiom reports. No proof uses prohibited tokens
or a premise whose proposition is simply True. Existing SC26 legality is derived
for direct agent calls from UID facts; other operation constructors retain their
existing model semantics.

## Runtime checks and independent sink evidence

Host attempt: `sudo -n python3 tools/run_deployment_boundary.py --output
/var/tmp/sol-deployment-runtime-20261010`. **FAILED**: Landlock syscall 444 returns
errno 95. Host kernel has CONFIG_SECURITY_LANDLOCK=y but active LSMs omit Landlock.
The launcher fails closed. Two host confinement unit checks skip; these are not
positive enforcement evidence. Failure trace: `deployment-evidence/host-confinement-failure.txt`.

The complete check then ran on this box in an offline aarch64 QEMU guest using an
already installed local kernel/rootfs and installed Python/libseccomp. No download,
network device, host LSM change or accounts were needed. Commands and asset pins:
`deployment-evidence/vm-command.txt`, `vm-assets.sha256`. The guest executed
`python3 tools/run_deployment_boundary.py --output /tmp/slice-runtime` and exited
0; final console shows clean power-down in `deployment-evidence/vm-console.txt`.

Raw sink files and observations are exported into
`deployment-evidence/runtime-vm/slice-runtime/`. The independent checker is
`python3 tools/check_deployment_evidence.py deployment-evidence/runtime-vm/slice-runtime`.
It reads actual archived sink bytes, hashes each against the observer snapshots,
checks current trusted source pins, and supplements them with the persisted SQLite
shared-budget/HALT state. It does not substitute the gate log for sink state.

- `clean-inflight-sink.json` and `clean-after-halt-sink.json`: exactly `1.body`,
  containing `exact-reviewed-two-agent-slice`. Two confined agents use one shared
  budget; the second release and nonce replay are denied. During real receiver
  publication, a trusted test hook pauses after durable publication and before
  receipt commit; concurrent HALT waits on the SQLite writer lock, then commits.
  Published bytes remain; subsequent delivery is denied.
- `writable-sink-mount-sink.json`: native permission/authority analogue of a writable
  mount produces `writable-mutation.body` through a direct unconfined helper.
  A separately confined agent write remains denied by Landlock. This test does not
  claim that a Docker mount was launched or that confinement alone was bypassed.
- `trusted-role-uid-collision-sink.json`: a direct helper with the trusted owner UID
  produces `uid-collision.body`. The authenticated launcher refuses same-UID
  broker attachment. This is a concrete authority failure and a launcher negative.

These are native reference-boundary checks, not attestation that synthetic Compose
images/inventories ran. Temporary UIDs exist only in processes; processes are
reaped, ownership restored, socket removed, and the guest powers down.

## Fixture results

Expected/actual results and exact scan/verify/report commands are recorded in
`deployment-evidence/matrix/matrix.json`. Every case is kernel-checked from its raw
IR projection; policy authorization is never used to remove reachability.

| Fixture | Expected | Actual |
|---|---|---|
| clean | CONDITIONAL | verification in progress |
| writable-sink-mount | UNASSURED | verification in progress |
| agent-broker-db-access | UNASSURED | verification in progress |
| trusted-role-uid-collision | UNASSURED | verification in progress |
| privileged-container | UNASSURED | verification in progress |
| host-network | UNASSURED | verification in progress |
| alternate-deputy-sink-credentials | UNASSURED | verification in progress |
| unknown-feature | UNASSURED | verification in progress |

## UNKNOWN and residual premises

Faithful extraction and protocol abstraction, exhaustive scoped process/capability
coverage, source/image correspondence, real OS caller identities, mount aliases,
trusted clock, byte/hash binding, approval semantics, kernel/storage correctness
and no rollback remain trusted assumptions. Runtime tests sample boundaries and do
not discharge these universally. Caller-supplied runtime inventories are unauthenticated.
The clean fixture uses invented image digests and a synthetic inventory. UNKNOWN
features, missing runtime facts, drift and reachable policy-forbidden paths produce
UNASSURED; syntactically invalid inputs/pin mismatch produce usage failure (2).
All scenario manifests, frozen evidence and EgressGate remain unchanged.

## Vacuity self-check

| Contract | Falsifying mutation / negative control |
|---|---|
| exclusive_sink / runtime_exclusive | writable sink mount; alternate deputy sink credentials; omitted real writer falsifies faithfulness |
| database_custody | agent broker-DB access |
| agent_not_receiver_uid / agent_call_legal | trusted-role UID collision |
| Accepted finite facts | privileged container, host network, UNKNOWN feature |
| protocol_safe / deployment_safe exact approval | disabled payload check: check_disabled_counterexample / SC26.payload_unchecked_breaks |
| one_use | disabled nonce check: SC26.nonce_protects_budget_only |
| gate_contract | disabled payload check falsifies the client's invariant; no reject-all usefulness: useful_acceptance |
| broker_contract shared budget | bypass broker DB custody or disable cap guard; TrustedBroker release guard and SC26.no_cap_breaks |
| sink deduplication portion | SC26.no_dedup_retry_duplicates / no_dedup_breaks_cap; actual receiver retry test |
| HALT boundary (runtime only) | new post-HALT delivery denied; already published in-flight bytes persist |

## Failures and dead ends

The first fixture test failed because the UNKNOWN reason omitted its fixture label;
fixed with an explicit unknown-feature diagnostic. Host confinement is unavailable
as described above. First guest run completed all runtime assertions and exported
evidence, then failed shutdown because /bin/poweroff was absent; the builder was
fixed to /sbin/poweroff and the full guest check rerun to clean power-down.

An initial fast check was 29/39: several existing script imports lacked the repo
on PYTHONPATH, copied Lean cache lacked moved Core modules, and two existing tests
required root. cstack now supplies repo PYTHONPATH; necessary Lean prerequisites
were rebuilt. Existing generated result pages had two stale test-command listings
and were regenerated with build_results. The full ledger must be generated with
Lean to retain its Lean section; no hand editing of generated files was used.

## Commands, CI and draft PR

- `lake build ControlStack.Deployment.Contracts`: PASS.
- `lake env lean ControlStack/Deployment/Contracts.lean`: pending final archived output.
- `python3 tools/test_deployment_slice.py`: PASS, nine tests.
- `python3 tools/test_deployment_runtime.py`: PASS, 17 tests, two host kernel skips.
- `python3 tools/test_deployment_evidence.py`: PASS, archived raw sink checks.
- `python3 tools/test_deployment_lean.py`: PASS, all eight raw fixture instances.
- `python3 tools/run_deployment_matrix.py --output deployment-evidence/matrix --lean`: final rerun pending boundary attachment.
- `python3 tools/cstack.py check --fast`: final result pending.
- Generated registry, statement catalog, overview, ledger, trust-root and results
  `--check`: final audit pending.
- Draft PR: pending publication. CI state at head: not yet published.

Stopping scope: one conditional assurance case. Follow-ups are in
`docs/DEPLOYMENT-SLICE-NEXT.md`; no HTTP/Kubernetes/remediation expansion.
