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
budget safety. Its unit-cost faithfulness premise derives a file-count bound as well as the weighted budget bound. Accepted facts also reject zero or unknown role UIDs. There is no bare CompleteMediation axiom. The runtime-faithfulness
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
  mount produces `2.body` through a direct unconfined helper.
  A separately confined agent write remains denied by Landlock. This test does not
  claim that a Docker mount was launched or that confinement alone was bypassed.
- `trusted-role-uid-collision-sink.json`: a direct helper with the trusted owner UID
  produces `3.body`. The authenticated launcher refuses same-UID
  broker attachment. This is a concrete authority failure and a launcher negative.

These are native reference-boundary checks, not attestation that synthetic Compose
images/inventories ran. Temporary UIDs exist only in processes; processes are
reaped, ownership restored, socket removed, and the guest powers down.

## Follow-up scope and real containers

Follow-up handoff: `HANDOFF-SOL-PR45-FOLLOWUP.md`. A and B are implemented;
C ran as **real Docker containers** with the same pinned Compose configurations
that were scanned. No runtime-socket, privileged or host-network fixture was
launched. The offline Alpine rootfs was imported without a network build; trusted
sources and the experiment entry point are baked into content-addressed image
`sha256:7b9a35caabc64d6cc70268c34ab7047d17993b81ac657144a706ec3c2e3d29e3`.
Source hashes and the import archive hash are in
`examples/compose-two-agent/image-pin.json`. Images/inventories in the examples
are no longer invented image references, but static negative inventories remain
synthetic. The imported image was removed after the run.

Commands:

- `python3 tools/build_deployment_container_image.py --output deployment-evidence/container-build`: PASS, offline import.
- `python3 tools/run_deployment_containers.py --output deployment-evidence/containers`: PASS, three real-container cases, using `docker compose up --pull never`.
- `python3 tools/check_deployment_container_evidence.py deployment-evidence/containers`: PASS, current pins, matching Compose, raw daemon facts and archived sink bytes.

Evidence: `deployment-evidence/containers/{clean,writable-sink-mount,trusted-role-uid-collision}/`
contains exact Compose, raw `docker inspect`, normalized runtime inventory, IR,
kernel bundle, observed sink state and actual `sink/*.body` bytes.
`commands.json` records workload/cleanup commands and results; `docker-info.json`
records daemon settings; `cleanup.json` verifies no experiment containers,
networks, volumes, image or scratch directory remains. `postgres:16-alpine` was
left alone. Docker inventory is daemon-derived, **not independent attestation**.
The sink observer reads files directly rather than broker logs.

| Real-container case | Sink-state check | Result |
|---|---|---|
| clean | Exactly `1.body`: `exact-reviewed-two-agent-container-slice`; second agent and replay denied | CONDITIONAL |
| writable-sink-mount | Agent directly publishes `2.body`: `unapproved real container mount` | UNASSURED |
| trusted-role-uid-collision | Empty sink after agent calls HALT as trusted admin; subsequent honest task denied | UNASSURED |

The writable-sink case explicitly changes DAC to 0777 as well as adding a RW bind;
mode 0700 alone would prevent that direct write. UID collision is demonstrated as
admin authority confusion and task suppression, **not** a direct sink write in an
agent container without a sink mount. These containers use Docker default seccomp,
namespaces and numeric UID mapping, **not Landlock**, which is inactive on this
host. The container runtime claim covers mounts and UIDs only. Earlier native
QEMU evidence above separately retains the in-flight HALT/Landlock checks.

## Verdict consistency and differential evidence

Skipped Lean means **UNASSURED**, including the clean fixture. CONDITIONAL needs
successful exact-IR kernel checking and all Python obligations. The permitted
fallback is explicit: Lean's `Accepted` is a **strict subset**. Bundles/reports list
kernel checks versus Python-only role counts, full UID separation, transitive
paths, exact writer sets and runtime drift. `docs/DEPLOYMENT-CLAIM-v0.md` explains
this limitation. No equivalence of Python and Lean is claimed.

`python3 tools/check_deployment_subset_differential.py --output deployment-evidence/subset-differential.json`:
PASS, seed 20261010, **200 kernel-certified mutations, 125 agreements and 75 disclosed subset
differences**. Drift, reviewer UID collision and missing reviewer are accepted by
the kernel subset but refuted by Python, so the final verdict is UNASSURED. Zero
cases were Python-accepted but kernel-refuted. The fixture table also records the
expected subset acceptance separately in `expected.json`; all raw fixture kernel
results are embedded in the matrix bundles.

## Fixture results

`deployment-evidence/matrix/matrix.json` records exact scan/verify/report commands,
actual verdicts and exits. Clean requires `--lean`; all negative fixtures are
UNASSURED even when the documented kernel subset accepts their projection.

| Fixture | Expected | Actual |
|---|---|---|
| agent-broker-db-access | UNASSURED | UNASSURED |
| alternate-deputy-sink-credentials | UNASSURED | UNASSURED |
| channel-target-shadow | UNASSURED | UNASSURED |
| clean | CONDITIONAL | CONDITIONAL |
| credential-password | UNASSURED | UNASSURED |
| daemon-uid-remap | UNASSURED | UNASSURED |
| host-network | UNASSURED | UNASSURED |
| inherited-descriptor | UNASSURED | UNASSURED |
| injected-helper | UNASSURED | UNASSURED |
| missing-isolated-network | UNASSURED | UNASSURED |
| missing-reviewer-role | UNASSURED | UNASSURED |
| mount-parent-alias | UNASSURED | UNASSURED |
| post-capture-drift | UNASSURED | UNASSURED |
| privileged-container | UNASSURED | UNASSURED |
| runtime-alias | UNASSURED | UNASSURED |
| runtime-code-tamper | UNASSURED | UNASSURED |
| runtime-socket-mount | UNASSURED | UNASSURED |
| storage-rollback | UNASSURED | UNASSURED |
| trusted-reviewer-uid-collision | UNASSURED | UNASSURED |
| trusted-role-uid-collision | UNASSURED | UNASSURED |
| trusted-source-mount | UNASSURED | UNASSURED |
| unknown-feature | UNASSURED | UNASSURED |
| unlisted-environment | UNASSURED | UNASSURED |
| unlisted-host-mount | UNASSURED | UNASSURED |
| writable-channel-mount | UNASSURED | UNASSURED |
| writable-sink-mount | UNASSURED | UNASSURED |

## UNKNOWN and residual premises

1. **Faithful extraction**: the snapshot exhausts actual scoped capabilities,
   processes, mount aliases, inherited descriptors, UID bindings and image/source
   correspondence. Docker-daemon capture remains unauthenticated.
2. **Protocol refinement**: actual implementation transitions, approval/hash
   semantics, unit costs, trusted clock, no rollback and durable publication match
   the model. `RuntimeFaithful.publication : sinkEffects = model.bank` assumes full
   **model–runtime correspondence of sink effects**, not merely faithful IR capture.

Neither is proved by successful example executions or source hashes. Extractor
self-review: `docs/DEPLOYMENT-EXTRACTOR-GAPS.md`. Remaining covert/unobserved cases
are aliases/hardlinks, inherited FDs, injected processes, code/image tampering,
daemon UID remapping, storage rollback and post-capture changes. Each has a fixture
showing reported divergence becomes UNKNOWN/drift; covert divergence is still
missed and invalidates the residual assumptions. No known expressible fact in the
restricted supported configuration profile silently closes an authority path.
All frozen evidence, scenario statuses and EgressGate remain unchanged.

## Vacuity self-check

| Contract | Falsifying mutation / negative control |
|---|---|
| exclusive_sink / runtime_exclusive | writable sink mount; alternate deputy sink credentials; omitted real writer falsifies faithfulness |
| database_custody | agent broker-DB access |
| agent_not_receiver_uid / agent_call_legal | trusted-role UID collision |
| Accepted finite facts | privileged container, host network, UNKNOWN feature |
| protocol_safe / deployment_safe exact approval | disabled payload check: check_disabled_counterexample / SC26.payload_unchecked_breaks |
| one_use | disabled nonce check: nonce_disabled_counterexample (duplicate reserved keys; sink deduplication still prevents duplicate effects) |
| gate_contract | disabled payload check falsifies the client's invariant; no reject-all usefulness: useful_acceptance |
| broker_contract shared budget | bypass broker DB custody or disable cap guard; TrustedBroker release guard and SC26.no_cap_breaks |
| sink deduplication portion | SC26.no_dedup_retry_duplicates / no_dedup_breaks_cap; actual receiver retry test |
| HALT boundary (runtime only) | new post-HALT delivery denied; already published in-flight bytes persist |

## Failures and dead ends

The fidelity audit replaced the deputy fixture’s environment-name-only proxy with a writable sink mount under the trusted owner UID. Broker-channel reachability now derives from a common `/channel` bind rather than being guessed from the role, and direct runtime mutations fsync numeric `2.body` / `3.body` files to stay within the exact protected effect class. Opaque credential names now remain UNKNOWN; they do not prove a reachable authority path.

The first fixture test failed because the UNKNOWN reason omitted its fixture label;
fixed with an explicit unknown-feature diagnostic. Host confinement is unavailable
as described above. First guest run completed all runtime assertions and exported
evidence, then failed shutdown because /bin/poweroff was absent; the builder was
fixed to /sbin/poweroff and the full guest check rerun to clean power-down.

An initial fast check was 29/39: several existing script imports lacked the repo
on PYTHONPATH, copied Lean cache lacked moved Core modules, and one existing script required root (the local-receiver OS boundary script skips unprivileged runs). cstack now supplies repo PYTHONPATH; necessary Lean prerequisites
were rebuilt. Existing generated result pages had two stale test-command listings
and were regenerated with build_results. The first final-head CI runtime assertions passed, but artifact upload failed with EACCES while traversing the private root-owned directory (run 38028612537). The workflow now independently checks the raw sink as root, packages a tar file as root, and uploads that readable file without weakening sink/database permissions.

The full ledger was regenerated with
Lean to retain its Lean section; no hand editing of generated files was used.

## Follow-up commands, CI and draft PR

- `python3 tools/test_deployment_slice.py`: PASS, 13 tests including the original hole reproductions, sensitive source variants and credential regex additions.
- `python3 tools/test_deployment_evidence.py`: PASS, three tests, including actual container sink tampering and daemon security-setting drift.
- Static matrix with `--lean`: PASS, 26 fixtures (one CONDITIONAL, 25 UNASSURED); final result in `deployment-evidence/followup-matrix-check.txt` and every exact bundle.
- `python3 tools/cstack.py check --fast --only deployment`: PASS, 4/4; final result in `deployment-evidence/followup-deployment-check.txt`; requires all four deployment steps.
- Generated registry, statement catalog, overview, results, ledger and trust-root `--check`: PASS. No generated content was hand-edited.
- Existing broader local fast result remains 40/41 historically: root-only native broker test plus host Landlock limitation, described above. This is not claimed as a new full-suite pass.
- CI at head: [live authoritative PR checks](https://github.com/jwcodes12/control-stack/pull/45/checks). Completion requires a final commit without `[skip ci]`, green required checks and a recorded head/check receipt in the PR description. The workflow now checks all expanded fixtures, the documented seeded subset differences and archived real-container bytes in addition to the native Linux boundary.
- Draft PR: https://github.com/jwcodes12/control-stack/pull/45. Keep draft; do not merge.

## Follow-up failures and corrections

The first seeded batch parser hit Lean's abbreviated list rendering; the checker
now prints every Boolean explicitly and checks all 200 values. An evidence check
first compared relative versus absolute provenance paths; portable source-path
normalization fixes that comparison while preserving every hash and selected fact.
The first cleanup audit expected a combined repository/tag string in Docker JSON;
it was corrected to inspect separate fields. Cleanup itself had already succeeded.

Stopping scope remains the handoff's A/B requirements plus the attempted C milestone;
all three real-container cases completed. Broader protocols/backends remain deferred
in `docs/DEPLOYMENT-SLICE-NEXT.md`.
