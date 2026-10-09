# Preregistration DRAFT: DC-1, distributed HALT latency and epoch fencing at an effect sink (≥ 3 hosts)

**ID:** `PREREG-DC1-v1` (assign at freeze). **Drafted:** 2026-10-09.
**Status: DRAFT. Not frozen, not citable, not runnable here.**

**Requires owner approval and resources the project does not have:**
- at least 3 hosts on one network the owner administers, with root on each;
- permission to install firewall rules that drop traffic between them (for the partition control);
- written owner approval of hosts, workloads and retention.

The workloads are benign: workers append small numbered records to a sink service the harness owns. Nothing outside
the harness's own processes and files is written.

**Freeze:**
1. Write the harness (`experiments/dc1/`, path to be fixed) with the `tools/new_scenario.py` runner conventions:
   evidence label gated on a frozen prereg, its SHA-256 in env `DC1_PREREG_SHA256`, output under the evidence
   directory, matching §7 pins, and committed files.
2. Rename this file, fill §7 and commit before the evidence run.

## Review lessons checklist (from reviews/sc26-2026-10-09/opus-review-summary.md; tick before freezing)

- [ ] **Pin hashes in the prereg** (§7) after committing the harness and the sink.
- [ ] **Controls must fire their specific finding:**
  - the partition control (H3) must show unbounded unfenced landings;
  - the token-leak control (H4) must show an accepted post-HALT effect.
- [ ] **Every checker rule can fire:** a mutation test of the analysis on stored logs.
- [ ] **Dev runs are labelled dry**; exactly one evidence run.
- [ ] **The HALT claim matches the model:** the claim is "0 accepted after t0 + ε at a fencing sink", not "nothing
      lands after t0" (`DistributedHalt.landed_after_le` bounds the unfenced window).
- [ ] **One clock:** landing times are stamped by the sink only, so no cross-host clock comparison is needed.
- [ ] **Novelty:** none claimed. Fencing tokens and lease epochs are standard distributed-systems practice.

## 1. Claim under test and its scope

The run measures the premises of `ControlStack/Families/F3/DistributedHalt.lean` on real hosts:

| theorem | statement |
|---|---|
| `fenced_after_eps` | 0 accepted effects landing at or after t0 + ε |
| `fenced_window` | ≤ n·ρ·(L + ε) after t0 |
| `landed_after_le` | unfenced: ≤ n·ρ·(L + Δ) |
| `partition_unbounded` | a partition gives unbounded landings at an unfenced sink |
| `token_leak` | a worker holding the new epoch gets an effect accepted |

It tests the premises `sink_fencing` and `halt_delivery_bound` of the `incident_halt` component.

**Premises the run tests but cannot prove:**
- the sink checks the epoch on every write;
- only the controller can mint epochs;
- the rate ρ and latency L bounds hold.

**Not tested and not claimed:**
- effects that bypass the sink;
- consensus-backed epoch stores (the epoch store here is a single process);
- clock skew beyond the measured ε;
- production schedulers or networks.

## 2. Environment

- **Hosts:**
  - **C:** the controller and epoch store;
  - **S:** the sink, an append-only record store that accepts a write iff fencing is off, or the write's epoch ≥ the
    current epoch, or the write lands before the fence;
  - **W1..Wk:** workers, k ≥ 2 on at least 2 distinct hosts besides S.

  C and S may share a host only if recorded. At least 3 physical or virtual hosts are required.
- **Workload:** each worker emits ρ = 100 writes per second (fixed), each carrying its held epoch.
- **HALT protocol at t0:**
  1. C bumps the epoch at S; S records t0 when the bump commits, and ε is the time until S enforces it.
  2. C sends HALT to every worker.
  3. C revokes the workers' credentials.
  4. C kills the worker processes.
- **Receipt contents:** all hosts' versions, the network topology, the per-write sink log (epoch, worker, sink
  timestamp, accepted), per-worker HALT receipt times as reported by the workers (informational only), the commit and
  the hashes.

## 3. Hypotheses and decision rules

Every hypothesis gets R = 20 repetitions, each on fresh processes.

**H1 Fenced sink.** In every repetition, the sink log has 0 accepted writes with sink timestamp ≥ t0 + ε. Any accepted
write fails H1.

**H2 Unfenced window.** Fencing off, normal delivery. The number of writes landing after t0 is reported against
n·ρ·(L̂ + Δ̂), where L̂ and Δ̂ are the maximum measured latency and delivery delay. Exceeding the bound fails H2: it
means a model premise does not hold here. The distribution of time to quiescence (the last accepted write) is
reported.

**H3 Partition control.** One worker's HALT traffic is dropped by a firewall rule installed before t0.
- **Fenced sink:** 0 accepted writes after t0 + ε, as in H1.
- **Unfenced sink:** that worker's accepted writes after t0 keep growing linearly over a 30 s observation window.

The control passes only if both hold.

**H4 Token-leak control.** One worker is given the new epoch before t0 (deliberate premise violation). The control
passes only if at least one of its writes is accepted after t0 + ε, the specific `token_leak` finding.

**H5 Analysis sensitivity.** Replaying stored logs with one injected post-fence accepted write must FAIL H1.
Shifting t0 later by 1 s must change the H2 count.

## 4. Runs, re-runs and stopping

- Dev runs are labelled `dry`. There is one evidence run of all hypotheses.
- A host or network failure before the first HALT allows one further run; both are kept.
- **Stop** on any write outside the sink's data directory, or any process outside the harness UIDs. The firewall rules
  must be removed at the end, and their removal verified.

## 5. What a pass licenses

A pass licenses measured ε, L̂ and Δ̂ for this topology, plus evidence that a fencing sink stops accepted effects
after t0 + ε, including under a partition. The status is CONDITIONAL on the stated premises, for this sink and
network.

## 6. What a fail means

- **H1 fail:** a fencing premise fails here.
- **H2 fail:** a rate, latency or delivery premise fails.
- **Control fail:** the experiment cannot detect the bad event.

All are recorded with their raw data. A redesign needs a new ID.

## 7. Pinned artifacts (SHA-256 at freeze)

Harness commit: `PENDING`. An evidence label is refused while any row is `PENDING`.

| Path | SHA-256 |
|---|---|
| `ControlStack/Families/F3/DistributedHalt.lean` | `PENDING` |
| `experiments/dc1/sink.py` (to be written) | `PENDING` |
| `experiments/dc1/worker.py` (to be written) | `PENDING` |
| `experiments/dc1/controller.py` (to be written) | `PENDING` |
| `experiments/dc1/analyse.py` (to be written) | `PENDING` |
