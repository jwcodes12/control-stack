# Preregistration: SC-07 egress allowlist + byte quota, single-host namespace reference run (v1)

**ID:** `PREREG-SC07-EGRESSQ-v1`. **Written:** 2026-10-09, before any dry run or evidence run. The four tolerances in
§3.1 were marked provisional in that first version and were fixed from dry-run measurements (§3.1, "Calibration")
before any evidence run. No evidence run had been made when they were fixed.
**Freeze:** this file's Git commit and SHA-256 are recorded in every receipt. After the evidence run starts, this file
is not edited. A change needs a new ID (`-v2`), a new file and a new run. The earlier run is kept.

## 1. Claim under test and its scope

SC-07: a job exfiltrates model weights or a large dataset. The candidate mitigation tested here is narrow and
operational, a data-loss-prevention style egress control:

- the job runs in its own network namespace whose **only** interface is one veth to a trusted gateway namespace, with
  its default route via the gateway;
- the gateway forwards only to **allowlisted** destination addresses and ports (forward chain, policy drop);
- the gateway caps the bytes it forwards from the job to the allowlisted destination with an nftables **quota**
  object (`quota job_q { over QUOTA bytes }`; the rule `quota name "job_q" ... drop` drops every upload packet once
  the quota is consumed);
- an admin **HALT** flushes the gateway's forward chain to drop-all in one nftables transaction;
- two **independent** byte counts: the gateway's named nftables counters, and each sink's own count of received
  bytes (a separate process, in a separate namespace, under a separate UID).

The run asks whether this mechanism enforces the allowlist and the byte cap and stops an upload on HALT for
**benign** workloads: a client that uploads random bytes over plain TCP to the allowed sink, and a client that
connects to a sink that is not on the allowlist.

**Implementation:** `scenarios/SC-07/harness/`:
- `gw.py`: the trusted gateway and namespace controller (namespaces, veths, nftables ruleset, quota, HALT, teardown);
- `sink.py`: the sinks (TCP servers that count, hash and timestamp received bytes);
- `job.py`: the benign job client;
- `run_sc07.py`: the checks and the receipt.

**Not tested here, and not claimed:**
- **Adversarial workloads.** No workload evades, tunnels, fragments, retries via other paths, spoofs addresses, uses
  other protocols, or attacks the gateway. Covert channels, timing channels, DNS, other protocols (UDP, ICMP, IPv6)
  as exfiltration carriers and side channels are SC-01 / SC-02 / SC-04 territory and out of scope. (IPv6 is disabled
  in every namespace, and the forward chain is `inet` family with policy drop; H5 only records the absence of IPv6
  addresses as configuration.)
- **Content.** The quota bounds bytes to the allowlisted destination. It says nothing about which bytes; an allowed
  destination receives up to the quota of arbitrary data.
- **Other hosts or deployments.** Generalisation to other kernels, nftables versions, real NICs, or multi-host
  gateways.
- **Trust in root.** Compromise of root, the kernel, nftables or the gateway namespace. These are trusted.
- **Several jobs / shared quota.** One job, one quota object. Cumulative quota across jobs, quota reset policy and
  persistence across gateway restarts are not tested.
- **Gateway-side HALT latency guarantees beyond this host.** HALT latency is measured, not bounded in general.

## 2. Environment and trust

- **Host:** the OCI ARM64 Linux box running this repository (single host, shared with other services).
- **Tools:** iproute2 (`ip`, `ss`), `nft` (nftables), `sysctl`, the system Python 3.9 via sudo.
- **Trusted:** the Linux kernel (network namespaces, veth, nf_tables, nft_quota), root, the gateway code and runner at
  the recorded hashes, and CPython.
- **Untrusted:** nothing in the adversarial sense; the workloads are benign by construction (§1).
- **Separate numeric UIDs:** sinks 23801, job 23802, the H1 gateway liveness probe 23803. The range 23800–23809 is
  reserved: `gw.py` refuses any other UID, and the run aborts before any test if any process already runs under one
  of them. No accounts are created. Each process enters its namespace with `setns(CLONE_NEWNET)` while still root,
  then sets `no_new_privs`, `setgroups([])`, `setgid`, `setuid`, then execs.
- **Receipt contents:** the Git commit and dirty status; the SHA-256 of every harness file and of this file; kernel,
  Python, nft and iproute2 versions; load average at start and end; the exact ruleset installed and read back for
  every repetition; the HALT script; every counter, quota and sink record; expected vs observed for every check; and
  a read-only host-network snapshot taken before and after the run (§2.1).

### 2.1 Host-safety bounds (enforced in `gw.py` / `run_sc07.py`, part of this registration)

- **Namespaces:** only network namespaces the runner creates, each named `sc07-<run token>-<hyp><rep>-{job,gw,sink}`.
  Three fresh namespaces per hypothesis × repetition.
- **Interfaces:** two veth pairs, both created **inside** our namespaces (`ip -n <job> link add sc07j type veth peer
  name sc07gj netns <gw>` and likewise gw↔sink). No device is created in, moved to, or attached to the host
  namespace. No bridge.
- **Addresses:** only 10.207.0.0/16 (job 10.207.1.2, gateway 10.207.1.1 / 10.207.2.1, sinks 10.207.2.10 and
  10.207.2.20).
- **nftables:** one table `inet sc07`, only inside the gateway namespace. The host ruleset is never written.
- **sysctls:** written only via `ip netns exec <our ns> sysctl` (net.* is per-namespace): `ip_forward` (1 in the
  gateway, 0 elsewhere) and `disable_ipv6` (1 everywhere). Read back after writing.
- **Host routes, host nftables, host sysctls:** never written. The runner records the host's link names, route-table
  hashes (IPv4, IPv6), nftables ruleset hash, the host values of the sysctls above, and the named-namespace list
  before and after the run.
- **Cleanup always runs**, in `finally` blocks, per topology: SIGTERM then SIGKILL our processes; SIGKILL any process
  still in our namespace; abort leftover non-TIME-WAIT TCP sockets in our namespace (`ss -K`); `ip netns del`. After
  every hypothesis × repetition the runner checks that no `sc07-` namespace, no host `sc07*` interface and no
  reserved-UID process is left; any residue aborts the run. A final sweep repeats this for the run token.
- **Wall limit:** 115 s per run (SIGALRM). Job processes exit by themselves after 10 s, sinks after 30 s.

## 3. Hypotheses and decision rules

### 3.1 Constants and tolerances

| name | value | meaning |
|---|---|---|
| `QUOTA` | 8 MiB = 8 388 608 B | nft quota `over` threshold. Counted by the kernel as IP packet length (headers included) of every job→allowed-sink upload packet that reaches the quota rule. |
| `H2_BYTES`, `H6_BYTES` | 3 × QUOTA = 25 165 824 B | unpaced upload |
| `H3_BYTES` | 0.5 × QUOTA = 4 194 304 B | unpaced upload |
| `H4_BYTES` / `H4_RATE` / `H4_HALT_AT` | 6 MiB / 4 MiB/s / 1 MiB | paced upload, below the quota; HALT once the sink has ≥ 1 MiB |
| `SMALL_BYTES` | 64 KiB | positive-control upload (H1, H5) |
| `PROBE_BYTES` | 16 B | H1 liveness probe from the gateway namespace to the non-allowlisted sink |
| `CONNECT_TIMEOUT` / `STALL_TIMEOUT` / `ACK_TIMEOUT` | 1.0 s / 1.0 s / 3.0 s | job client timeouts |
| `TOL_QUOTA` | **1 500 B** (one MTU; fixed by calibration) | H2 upper slack: sink bytes ≤ QUOTA + TOL_QUOTA |
| `TOL_LOW` | **128 KiB** = 131 072 B (fixed by calibration) | H2 lower slack: sink bytes ≥ QUOTA − TOL_LOW (the quota, not something else, stopped the upload) |
| `TOL_AGREE` | **64 KiB** = 65 536 B (fixed by calibration) | H2: \|gateway `fwd_up` bytes − sink bytes\| ≤ TOL_AGREE |
| `TOL_HALT` | **128 KiB** = 131 072 B (fixed by calibration) | H4: sink bytes received after HALT took effect ≤ TOL_HALT |

**Calibration (dry runs, before any evidence run).** The first version of this file gave provisional values
(TOL_QUOTA 64 KiB, TOL_LOW 256 KiB, TOL_AGREE 64 KiB, TOL_HALT 64 KiB). They were replaced by the values in the
table above after three full 5-repetition dry runs (`--kind dry`, scratch receipts `sc07-dry1..3`, 2026-10-09,
05:22–05:27 UTC, same host and kernel `6.12.0-206.104.3.3.el9uek.aarch64`, nftables v1.0.9). The rest of
this file, the constants and the checks were unchanged by calibration. One harness bug found in `sc07-dry1` was fixed
before `sc07-dry2`: the H6 check matched the substring "quota" in the counter name `quota_drop`, and it now inspects
the JSON ruleset for quota objects and statements. A matching positive check was added to H2.
Measurements over the 15 H2 and 15 H4 repetitions:

| quantity | min | max | mechanism bound | fixed tolerance |
|---|---|---|---|---|
| H2 sink count − QUOTA | −70 800 B | −8 848 B | < 0: the crossing packet is itself dropped (`consumed ≥ quota` after adding it), so `fwd_up` < QUOTA, and the sink's payload is < `fwd_up` (headers) | TOL_QUOTA = 1 500 B: one MTU of margin over the bound |
| H2 `fwd_up` − QUOTA | −62 316 B | −244 B | < 0 (as above) | (recorded, not a decision) |
| H2 `fwd_up` − sink count | 8 068 B | 10 148 B | = 52 B (20 IP + 32 TCP with timestamps) × forwarded upload packets (161–192), plus retransmissions | TOL_AGREE = 64 KiB: about 6× the measured max. It allows ≈ 1 260 forwarded packets (mean ≥ 6.6 KB per GSO packet) |
| H2 QUOTA − sink count | 8 848 B | 70 800 B | ≤ one dropped GSO packet (≤ 64 KiB + headers) plus the header overhead above (≈ 76 KB) | TOL_LOW = 128 KiB |
| H4 bytes after HALT `t_end` | 0 B | 0 B | data already forwarded but not yet read by the sink at `t_end`: at most about one 64 KiB job send chunk at 4 MiB/s | TOL_HALT = 128 KiB = two job send chunks |
| H4 bytes after HALT `t_start` | 0 B | 131 072 B | chunks arriving during the 18–54 ms `nft` call | (recorded, not a decision) |
| HALT latency (`nft -f` via `ip netns exec`) | 18 ms | 54 ms | — | (recorded, not a decision) |

All checks of H1–H6 passed in `sc07-dry2` and `sc07-dry3` with the provisional values. The fixed values are
**tighter** for TOL_QUOTA and TOL_LOW, and **looser** for TOL_HALT, which is a deliberate allowance for scheduling
noise on the shared host. They are the values the evidence run uses (`run_sc07.py` constants, recorded in every
receipt's `meta.json`).

**Confirmation after fixing (still dry, not evidence).** `sc07-dry4` used the fixed values: 30/30 repetitions
passed, wall time 83.5 s at load average 3–6. That wall time is close to the 115 s limit on this 2-CPU shared host.
So, before any evidence run, `gw.py` was changed to batch its setup and teardown commands:
- `ip -batch`;
- one `sysctl` process per namespace, with read-back kept;
- `ss -N`;
- a single /proc scan instead of `ip netns pids`.

The change does not touch the topology, the ruleset, the workloads or any check. `sc07-dry5`, run on the final
harness, passed 30/30 in 55.0 s at load average ≈ 4. Its H2/H4 measurements lie inside the calibration ranges above:
- sink − QUOTA from −66 776 to −15 400 B;
- `fwd_up` − sink from 9 264 to 9 732 B;
- 0 B after HALT `t_end`.

### 3.2 Definitions

- **Sink count:** the bytes a sink process read from accepted connections whose peer address is the job (10.207.1.2),
  from the sink's own state file. Each connection also records its SHA-256 and a timeline of (CLOCK_MONOTONIC time,
  cumulative bytes) at every `recv`.
- **Gateway counters:** named nftables counters in the gateway's table: `fwd_up` (accepted job→allowed-sink upload
  packets; IP lengths), `fwd_down`, `quota_drop` (upload packets dropped by the quota), `deny_drop` (everything not
  allowlisted), `halt_drop` (everything after HALT).
- **Completed upload:** the job received the sink's reply `OK <bytes> <sha256>` and it equals the job's own length
  and SHA-256 of the data it generated.
- **Failed connection:** `connect()` from the job did not succeed within `CONNECT_TIMEOUT` (the gateway drops; there
  is no reject).
- **HALT took effect:** the time `nft -f` returned for the HALT transaction (`t_end`). `t_start` (just before the
  call) is also recorded, and bytes after `t_start` are reported but not used in a decision.

**Pass rule:** each hypothesis runs **5 repetitions**, each on a freshly built topology (three new namespaces,
fresh ruleset, fresh quota, fresh sinks). A hypothesis passes only if every check passes in all 5 repetitions. An
exception inside a repetition fails it.

### 3.3 Hypotheses

**H1 Allowlist.** The job uploads 0.5 × QUOTA to the non-allowlisted sink 10.207.2.20:8080.
- the job's connection fails;
- the non-allowlisted sink records 0 bytes and 0 connections from the job (independent sink count);
- the gateway's `deny_drop` counter is ≥ 1 packet and `fwd_up` is 0 packets after the attempt;
- **liveness (not vacuous):** a 16-byte probe from the gateway namespace (UID 23803) to 10.207.2.20:8080 completes
  and that sink records exactly 16 bytes from 10.207.2.1;
- **positive control:** a 64 KiB upload from the job to the allowed sink in the same topology completes.

**H2 Quota.** The job uploads 3 × QUOTA, unpaced, to the allowed sink.
- the upload does not complete;
- allowed-sink count ≤ QUOTA + TOL_QUOTA;
- allowed-sink count ≥ QUOTA − TOL_LOW;
- \|`fwd_up` bytes − allowed-sink count\| ≤ TOL_AGREE;
- `quota_drop` ≥ 1 packet (the quota was binding);
- the non-allowlisted sink records 0 bytes from the job.

**H3 Under-quota usefulness.** The job uploads 0.5 × QUOTA, unpaced, to the allowed sink.
- the upload completes (ack equal to length and SHA-256);
- the sink records exactly one connection from the job, with byte count = 4 194 304 and SHA-256 equal to the job's;
- that connection ended by EOF and the sink sent its ack;
- `quota_drop` = 0 packets.

**H4 HALT.** The job uploads 6 MiB paced at 4 MiB/s (below the quota). When the allowed sink's count reaches
≥ 1 MiB, the runner issues HALT.
- **precondition:** at HALT, the job is still running and the sink's count is in [1 MiB, 6 MiB);
- bytes the sink received after HALT took effect (`t_end`, from the sink's timeline) ≤ TOL_HALT;
- the upload does not complete, and the sink's total < 6 MiB;
- `fwd_up` is unchanged between right after HALT and the end;
- `halt_drop` ≥ 1 packet (the job kept sending and was dropped);
- a new 64 KiB upload from the job after HALT fails to connect, and the sink records no connection from the job other
  than the first;
- the gateway's forward chain after HALT has policy drop and exactly one rule (the `halt_drop` drop).

**H5 No bypass route (configuration check, not an attack).**
- the job namespace's interfaces are exactly `lo` and `sc07j`;
- `sc07j` is a veth whose peer (`link_index`, `link_netnsid`) is the gateway's `sc07gj` in another namespace;
- every non-local route in every table uses `sc07j`, and any gateway in them is 10.207.1.1;
- exactly one default route, via 10.207.1.1 dev `sc07j`;
- local-table routes are only on `lo` / `sc07j`; policy rules are the defaults (priorities 0, 32766, 32767);
- no IPv6 address in the job namespace;
- `ip route get` for 10.207.2.10 and 10.207.2.20 returns via 10.207.1.1 dev `sc07j`;
- a job process (`job.py hold`) is in the job namespace (`/proc/<pid>/ns/net` inode), has real/effective/saved/fs
  UID 23802, `CapEff` = `CapPrm` = `CapAmb` = 0 and `NoNewPrivs` = 1, i.e. it cannot alter its own namespace's
  interfaces or routes;
- **behavioural cross-check:** a 64 KiB upload from the job completes, the sink records 64 KiB from the job, and the
  gateway's `fwd_up` bytes ≥ the sink's count (every byte crossed the gateway's counted rule).

**H6 Negative control: the quota is what limits H2.** The gateway's ruleset is built **without** the quota object and
quota rule (allowlist otherwise identical). `gw.py` refuses to build this ruleset unless `SC07_NEGATIVE_CONTROL=1`;
the runner sets it only around H6's ruleset construction and records it in each H6 result. The job uploads
3 × QUOTA, unpaced.
- the control flag is recorded, and the installed ruleset contains no quota object and no quota rule;
- the upload completes;
- the sink records exactly one connection with 25 165 824 bytes and the job's SHA-256;
- the sink count > QUOTA + TOL_QUOTA.

**Overall pass:** H1–H6 all pass, the run is not aborted, the final cleanup leaves no `sc07-` namespace, no host
`sc07*` interface and no reserved-UID process, and the host's sysctl values (§2.1) and named-namespace list are
unchanged between the before/after snapshots. The host route-table hashes, link-name list and host nftables hash are
recorded and reported but are **not** pass conditions, because other services on this shared host may change them
legitimately during a run.

## 4. Runs, re-runs and stopping

- **Dry runs:** use `--kind dry`, go to scratch directories, and are for debugging and for the calibration in §3.1.
  They are not evidence.
- **The evidence run** is exactly one invocation of:
  ```
  sudo -n /bin/python3 scenarios/SC-07/harness/run_sc07.py --kind evidence --reps 5 --out <new dir>
  ```
  - It runs from a commit in which this file and every harness file are committed and unmodified. The runner refuses
    otherwise (it also refuses an existing `--out`, any `--only` subset, and `--reps` ≠ 5).
  - It runs all six hypotheses. The receipt directory is kept, whatever the outcome.
- **Infrastructure errors:** a re-run is allowed only for an infrastructure error, defined as a preflight failure
  before any hypothesis starts: not root; a missing tool; a stale `sc07-` namespace or host `sc07*` interface; a
  reserved-UID process already running; `SC07_NEGATIVE_CONTROL` set at start; a dirty tree. At most one re-run, and
  both receipts are kept.
- **Failures are final:** a hypothesis failure, including one caused by load on the shared host, is recorded as
  FAILED in the scenario manifest. It is never re-run under this ID. A re-run with changed bounds needs `-v2`.
- **Stop:** the runner aborts the whole run, with cleanup, if any `sc07-` namespace, host `sc07*` interface or
  reserved-UID process survives a hypothesis × repetition, or if the 115 s wall limit is reached.

## 5. What a pass licenses

A pass licenses only this statement. On this host and kernel, for benign single-connection TCP uploads from a job
whose only network path is a veth to a trusted gateway namespace:
- an nftables forward-chain allowlist (policy drop) delivers no bytes to a non-allowlisted destination;
- an nftables `quota over` object caps the bytes delivered to the allowlisted destination at the quota plus the
  calibrated tolerance, and the gateway's counter agrees with the receiver's own count within tolerance;
- an under-quota upload is delivered byte-exact;
- a HALT that flushes the forward chain stops an in-progress upload within the calibrated tolerance and blocks new
  connections;
- the job namespace has no route except via the gateway (configuration);
- without the quota rule, the same upload is delivered in full (the quota is what limits it).

It is an operational premise for the SC-07 "artifact quotas and egress denial" assumption. It is not evidence about
adversarial workloads, covert or timing channels, other protocols, or content, and it does not move SC-07 out of
DRAFT on its own. Independent review remains open.
