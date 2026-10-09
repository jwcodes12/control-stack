# SC-07 harness: egress allowlist + byte quota check

This is a defensive operational test of a data-loss-prevention style egress control. A trusted gateway caps how many
bytes a sandboxed job may send off-host, and to which destinations. The workloads are benign: a client that uploads
random bytes over plain TCP to an allowed sink, and a client that tries a sink that is not on the allowlist. No
evasion, tunnelling, covert channels or attacks on the gateway. Those, plus timing channels, DNS, other protocols and
side channels, belong to SC-01 / SC-02 / SC-04.

The preregistration is [`prereg/SC07-EGRESS-QUOTA.md`](../../../prereg/SC07-EGRESS-QUOTA.md)
(`PREREG-SC07-EGRESSQ-v1`). It holds the decision rules, the calibrated tolerances and the re-run policy.

## Topology

Each hypothesis × repetition builds a fresh topology and tears it down afterwards.

```
netns sc07-<tok>-<tag>-job      netns sc07-<tok>-<tag>-gw                 netns sc07-<tok>-<tag>-sink
sc07j 10.207.1.2  <== veth ==>  sc07gj 10.207.1.1
default via 10.207.1.1          sc07gs 10.207.2.1   <== veth ==>          sc07s 10.207.2.10 (allowed sink :8080)
                                nftables table inet sc07                        10.207.2.20 (not allowlisted :8080)
```

The gateway's forward chain has policy drop. It contains:
- an allowlist rule for job → 10.207.2.10 tcp/8080 and its return direction;
- the quota rule `quota name "job_q" counter name "quota_drop" drop`, with the object `quota job_q { over 8 MiB }`;
- named counters `fwd_up`, `fwd_down`, `quota_drop`, `deny_drop` and `halt_drop`.

HALT is one nft transaction: flush the forward chain, then add `counter name "halt_drop" drop`.

## Files

| file | role |
|---|---|
| `gw.py` | The trusted gateway and namespace controller (root). It creates the namespaces and the veths inside them, sets addresses and routes, and writes per-namespace sysctls, reading each back. It installs the ruleset, reads counters and quotas, and performs HALT. It starts processes in a namespace with `setns` followed by a drop to a numeric UID with `no_new_privs`. Teardown sends SIGTERM, then SIGKILL, kills any process still in a namespace, runs `ss -K` on leftover sockets, and finally `ip netns del`. Host-safety bounds are enforced here. |
| `sink.py` | The independent observer. It is a TCP server, running as UID 23801, that counts, hashes and timestamps every byte it receives (a CLOCK_MONOTONIC timeline). At EOF it replies with `OK <bytes> <sha256>`. It writes its state file atomically. |
| `job.py` | The benign client, running as UID 23802. `upload` sends random bytes (unpaced or paced), half-closes and waits for the ack; it gives up after a 1 s connect timeout or a 1 s send stall. `hold` waits on stdin, so its credentials can be inspected. |
| `run_sc07.py` | Runs H1–H6 and writes the receipt. |

## Run

Root is required. The runner uses the system Python 3.9 through sudo.

```
# dry run (debugging/calibration, not evidence); --only H1,H4 and --reps N are allowed
sudo -n /bin/python3 scenarios/SC-07/harness/run_sc07.py --kind dry --reps 5 --out /path/to/new-dir

# the single preregistered evidence run (needs committed, unmodified harness + prereg)
sudo -n /bin/python3 scenarios/SC-07/harness/run_sc07.py --kind evidence --reps 5 --out /path/to/new-dir

# recovery only: kill reserved-UID processes and delete stale sc07- namespaces
sudo -n /bin/python3 scenarios/SC-07/harness/run_sc07.py --kind dry --out /unused --cleanup-stale
```

The runner refuses an `--out` that already exists. An evidence run refuses, with an INFRA-ERROR receipt and no
hypothesis run, unless every harness file and the prereg are committed and unmodified. The receipt holds:
- `meta.json`: the commit, dirty status, file SHA-256s, kernel, Python, nft and iproute2 versions, the ruleset text,
  the HALT script, the constants, and read-only host-network snapshots before and after;
- `results.jsonl`: one line per hypothesis × repetition, with the checks as expected / observed / pass and the raw
  data (the read-back ruleset, counters, quotas, sink records and job results);
- `verdicts.json`;
- `cleanup.json`;
- `summary.md`, which includes the per-repetition H2/H4 measurements;
- `logs/`: process stderr.

The receipt is chowned to `SUDO_UID`. The exit status is 0 only for an overall PASS. A full run takes about 55 s (83 s observed at load average 6 before setup batching; 115 s wall limit).

## Host safety

This harness is built for a shared box:
- **Namespaces:** only namespaces named `sc07-<random run token>-…` are created. The run refuses to start if any
  `sc07-` namespace or host `sc07*` interface exists.
- **Interfaces:** both veth pairs are created inside our namespaces (`ip -n <ns> link add … peer … netns <ns>`). No
  device is ever created in, moved to, or bridged with the host namespace.
- **Addresses:** only 10.207.0.0/16.
- **nftables:** only inside the gateway namespace. Host nftables, host routes and host sysctls are never written.
  Sysctls are set only through `ip netns exec <our ns>` (net.* is per-namespace).
- **Host check:** the runner records host link names, route hashes, the stateless host nftables hash
  (`nft -s list ruleset`), the host sysctl values and the netns list, before and after. Unchanged sysctls and an
  unchanged netns list are required for an overall PASS. The rest is reported, since other services may change it.
- **UIDs:** processes in namespaces run as UIDs in 23800–23809 (no account creation, `no_new_privs`, no
  capabilities).
- **Cleanup:** cleanup runs in `finally` blocks. Leftover namespaces, interfaces or processes after any repetition
  abort the run, and a final sweep runs for the run token.
- **Limits:** a 115 s wall limit. Jobs exit by themselves after 10 s, sinks after 30 s.
- **Host side effects:**
  - `ip netns add` creates `/run/netns`, which is a bind mount, if it does not exist.
  - The first use of an nftables `quota` loads the `nft_quota` kernel module on demand (`nf_tables` is built in).
    Neither changes host networking.
- **Scratch files:** files are written only to a temporary `/var/tmp/sc07-run-*`, which is removed afterwards, and
  to `--out`.
