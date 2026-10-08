# SC-03 egress boundary: test-only vertical slice

The sandbox has a private PID/network namespace, loopback only, no IPv4 routes,
no capabilities, no new privileges, cleared environment, private `/tmp` and `/run`,
and read-only runtime/code mounts. Its one intentional host service is
`/run/egress.sock`. The host gateway chooses numeric loopback peers from a pinned
authority table. No DNS resolution, public endpoints or production sandbox
configuration changes occur in this fixture.

The 2026-10-08 follow-up fixes IPv6 connect-trace parsing and non-initial fragment
visibility; nine oracle regressions pass. A separate eight-flow outer-namespace
calibration is in `experimental/outer_accounting.py`, with commands, results and
limits in `../reviews/egress-follow-up-2026-10-08.md`. It captures every IP destination
in a loopback-only private namespace and attributes initial TCP/UDP packets to two
traced sender PIDs. It does not yet integrate the sandbox/gateway or discharge
general process attribution.

The claim is **immediate network peer reachability**, conditional on Linux and the
specified launch contract. It is not confidentiality, authenticated HTTP origin
identity, a kernel escape proof, or a guarantee about downstream forwarding by an
allowed service. Allowed CONNECT tunnels carry arbitrary bytes. The suite
explicitly demonstrates secret delivery and a TLS SNI different from the allowed
authority at the same permitted immediate peer.

## Run

Requirements: Linux, `/usr/bin/python3` (3.9+), bubblewrap, openssl, strace, working
user/PID/network namespaces; full observation additionally requires `CAP_NET_RAW`.
The controlled local test runs below use sudo for host observation. Sandbox
capabilities remain empty. Each run creates and cleans disposable loopback servers,
a gateway, test certificate and code snapshot; it never executes a production
agent or modifies an installed sandbox.

```sh
/usr/bin/python3 egress/test_oracle.py
/usr/bin/python3 egress/suite.py --gateway-only --output /tmp/egress-parser.json
sudo /usr/bin/python3 egress/suite.py --output /tmp/egress-full.json
sudo /usr/bin/python3 egress/suite.py --self-check-shared-net --output /tmp/egress-net-mutation.json
sudo /usr/bin/python3 egress/suite.py --self-check-packet-oracle --output /tmp/egress-packet-mutation.json
sudo /usr/bin/python3 egress/suite.py --self-check-direct-mirror --output /tmp/egress-mirror-mutation.json
egress/check_lean.sh
```

Exit 0 means the selected mode met its expectations; 1 is a failure; 2 means an
unavailable prerequisite. `--gateway-only` is explicitly `partial-pass`, never
isolation evidence. A missing namespace, packet observer, strace, dropped capture
packets or crashed attacker cannot silently become a successful denial. CI runs
full mode and all three mutations as mandatory steps and uploads artifacts on failure.
The private branch passed [remote egress CI](https://github.com/jwcodes12/control-stack/actions/runs/37784398180) on
2026-10-08 at `b30177e`: 62 full controls, all three mutations, nine oracle
regressions and six Lean theorem checks; zero packet drops. The outer-topology
calibration is checked from its stored receipt, not rerun by this workflow.

## Components and integration

`attacks.py --matrix` emits the checked-in `expected_outcomes.json`. Each case has
an id, attack family, expected class (`allow`, `deny`, `local`, `scope-limited`),
and optional raw proxy request. Run an attacker as `attacks.py CASE CONFIG_JSON`;
it emits a JSON report and a nonzero exit on unexpected Python errors. Reports are
untrusted diagnostic evidence. The host oracle decides reachability using packets,
destination observations, trusted policy bytes and independently traced connects.
OSError diagnostics are not enough to establish denial or usefulness.

`launcher.py CODE_DIR CONFIG_JSON SOCKET CASE` builds the fixed bubblewrap mount
contract. `sandbox_entry.py` validates that *same* actual namespace before starting
the untrusted TCP adapter on 127.0.0.1:3128. `validator.py` records namespaces,
interfaces, routes, capability/no-new-privilege state, descriptors and mounts,
checks a mountpoint allowlist and all namespace processes for inherited sockets, and rejects inherited sockets or extra descriptors.
The host policy file is absent inside. System runtime trees must be trusted and
contain no unexpected sockets, helper privilege, or submounts; arbitrary alternate
launchers are outside this evidence. Read-only mounts alone do not make sockets safe.

`suite.py` supplies a JSON config with socket/fixture addresses and ports, host
namespace ids, a public test CA, the wheel digest, host policy/gateway paths and a
synthetic secret. Metadata-shaped traffic targets 127.77.0.254:80; no real cloud
metadata endpoint is contacted. All attackers are bounded, including child/fork,
exec restart, SCM_RIGHTS, namespace join, raw sockets, host control/abstract sockets,
policy/code mutation, 32-request flood and 72 stalled-header clients.

`observer.py` uses host AF_PACKET on loopback and records IPv4 fixture traffic to
127.77.0.0/16 and all IPv6 loopback traffic, including failed SYNs,
UDP and ICMP. It checks packet-drop statistics; any loss invalidates absence
claims. Independent destination servers record accepted connections and bytes.
`strace` records every gateway IPv4 connect syscall with PID, timestamp and return
value, including failure; `tracing.py` requires a prior matching permit and a
pinned peer. Initial SYNs to the mirror must also match the gateway's recorded
local address/port and immediate peer; direct-to-mirror traffic without gateway
provenance is a failure. This is exhaustive for this bounded fixture, not process-attributed
capture of arbitrary host traffic. No outside network is needed. Runs share a fixture address prefix; a host-wide abstract-socket lock serializes
them so parallel CI/local invocations cannot contaminate observation windows.

Each case records its exit status, diagnostic report, packet/destination deltas
and gateway decisions. A successful honest mirror check runs after every case,
with its own observations, to catch outages that could otherwise mask bypasses.
The observer is calibrated against TCP/UDP/IPv6 and a refused TCP connect first.
A deliberate inherited live socket must cause startup rejection. Gateway death,
restart and invalid policy are separately checked. The packet mutation injects a
failed host SYN into the normal negative-case oracle and requires packet-based
failure; the namespace mutation tests validator rejection. The direct-mirror mutation
connects to the permitted peer from the host without a gateway attempt and must
be caught by source-port/SYN correlation.

## Exact proxy grammar

Only ASCII `GET`, `HEAD`, `POST`, `CONNECT`, exactly space-separated request lines,
HTTP/1.0 or HTTP/1.1 and CRLF framing are accepted. CONNECT requires a DNS-name and
canonical decimal port. Ordinary requests require absolute `http://` URIs; absent
port defaults to 80. Names are case-insensitive DNS labels, with no trailing dot,
userinfo, IP literals, percent escapes or backslashes. Fragments and noncanonical
ports are refused. The exact authority key must exist in the immutable table.

Headers are ASCII token names with no folding/control characters or duplicates.
Host, when supplied, must match the chosen authority. Transfer-Encoding, Upgrade,
Expect and Trailer are refused. Content-Length is decimal and at most 1 MiB; GET,
HEAD and CONNECT have no framed body. Request lines are limited to 8 KiB and all
headers to 32 KiB, with an absolute two-second header deadline and 64 active peers.
HTTP forwards exactly one framed request; subsequent pipeline bytes are discarded.
CONNECT passes arbitrary tunnel bytes to the pinned peer. The gateway never follows
redirects. A client following a redirect must obtain a new permission.

## Honest task and usefulness

The declared task is `sc03-fixture/1.0`: fetch its deterministic pure-Python wheel
from the mirror using the standard HTTP proxy adapter, verify the pinned SHA-256,
install it into private `/tmp`, compile it and run its tests. HTTP mirror fetch,
certificate-validated HTTPS CONNECT and local build/service activity must succeed.
The installer is deliberately small and restricted to the fixture wheel; apt/pip/npm,
public TLS trust, CDN redirect chains, caches and arbitrary internet tasks have not
been evaluated. See `USEFULNESS.md` and `FIDELITY.md` for scope and evidence.
