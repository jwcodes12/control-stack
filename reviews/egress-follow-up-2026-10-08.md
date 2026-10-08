# SC-03 local follow-up, 2026-10-08

The authorized follow-up completed locally after the scheduled 09:30:31 UTC window.
Two concrete observer bugs were fixed. The existing fixture remains CONDITIONAL;
a separate bounded experiment establishes feasibility of outer-topology accounting.
No production sandbox, publication, repository transmission, public service contact,
or auditgate change occurred. No model requests or rate-limit errors occurred, so
no account reset time is inferred from the scheduled five-hour interval.

Read `global agent instructions`, HANDOFF.md, SESSION.md, egress/README.md,
egress/FIDELITY.md, reviews/dialogue/sol-11.md, ROADMAP.md and the prior review
dispositions first. No nearer AGENTS.md/CLAUDE.md/GEMINI.md was found. This checkout
has no configured Git remote, so the conditional GitHub issue check did not apply.
The existing Astra/Opus findings were assessed from local records; no new external
review was requested. Initial untracked `egress/dest_server.py` and four TMCERT
review error/metadata files were left unchanged. The unused destination prototype
is not the suite's active destination oracle (which is `suite.Endpoint`).

The initial `python3 egress/check_evidence.py` verified all old receipt hashes, and
`python3 egress/test_oracle.py` passed seven regressions. The latest committed
changes were SC-03 implementation and review-whitespace normalization.

## Concrete fixes

- `tracing.connects` previously found AF_INET6 lines through a substring match,
  then used IPv4-only address/port patterns and rejected them rather than producing
  a connect record. It now records IPv6 attempts and checks them against the same
  pinned-peer/prior-permission oracle; malformed IPv6 lines fail closed. The
  original fixture used IPv4 gateway peers, so this was a coverage/correctness gap,
  not evidence of a bypass in its stored passing run.
- `observer.decode_packet` previously continued extension-header parsing after a
  non-initial IPv6 fragment. Arbitrary continuation payload could make it return
  None and lose address-level evidence. It now stops parsing at that fragment,
  preserving addresses and marking ports unavailable. A short adversarial
  continuation payload reproduces the old omission.

Two targeted regressions were added. Gateway/parser policy and the Lean model were
not changed. Original fixture receipts were rerun against the corrected sources;
manifest and summary hashes/statistics were refreshed, without promoting assumptions.

## Commands and real results

Commands ran from `<research-root>/control-stack`. Fixtures sharing the host
prefix ran under the existing serialization lock. In mutation mode `tcp4: fail`
is the intended observed violation; the command exits zero only on detection.

| Command | Result |
|---|---|
| `/usr/bin/python3 egress/test_oracle.py` | 9 tests, OK, exit 0 |
| `sudo -n /usr/bin/python3 egress/suite.py --output egress/results/local-full.json` | pass, 62/62 controls; 1,454 packet records counted by kernel statistics, zero drops; 69 mirror SYNs, zero orphans; 69 independently traced gateway connects; exit 0 |
| `sudo -n /usr/bin/python3 egress/suite.py --self-check-shared-net --output egress/results/local-namespace-mutation.json` | mutation-detected, zero drops, exit 0 |
| `sudo -n /usr/bin/python3 egress/suite.py --self-check-packet-oracle --output egress/results/local-packet-mutation.json` | mutation-detected, zero drops, exit 0 |
| `sudo -n /usr/bin/python3 egress/suite.py --self-check-direct-mirror --output egress/results/local-mirror-mutation.json` | mutation-detected, zero drops, exit 0 |
| `sudo -n /usr/bin/python3 egress/suite.py --gateway-only --output egress/results/local-parser.json` | partial-pass, 34 controls, exit 0 |
| `/usr/bin/python3 egress/suite.py --output egress/results/local-unprivileged.json` outside managed network restrictions, ordinary user | blocked: `[Errno 1] Operation not permitted`; exit 2; no isolation pass inferred |
| `egress/check_lean.sh` | six theorem checks pass; only propext/Quot.sound, exit 0 |
| `/usr/bin/python3 egress/check_evidence.py` | source/evidence hashes and original controls/mutations plus isolated eight-flow calibration pass; CONDITIONAL, exit 0 |
| `git diff --check` | clean, exit 0 |

The managed sandbox's ordinary-user full-mode attempt was separately blocked by
`bwrap: loopback: Failed to create NETLINK_ROUTE socket: Operation not permitted`
(exit 2, `/tmp/egress-followup-managed-blocked.json`). Its initial parser-only
attempt was blocked by EPERM on the fixture socket (exit 2); the final parser
receipt is the successful privileged rerun. Default sudo was also blocked by the
managed no-new-privileges flag. Approved local escalated execution succeeded; no
automatic approval rejection occurred. The full project build was not repeated:
no Lean/module changes were made, and the relevant standalone theorem check passed.

## Bounded outer topology experiment

Feasibility probe:

```sh
sudo -n unshare --net /bin/sh -c 'ip link set lo up; ip -brief link; ip route show; ip -6 route show'
```

Exit 0: only lo, no external/default routes. Then:

```sh
sudo -n unshare --net /usr/bin/python3 egress/experimental/outer_accounting.py \
  --host-netns "$(stat -Lc %i /proc/self/ns/net)" \
  --output egress/results/local-outer-accounting.json
```

Exit 0, status pass, including a rerun after adding per-child topology guards.
The outer namespace has only lo. Documentation addresses 192.0.2.1,
198.51.100.2, 2001:db8::1 and 2001:db8::2 are assigned to lo; they never route
outside. There are no target listeners. Two traced child senders each attempt
refused TCP connects and UDP datagrams using explicit bound source tuples.
All IP frames are captured without destination filtering: 16 decoded outgoing
frames (including replies), 32 kernel-counted frames, zero drops. Eight initial
TCP SYN/UDP packets map to eight independently traced bind/connect/sendto flows
from exactly two sender PIDs. Removing one traced flow causes provenance failure.
The receipt preserves full per-PID traces, packets, namespaces, routes and hashes.
Direct invocation of `--sender 0` without a validated topology exits 1 with
`private outer namespace required`, before socket traffic.

This experiment is isolated under `egress/experimental/`, not installed in a
production launch path and not substituted for the existing fixture oracle.
Its packet collector has no destination filter, but the finite sender inventory
is still a calibration: not an all-syscall/all-adversary attribution guarantee.
Initial transmissions are attributed through independently traced explicit binds;
ICMP/TCP replies are recorded without PID attribution. Raw sockets, inherited
FDs, connected UDP, sendmsg, io_uring, async trace interleaving and arbitrary
attacker processes are untested. Traced programs are trusted calibration code.
The manifest's all_destination_attribution assumption remains UNRESOLVED.

## Remaining next step

Integrate the existing gateway and disposable sandbox launch into an isolated
outer namespace, separate trusted gateway and attacker process trees, and account
for every observed initial transmission across those trees. Include direct-to-peer,
failed-connect and missing-trace mutations plus inherited-FD and alternate-send
controls before widening any reachability claim. Keep an outer topology with no
external links; veth/routing complexity is unnecessary for this first integration.
Remote CI and publication still require separate authorization. Stop here for
this bounded follow-up; auditgate remains outside scope.
