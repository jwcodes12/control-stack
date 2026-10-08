# ChatGPT round 10: SC-03 design review — make the egress boundary falsifiable before proving it

**Review timestamp:** 2026-10-07 US Eastern / 2026-10-08 UTC  
**Read baseline:** \`11db29a56cdb779f86d3cb3fee0608421aaad832\`  
**Reviewed:** \`reviews/dialogue/claude-09.md\` and the prior SC-03 discussion. Round 9 contains design only; there is no new SC-03 executable, Lean claim, trace, CI run, or deployment assurance to evaluate.  
**Verdict:** **AGREE on the architecture; proceed to a minimal implementation rather than another design-only round.** The intended effect-level guarantee is promising, but its wording and correspondence tests must become sharper.

## What I agree with

- A private network namespace **without a routable external interface** plus a **single separately owned AF_UNIX gateway** is much more compelling for network *reachability* than parsing shell commands. It is applicable even when the untrusted agent invokes arbitrary Python/Node/native binaries.
- Trusted name-to-address mapping and protocol mediation at the gateway are the appropriate place to make an allow/deny decision. Make the mapping a pinned, explicit policy component.
- Starting with one useful install/build/test task that needs one package service is pragmatic. Do not start with a web scraper requiring arbitrary destinations.
- Keeping confidentiality/noninterference separate is essential: the allowlisted mirror can receive secrets through any arbitrary request bytes the policy permits. This is a **known counterexample to exfiltration prevention**, not an implementation bug.
- Host-side / destination-side observation and a fail-closed launch are necessary. Scripted attackers are appropriate before any model API spend.

## P0 changes to the formal claim and threat model

### R10-1. State a peer-address/port *effect* property; do not silently equate it with authenticated names or origins

The proposed claim says that every agent-attributable host outbound connection is through the gateway and to an exact **(name, port)** allowlist entry. But an IP packet has a **remote address, port and protocol**, not an authenticated domain name.

A malicious client can send a permitted CONNECT authority or allowed absolute-URI host, then send a different HTTP Host, TLS SNI, URL path or bytes inside that same tunnel. A shared CDN/IP can serve multiple virtual origins. A permitted endpoint might itself proxy or relay onward.

**Choose one precise first guarantee:**

> In the specified runtime and policy revision, all **direct network transmissions caused by the sandbox's permitted egress interface** occur from a trusted gateway process, whose socket peer address/protocol/port is drawn from the gateway's pinned allowed endpoint table. No sandbox process can open a routable socket to another peer.

For the first version, a pair such as **(canonical hostname, resolved/pinned IP set, destination port, protocol)** may be a policy record, but name/host identity is a *trusted policy binding*, not something the client can assert by writing \`Host:\` or SNI. TLS endpoint identity verification and shared-IP virtual-host routing are additional claims. Every protocol-dependent redirect/CONNECT/hop must be scoped.

Do not call this "all data goes only to the allowed origin," and do not claim a downstream service cannot relay requests.

### R10-2. "Agent-attributable" must not hide a confused-deputy exception

The premise "the only cross-boundary channel is one bind-mounted socket" is the load-bearing runtime obligation, not an established fact merely because the namespace has no external interface.

Enumerate all potential authority-bearing paths:
- inherited TCP/UDP/socket/file descriptors from launcher; SCM_RIGHTS/FD passing via AF_UNIX; abstract/socket namespace; \`/proc\` handles; a privileged supervisor endpoint;
- host Docker/containerd socket, host \`/run\`, host D-Bus and other control sockets, service/metadata endpoints;
- writable workspace or build artifacts subsequently executed/uploaded by a trusted host service; cron/systemd/CI hooks; writable trusted gateway config or executable;
- other processes sharing the sandbox's network namespace, ability to join a different namespace, capabilities or helper binaries allowing host-network access.

Some are outside the **immediate network-peer** guarantee if the claim is explicitly restricted to direct network sockets. State such exclusions clearly and never sell that as "the agent cannot induce any other host egress." But if the claim quantifies over **all induced host egress**, these paths have to be mediated or excluded by enforceable assumptions.

At startup, reject any inherited/host-visible network FD or privileged socket not in the allowlist, and launch with tightly specified mounts, privileges and namespaces. Record the actual netns interfaces/routes and file descriptor table.

### R10-3. No tautological Lean theorem, please

The proposed state-machine rule "an untrusted process can emit only a request to the gateway" makes the desired conclusion immediate by construction. That's mathematically valid but risks repeating the auditgate "effect is whatever the model calls an effect" correspondence gap.

The first important checker is **not** the five-line induction. It is a **trusted topology/configuration validator** that fails closed unless:
1. the untrusted namespace genuinely lacks routes, external interfaces and host-net access;
2. only intended AF_UNIX resources cross the boundary;
3. the gateway owns the destination policy and no untrusted principal can mutate it;
4. all gateway-established peer sockets satisfy policy;
5. untrusted code has no privileged/delegated alternate network path.

Lean may formalize the gateway state machine and prove the policy invariant conditional on those facts. Then explicitly map validator checks, OS tests, pinned binaries/config hashes and remaining kernel/privileged-host assumptions to the hypotheses. A runtime observation test is not a universal refinement proof.

## Implementation questions to settle in code, not prose

### R10-4. Proxy compatibility is part of usefulness

Most package tools speak HTTP(S) proxy over **TCP host:port** (or direct sockets), not arbitrary custom framing to an AF_UNIX socket. An empty network namespace may also have loopback down by default.

Describe and implement the explicit local adapter:

    apt/pip/npm/etc.
        → optional 127.0.0.1 proxy adapter IN sandbox
        → bind-mounted AF_UNIX socket
        → trusted host gateway
        → fixed allowed remote peers

The adapter may be untrusted if it has no authority beyond sending requests to the gateway. The gateway must independently parse and enforce every new CONNECT/HTTP request; it must not trust the adapter's assertion of the destination. The adapter/socket's file permissions and peer credential checks should be tested and documented; ensure the local adapter doesn't accidentally become an unconstrained host proxy.

Set a small actual task identity and package/mirror/version. Demonstrate successful dependency install and tests without giving the sandbox a direct route. Report whether legitimate TLS validation, redirects, package mirrors/CDN redirects and caching are supported or require a deliberately narrower task.

### R10-5. Protocol/parser and file-descriptor attacks deserve first-class negative controls

Make an **expected outcome matrix** with at least:

- Allowed: exact permitted host + port via adapter, legitimate HTTPS CONNECT (if supported), required local service tests, dependency fetching, build/test.
- Denied and *externally observed absent*: raw IPv4/IPv6 TCP, UDP/ICMP egress, DNS outside gateway, forbidden host/port, malformed CONNECT, alternate URL authority and port, userinfo/fragment tricks, request smuggling/ambiguous headers, host suffix collision, untrusted redirects, and attempts to connect to host control sockets.
- Privilege/bypass controls: inspect inherited FDs; attempt namespace escape/join, raw socket, \`setns\`, untrusted child/fork, process restart, policy file mutation, gateway admin interface, socket-FD passing via \`SCM_RIGHTS\` (if protocol could support it), stress/flood and service restart/fail-closed behavior.
- Allowed-but-scope-limited **counterexample**: upload an arbitrary encoded secret in the path/header/body of a request or TLS tunnel to the **allowed** mirror. This must succeed or otherwise be characterized without pretending that the reachability invariant supplies confidentiality.
- Egress accounting: independent host observer must identify every test endpoint/peer reachable, not only a few denied destination-side counters. Include packets to addresses with no cooperating test server; a failed TCP handshake can still have emitted a forbidden packet.

If the gateway accepts plaintext absolute-URI HTTP requests and CONNECT, write an exact grammar and decide which forms are accepted or rejected (CONNECT authority syntax; IPv4/IPv6 literals; ports; Host mismatches; absolute URI; HTTP versions; transfer/framing; maximum request sizes). Prefer a small well-tested standard proxy parser with a strict policy layer to an ad hoc security-critical parser.

### R10-6. What exactly will the 'gateway allows mirror' test establish?

The strongest immediate test should compare:
1. **OS-observed egress effects** from host/gateway (IP, port, protocol, timestamps or connection ID);
2. gateway permitted/denied decisions and pinned destination mapping;
3. expected effect classifications in a matrix;
4. honest task exit status and test outcome.

An unauthorized TCP **SYN** that reaches the host interface is already a security failure for a "zero outbound packets to forbidden peers" claim even if the remote server never accepts. A gateway socket opening before a deny decision is also a failure. Avoid observing only completed connections.

Use independent external tracing where possible, plus a deterministic test topology that you control. No model tokens required.

## Auditgate v1 residual note (keep as library caveat; no need to reopen that project now)

The PostgreSQL primary key/Lean Nodup guarantees **no duplicate effect records**, not exactly-once external RabbitMQ execution. The concurrency matrix does not simulate process crashes between external dispatch and worker acknowledgement. The SQL \`audited_at <= dispatched_at\` wall-clock test is weaker than causal/transactional ordering (wall clocks can step); use a transactional proof/ordering witness. The demonstration credentials and app-controlled identity should remain explicit unresolved deployment premises. These are not blockers for SC-03.

## Concrete acceptance gate for Claude round 11

I would prefer an implemented **minimal vertical slice** over further prose:
1. Exact dev-environment/task, declared network needs, pinned destination policy, expected honest outcome.
2. Namespace/process launcher + AF_UNIX host gateway (+ adapter if needed), all committed with **safe test-only** defaults.
3. An external observer/tracing script that records attempted forbidden network packets, including failed connections.
4. Expected-outcome tests: at least one honest task passes; direct forbidden peer attempts fail; forbidden proxy requests are denied; allowed-host confidentiality counterexample is explicit; child processes cannot bypass; fail-closed gateway/policy failure.
5. A Lean state-machine theorem (standard axioms) plus a **premise/evidence mapping table** identifying which runtime obligations are established by checks and which remain unverified.
6. CI green for deterministic tests feasible on GitHub runners, with environment capability limitations surfaced; do not silently skip isolation tests. A privileged runner/VM may be needed for some packet-observation tests.

**If a useful vertical slice is not feasible on available hardware or within trustworthy isolation, report the blocker rather than making a hypothetical theorem the next milestone.**

**DIALOGUE_STATUS: CONTINUE**
