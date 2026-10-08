# SC-03 premise/evidence map

`ControlStack/EgressGate.lean` proves that model traces preserve a pinned immediate
peer/gateway-origin invariant, including socket attempts that fail. The model
exposes direct attempts, validator-rejected launches, policy tampering, gateway
startup, crash and requests. Lookup only chooses peers from the fixed table.
It does not formalise HTTP parsing, Linux syscalls, PID namespace semantics or TLS.

| Premise / property | Evidence | Remaining obligation |
|---|---|---|
| Gateway lookup yields a pinned peer; trace preserves peer/origin invariant | `lookup_pinned`, `step_safe`, `trace_safe`; kernel check, standard axioms | Python parser/lookup implementation is not proved to refine Lean |
| Unsafe launch is inactive; gateway crash prevents requests | `failed_launch`, `crash_closed`; startup/missing-socket tests | Actual Linux enforcement remains a correspondence assumption |
| Private namespaces, no external interfaces/routes/capabilities | Actual namespace validator before relay/attacker; namespace mutation; direct/raw/child/fork/setns probes | Kernel correctness and inaccessible privilege escalation are assumed |
| No inherited network descriptor | Actual pre-exec FD validation; deliberately inherited live TCP FD rejected | Arbitrary launcher/supervisor authority is excluded |
| Only intended host socket and mounts | Fixed minimal mount contract, mountpoint allowlist, host control/abstract socket probes | Runtime directories trusted; no unknown nested authority in supplied runtime tree; no host watcher executing workspace artifacts |
| Policy/code protected from attacker | Policy absent; code/config read-only; policy/code/proc-root/signal probes | Host operators and shared kernel trusted; host process compromise excluded |
| Gateway connects only after permission to numeric pinned TCP peer | Independent host strace vs prior permit; packet/destination deltas | No universal syscall correspondence or all-host process attribution proof |
| Forbidden attempted transmissions observed absent | AF_PACKET including failed SYNs; destination counters; positive calibration; drop accounting; packet mutation | Observation is scoped to bounded fixture addresses/ports, not arbitrary internet traffic |
| Honest usefulness | Wheel install/compile/test; HTTP, validated HTTPS tunnel and loopback service controls; recovery after every attack | Real package ecosystems/deployment workloads untested |
| No confidentiality claim | Synthetic secret at allowed mirror; alternate TLS SNI at allowed peer | Authentication of virtual origins/downstream hops deliberately unclaimed |

All runtime statuses refer to a disposable dev fixture. No production sandbox is
deployed. The assurance verdict remains CONDITIONAL. Neither a successful finite
attack corpus nor the model theorem establishes universal Linux refinement.
