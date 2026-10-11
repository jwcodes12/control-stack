# Linux per-process agent confinement and OS effect limitations

This runtime addition does **not** establish universal OS/network effect
mediation. The module trusted_stack/agent_confinement.py is a real kernel
confinement mechanism for **one separately launched, unprivileged agent
process** and is fail-closed when prerequisites are absent.

Before executing preloaded untrusted Python source, it:
1. Requires a non-root, real/effective UID-matched principal.
2. Optionally opens the trusted broker Unix socket and verifies the socket
   inode owner and SO_PEERCRED peer owner are a **different trusted UID**.
3. Preserves only stdin/stdout/stderr (all three redirected to /dev/null)
   and fd 3 (either the authenticated already-connected broker, or /dev/null).
4. Installs PR_SET_NO_NEW_PRIVS, Linux Landlock ABI 3+ (no write grants;
   all handled filesystem write, create, deletion, refer and truncate
   operations denied), and a libseccomp deny-list for sockets, network,
   exec/fork/clone, namespace/mount/ptrace, cross-task signaling,
   alternate I/O interfaces and relevant metadata mutation syscalls.
5. Executes already-compiled source, which may send **one** JSON-framed
   request using os.write(3, request) and receive its response using
   os.read(3, ...). The trusted broker continues to validate the exact
   review/approval/nonce/lease/agent-or-delegate/global budget.

Usage (prepare separate trusted broker and reviewed one-use approval first):

    python3 -m trusted_stack.agent_confinement --script /agent/script.py       --broker-socket /trusted/broker.sock --broker-uid 10000

A host-prerequisite probe is:

    python3 -m trusted_stack.agent_confinement --probe --script /agent/script.py

The independent test runs actual syscall calls:

    python3 -m unittest trusted_stack.test_agent_confinement -v

If Linux kernel Landlock or libseccomp support is absent, the agent source
**will not execute**. The test reports unsupported hosts explicitly;
a skipped test is NOT a positive result. The dedicated GitHub Actions
workflow requires both probe and live negative controls on its runner.

## Residual premises; never present as deployment assurance

- This is **per-process confinement**, not confinement of all host
  processes. External same-UID helpers, already-running tasks, privileged
  host actors, processes not launched through this entrypoint, or malicious
  trusted brokers can still perform actions. The launcher cannot attest
  that every actual agent/side-task ran inside its boundary.
- This uses a deny-list of selected Linux syscalls and Landlock-covered
  file mutations, not a closed allow-list or complete syscall semantics
  proof. Unknown/new syscalls, device ioctls, obscure IPC, kernel bugs,
  shared memory inherited through external channels, and other paths
  require a separately audited container/VM/capability closure.
- Read observations, timing and CPU use, return status, untrusted memory,
  process side channels and broker response semantics remain unbounded.
  Linux kernel Landlock ABI/feature negotiation is only a check, not
  remote attestation or an independent trust root.
- The approved downstream local-file effect uses the trusted receiver's
  separate SQLite writer lock, not a jointly atomic filesystem/database
  transaction. HALT cannot undo effects already published.
- A sufficiently detailed theorem of the OS/kernel, seccomp filters,
  Python interpreter and actual host system is not established by this
  code or by trace differential tests.

This slice can establish narrow real effect denials when host tests pass.
It cannot satisfy the universal OS/network, independent F6 calibration,
or full model-to-runtime refinement assurance claims. All 28 scenario
deployment statuses remain CONDITIONAL.
