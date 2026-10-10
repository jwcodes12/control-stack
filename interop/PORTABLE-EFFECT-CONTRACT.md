# Portable control-stack effect contract (proposal v1)

## Separation of concerns

The **admission policy and Lean model** should be independent of any agent
programming language or host OS. A request names a **staged content digest**,
**pre-reviewed destination**, **one-use nonce**, **lease identifier** and a
finite cost. The trusted gate binds it to a principal obtained through an
**authenticated transport** and checks authorizations/budgets/HALT *before*
admitting a downstream effect. Agents never receive direct authority to
perform the target consequential effect.

```text
Python / Node / Java / Rust / Go / Wasm / any agent
             | portable message + authenticated caller identity
             v
       trusted admission policy   <->   OS-neutral Lean transition model
             | admit / deny
             v
      trusted effect executor
             | chosen host backend
             v
 Linux (Landlock/seccomp/VM) / Windows (AppContainer/WFP/VM) /
 macOS (VM/approved sandbox entitlement) / WASI capability host
```

**Keep four contracts distinct:** (1) agent request encoding, (2) authenticated
transport, (3) admission-state transition and durable audit, and (4)
host-specific effect execution/confinement. A working portable wire client
establishes ONLY (1); it is never proof of (2)–(4).

## Current reference wire protocol

Reference broker: `trusted_stack/server.py`. A connection permits **one
request**. UTF-8 JSON object followed by LF, maximum 1,500,000 bytes including
LF. The response is one LF-terminated JSON object; `ok` is a boolean.
`{"ok":true,"result":...}` acknowledges admitted commands; `{"ok":false,
"error":"DENIED"}` is a uniform rejection. A lost response does not roll
back a committed effect and must not be interpreted as rejection.

Commands and *exact* required field sets (all other fields rejected):

| op | fields |
|---|---|
| stage | body_b64 |
| review | digest |
| issue_lease | lease_id, agent_uid, budget, expires |
| approve | nonce, digest, destination, agent_uid, lease_id, expires |
| revoke | lease_id |
| delegate | nonce, delegate_uid |
| revoke_delegation | nonce |
| release | nonce, digest, destination, lease_id |
| effect_release | nonce, digest, destination, lease_id |
| halt | (none) |
| state | (none) |

**Transport:** current implementation uses Unix-domain stream sockets and
Linux `SO_PEERCRED` for the *actual caller UID*, not any `agent_uid`
claim in JSON. `agent_uid` is only the **target** of an admin/approver
action. Other transports require their own independently verified binding
(e.g., OS identity on named pipes, mutually authenticated workload
credentials), not an unauthenticated TCP endpoint. A polyglot Node
reference client is in `interop/node/control_stack_client.mjs`.
It is **not a sandbox** and cannot independently verify the broker's UID.

**Non-neutral details currently remaining:** the broker/runtime is Python,
durable state uses SQLite, filesystem publication is POSIX, and the current
Linux confined launcher executes **precompiled Python source**. A Node
client can request an effect using exactly the same policy but that does
**not** make a native Node process confined by the Python launcher.

## How to make the complete stack portable

1. Define an OS/language-neutral, typed `EffectRequest`, `Decision`,
   `CommittedEffect` and `DeliveredEffect` transition system in Lean,
   with rejection/one-use/HALT/budget/delegation invariants. Make
   message encoding and canonicalization conformance testable across
   languages, including malicious duplicate fields and normalization.
2. Make the controller a separately privileged **trusted service**.
   Agents may use any language but get only an authenticated request
   channel, not raw network/filesystem/exec authority.
3. Implement host **adapter contracts** with explicit capability closure:
   Linux OS sandbox/VM; Windows restricted token + AppContainer/WFP/VM;
   macOS VM or properly supported OS security frameworks; and a
   sandboxed WASI component model for languages compiled to WebAssembly.
   Default to DENIED if a host lacks required controls.
4. Give each adapter adversarial OS-specific negative tests and an
   explicit Lean-to-implementation correspondence/evidence obligation.
   A backend is never marked verified because a Linux backend passed.
5. For workloads suitable for WebAssembly, a WASI capability host is the
   best near-term **cross-platform** route: ungranted host capabilities
   simply are not imported. For arbitrary native agents, per-OS
   VM/sandbox drivers remain necessary; portable APIs alone cannot
   intercept their direct syscalls.

**Guarantee scope:** formal invariants can be portable only under an
explicit simulation/capability-capture premise. Neither current Linux
proof candidates nor successful Node/Python RPC tests discharge it.
All deployment claims remain CONDITIONAL.
