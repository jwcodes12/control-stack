# Adversarial review of the restricted Compose extractor

The extractor accepts a small allowlist, not arbitrary Compose. All table entries
are scoped configuration/runtime facts; CONDITIONAL still depends on faithful
extraction and full protocol refinement. Authorization labels never hide paths.

| Authority source | Treatment / evidence |
|---|---|
| Agent/reviewer/approver binds | Only the declared channel source at `/channel`, read-only. Every other bind is UNKNOWN; `unlisted-host-mount`, `writable-channel-mount`, `channel-target-shadow`. |
| Broker/receiver binds | Declared DB at `/private`, channel at `/channel`, receiver sink at `/output` only. Unlisted binds UNKNOWN; direct sink/DB authority checked independently of allowlist. |
| Docker/containerd/podman sockets | Explicit PRESENT escape authority even read-only, including ancestors of conventional socket paths; `runtime-socket-mount` and socket-variant regression. Never launched. |
| `/`, `/proc`, `/sys`, `/dev`, `/etc`, `/var/lib/docker` | Sources overlapping these paths yield named PRESENT escape authority; sensitive-path regression. Never launched. Container defaults inside its namespace are not host bind sources. |
| Trusted-source directory, descendants or ancestors | Explicit escape authority for `/slice/trusted_stack`, `/slice/entry.py` and this clone's trusted source, entry point, extractor and verifier directories; `trusted-source-mount`. Code is baked into the pinned image in the live run. Other source directories are unlisted UNKNOWN. |
| Writable protected sink/DB, ancestor/descendant binds | PRESENT write/read edges and refuted ownership/custody; writable-sink and agent-DB fixtures. Duplicate derived edges merge conservatively. |
| Shared SELinux z bind label | Explicitly supported on disposable bind sources; selected mount authority strips this label option but the original Compose pin retains it. Host Enforcing does not imply Docker SELinux enforcement. |
| Other bind options, short-form/relative paths, mount types, volumes_from, tmpfs, secrets/configs, interpolation | UNKNOWN via strict field/type allowlist. Parent traversal is UNKNOWN (`mount-parent-alias`). Target shadowing is UNKNOWN. |
| Privileged, host networking, devices, capabilities, PID/IPC/user namespaces, group_add, security_opt, runtime, sysctls | Explicit privileged/host-network refutation; all other service keys UNKNOWN. Docker capture flags nondefault selected host settings as runtime drift. |
| Root/missing UIDs, agents sharing trusted UIDs, supplementary identities | Python refutes root/collisions; unresolved UID is UNKNOWN. Supplementary-group configuration UNKNOWN; daemon capture detects GroupAdd. Default numeric Docker UID mapping remains a daemon/kernel premise. |
| Missing/drifted mounts, images, identities, environment names, extra runtime services | MISSING/DRIFT or UNKNOWN, never absence evidence. Capture retains raw inspect hash and checks resolved content image ID. |
| Networks, external routes/ports, DNS, extra hosts, network_mode, aliases | Exactly one declared internal network per service; other topology/key shapes UNKNOWN. `missing-isolated-network`; host-network refuted. External deputies remain unsupported. |
| Environment credentials | SINK/CREDENTIAL/TOKEN/SECRET/KEY/PASSWORD/PASS/PASSWD/AUTH/COOKIE/PRIVATE names yield UNKNOWN credential edge. Other names outside SLICE_ROLE/PYTHONPATH yield UNKNOWN (`credential-password`, `unlisted-environment`). Values are never emitted in selected IR. |
| Commands, entrypoints, builds, mutable images, dynamic sidecars/roles | Unsupported Compose fields UNKNOWN; mutable/unresolved images UNKNOWN; deputy UNKNOWN; role counts refuted. Docker capture detects command/entrypoint changes. Pinned image/code correspondence is residual, not established by hashing host sources alone. |

The self-review found and closed the unlisted bind, writable channel, target
shadow, environment-name and missing-network holes. Each has a fixture. No known
**expressible configuration fact** in this restricted profile is silently accepted
as denied authority. Tier 1 strengthens the Lean raw-IR projection to the full
finite Python rules; 26 fixtures and 250 seeded mutations now agree. The historical
subset discrepancies remain archived as historical evidence, not current scope.

Still missed at the observational level: host symlink/hardlink aliases that change
behind an allowed source, inherited descriptors, processes injected through Docker
exec, runtime image/code tampering, daemon UID remapping, storage rollback, and
changes after capture. Fixtures `runtime-alias`, `inherited-descriptor`,
`injected-helper`, `runtime-code-tamper`, `daemon-uid-remap`, `storage-rollback`
and `post-capture-drift` respectively show that **reported** versions of each
produce UNKNOWN/drift and UNASSURED. They do not pretend to detect covert,
unreported changes. These are not claims discharged by this collector. Explicit
configuration of aliases/remapping/helper injection is UNKNOWN, but covert state
cannot be detected from selected daemon facts. Faithful extraction and protocol
refinement explicitly exclude such undetected divergence. This is a residual
limitation of the conditional claim, not a reason to label UNKNOWN as safe.
