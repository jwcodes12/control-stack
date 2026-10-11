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
| Compose syntax and bind options | Fresh CLI normalization expands YAML, short-form paths and interpolation before strict checking. Source realpaths are observed. Unsupported bind options and target shadowing are UNKNOWN. Legacy v0 parsing does not resolve host aliases. |
| Privileged, host networking, devices, capabilities, PID/IPC/user namespaces, group_add, security_opt, runtime, sysctls | Explicit privileged/host-network refutation; all other service keys UNKNOWN. Docker capture flags nondefault selected host settings as runtime drift. |
| Root/missing UIDs, agents sharing trusted UIDs, supplementary identities | Python refutes root/collisions; unresolved UID is UNKNOWN. Supplementary-group configuration UNKNOWN; daemon capture detects GroupAdd. Default numeric Docker UID mapping remains a daemon/kernel premise. |
| Missing/drifted mounts, images, identities, environment names, extra runtime services | MISSING/DRIFT or UNKNOWN, never absence evidence. Capture retains raw inspect hash and checks resolved content image ID. |
| Networks, external routes/ports, DNS, extra hosts, network_mode, aliases | Exactly one declared internal network per service; other topology/key shapes UNKNOWN. `missing-isolated-network`; host-network refuted. External deputies remain unsupported. |
| Environment credentials | SINK/CREDENTIAL/TOKEN/SECRET/KEY/PASSWORD/PASS/PASSWD/AUTH/COOKIE/PRIVATE names yield UNKNOWN credential edge. Other names outside SLICE_ROLE/PYTHONPATH yield UNKNOWN (`credential-password`, `unlisted-environment`). Values are never emitted in selected IR. |
| Commands, entrypoints, builds, mutable images, dynamic sidecars/roles | Overrides and builds UNKNOWN; unavailable images UNKNOWN; deputy UNKNOWN; role counts refuted. Fresh inspection checks exported baked source bytes and the known entrypoint, with explicit numeric USER override and principal-policy matching. Daemon observations remain untrusted. |

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

## Tier 3 fresh-scanner coverage

The default `cstack scan` now uses `deployment/scan.py`, schema 0.1 and Compose CLI
normalization. All 44 static fixtures still pass through the legacy pure parser
for finite-rule regression; this does not turn them into physical observations.

| Additional authority source | Treatment / evidence |
|---|---|
| cap_add, devices, host PID/IPC, seccomp/AppArmor unconfined, userns_mode | UNKNOWN service feature, separate static fixture for each; never launched. |
| named volumes, volumes_from, tmpfs, secrets, configs | UNKNOWN unsupported authority, separate fixtures; never launched. |
| extra_hosts, published ports, read_only rootfs, depends_on | UNKNOWN outside supported profile, separate fixtures; conservative over-rejection is explicit. |
| entrypoint/command overrides | UNKNOWN even if an override looks harmless; separate fixtures. |
| Source symlinks and realpaths | Fresh host stat and strict resolution, including declared protected sources and runtime binds. Protected-sink aliases become PRESENT; benign channel aliases are permitted; missing sources UNKNOWN. Scanner tests create actual disposable symlinks. |
| Host store custody | DB and sink must be directories, owned by their declared trusted UID, with mode 0700; channel directory must be broker-owned 0755. Other facts UNKNOWN. Permission drift after capture remains outside observation. |
| Image USER, entrypoint, setuid/setgid | Local inspect plus export of a stopped, isolated, harmless-entrypoint container; never started. Numeric Compose user must explicitly override image USER. Any setid entry, unavailable image, unexpected entrypoint/command or image-declared volume is UNKNOWN. |
| Baked reference code and principal policy | Exported trusted Python bytes must match known sources. Role UIDs must match literal principal arguments in that entrypoint; environment must preserve reference dispatch and PYTHONPATH. Mismatch UNKNOWN. A separated Compose UID assignment cannot silently override baked admin authority. |

Explicit observational exclusions: covert hardlink changes, inherited descriptors,
Docker exec injection, runtime code changes, malicious daemon reports, UID mapping
outside selected daemon facts, storage rollback and changes after capture. Existing
negative fixtures cover reported forms; none proves detection of covert forms.
The image inspection checks the merged filesystem metadata and selected trusted
code bytes, not arbitrary native library behavior, kernel integrity or all runtime
process capabilities. These remain extraction/TCB premises. Legacy v0 snapshots
and schema-only migrations do not establish fresh realpaths, custody or image facts.
