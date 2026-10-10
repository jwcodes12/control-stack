# Tier 2 adversarial self-review

The initial and final experiments each ran seven safe real Docker cases. Each
scanned Compose path is exactly the one passed to compose up. No dangerous fixture
was launched. The harness accepts only fixed case names, validates own state paths,
bind types, image tag ownership and forbidden service features before launch.
Docker raw inspect is independently normalized and hash checked; it is not attestation.

Usefulness is two actual agent identities, two exact approved bodies and one shared
cap of 2. The cap-1 concurrency experiment has a separate shared start signal after
both contender processes report readiness. Actual sink bytes and read-only SQLite
backups corroborate outcomes; the broker log alone is never substituted for a sink.
Reconciliation distinguishes admission, durable receipt and unknown-commit. HALT
serializes after an in-flight write and does not retract its bytes. The real KILL
occurs after publication and before receipt, and two retries yield one receipt/file.

Findings fixed before final run: reverify a fresh runtime inventory after receiver
restart; remove an image only after its cstack-r2 ownership is checked; reject
nonregular sink artifacts rather than following links; explicitly audit volumes
and images alongside containers/networks. The final seven-case run exercises all
fixes. Nine raw IR snapshots get independent kernel certificates; byte-tamper and
symlink mutations must fail the archive checker.

Shared SELinux z labels avoid private-label conflicts across shared mounts. Docker
here does not advertise SELinux enforcement; no enforcement claim is inferred from
host Enforcing status. Landlock is inactive on this host and remains separate native
QEMU evidence. The egress test uses reserved TEST-NET TCP and verifies absence of a
default IPv4 route, not arbitrary Internet safety or covert-channel elimination.
UID collision demonstrates admin confusion/HALT, not a fabricated direct sink write.
A writable bind alone cannot bypass 0700 DAC; the negative explicitly changes DAC.

The first image build failed because an added image-tag argument also entered the
chown command; fixed, and build attempt 2 passed. Both actual container runs and
independent replays passed. All failures are retained in deployment/runs/tier2.
Historical image/entry manifests preserve prior container evidence independently
of new example pins. Frozen evidence and EgressGate remain unchanged. Universal
ExtractionFaithful and ProtocolRefinement are still residual assumptions. No R3
or independent security review is claimed; final-head CI remains an exit check.
