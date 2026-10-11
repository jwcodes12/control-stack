# Exact-nonce one-hop delegated effect release (review scope)

The reference Unix broker now accepts `delegate {nonce, delegate_uid}` from the
**actual peer-authenticated owner agent UID** of an unspent, unexpired approval
and active matching lease. Only the single designated peer agent UID can
subsequently issue `release` or `effect_release` for that nonce. A grant is
immutable, not transitive, and cannot widen the reviewed artifact digest,
destination, lease, approval signer, cost or global/per-lease budget. After a
grant the original owner also cannot release that nonce. A grantor or trusted
admin may irrevocably `revoke_delegation {nonce}`; this also blocks a previously
admitted but not yet published local receiver effect.

The release row retains the approval/lease owner's UID. An atomic
`delegated_releases` row independently records the exact invoking delegate,
nonce and grantor, and the trusted local receiver validates this provenance,
authorization, expiry and revocation again under the same SQLite lock as HALT.

**Threat boundary:** `server.py` derives the initiating UID from Linux
`SO_PEERCRED`; request JSON can provide only the delegate's **target** UID,
never the invoking UID. The unit tests simulate the originating UID. This is
one-hop delegated **approval use**, not delegation of an OS capability or
arbitrary subprocess execution. Agents can still bypass the broker using
unconfined host/network capabilities. A malicious trusted admin or compromised
broker/database can forge grants. Actual UID separation, durable storage,
clock validity, host isolation, OS scheduling, controlled receiver custody,
and complete effect mediation remain premises.

The SQLite schema was extended with `delegations` and `delegated_releases`.
Existing already-initialized databases are **not automatically migrated**;
a trusted offline schema migration with a versioned backup and audit is
required before enabling this operation for preexisting deployments.
A missing table fails closed, not silently grants authority.

Run `python3 -m unittest trusted_stack.test_delegation -v` and the full
trusted_stack suite; verify the real separate-UID broker test on Linux. The
F8 Lean lifecycle currently treats the delegate ID as an unconstrained tag
and therefore does **not** formally establish this new runtime's identity
or grant behavior. Additional relation proofs and adversarial tests remain
required before labeling delegated execution formally verified.
