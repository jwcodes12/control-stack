# Trusted-stack reference service — F1 / F3 / F4 / F5 / F7 / F8

This is a **narrow, non-production reference enforcement boundary**.
The only modeled external effect is a durable record in SQLite's
\`releases\` table. **It does not launch programs, deploy artifacts, execute
privileged commands, provide OS sandboxing or confine observations.** It
cannot be counted as a deployment-validated implementation of F1/F3/F4/F5/F7/F8.

A trusted standalone process receives one JSON request per Unix-domain socket,
looks up the calling process UID using Linux \`SO_PEERCRED\`, and authorizes
operations based on disjoint agent/reviewer/approver/admin UID sets. No UID is
accepted from a request. Only the trusted broker UID should have read/write
permission to the SQLite state (0600). The global release cap, per-agent lease
counter, exact-content SHA-256, distinct review and approval, one-use nonce,
expiry, revocation and absorbing HALT are checked under one \`BEGIN IMMEDIATE\`
transaction before writing each release record.

This supplies a **limited executable check-before-record** proof target.
The actual host must enforce (and independently verify) that *all real harmful
effects* are made exclusively through an appropriate trusted adapter that
performs authorization **before** the effect, and closes races or partial
failure windows. Adding such an adapter to this reference service without
re-deriving the correspondence is unsafe.

Run library-level tests (no external service):

\`\`\`sh
python3 -m unittest discover -s trusted_stack -p 'test_*.py' -v
\`\`\`

Example trusted host configuration (requires four distinct OS UIDs,
a trusted broker process and a private state directory):

\`\`\`sh
python3 -m trusted_stack.server --db /path/to/private/state.sqlite3 \
  --socket /path/to/socket --agents 12001 --reviewers 12002 \
  --approvers 12003 --admins 12004 --bootstrap-cap 10
\`\`\`

Remove \`--bootstrap-cap\` on subsequent starts; initialization refuses to
overwrite the original DB. Do not use an untrusted directory or run the broker
under the agent UID.

**Open premises:** UID separation/OS and broker integrity; clock rollback;
persistent database rollback, crash/power-loss/SQLite storage honesty; distinct
reviewers actually inspecting contents; SHA-256 collision assumptions;
the absence of any non-broker harmful action route; subprocesses and
confused deputies; meaning/harmlessness of the reviewed contents; real
effect dispatch consistency and external-system commit. This code does not
create a third-party attestation or resource usage meter.
