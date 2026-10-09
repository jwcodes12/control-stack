# SC-10 v2: serialized policy-decision reference (new candidate)

This directory is not part of the frozen PREREG-SC10-POLICY-v1 harness and does
not replace its pinned evidence. Original scenarios/SC-10/harness files remain unchanged.

## Problem addressed

The original policy evaluator fetches latest over an RPC and then separately
computes and logs its decision. A concurrent admin update can occur between
read and use; the existing Lean model assumes those events are atomic
(see ControlStack/Scenarios/SC10ReadUseGap.lean, draft PR #22).
The original store also starts with an empty in-memory version list rather than
replaying its retained disk journal.

## Prototype v2

atomic_store.py puts admin policy writes and DECISION RECEIPTS behind one
serial Unix-socket loop with one append-only journal. A write or decision:
1. Is serialized with every competing request on that service.
2. Is written as a canonical JSON line with a sequential index, prior-record
   SHA-256 hash, and source-bound policy digest.
3. Is fsync'd before the API responds.
4. Is replayed and checked (including version and decision freshness) at restart;
   malformed, truncated or altered journals fail closed. A nonblocking exclusive
   file lock rejects another store instance sharing the same journal.

Only a strict allow-list object with an array of distinct hostname strings is
accepted. Untrusted peers may request decisions; writes require the configured
admin PID as observed by Linux SO_PEERCRED. This is pid authentication, not
multi-UID security isolation. All socket callers under the same UID may still
have filesystem and process-control capabilities outside this model.

There is NO firewall rule installation or other external effect here.
The serialized point is the durable decision receipt. A caller could apply
the returned decision later when a newer policy exists. That TOCTOU and
the all-effects-mediation obligation remain unsolved.

## Reproduction

From repository root on Linux:

    python3 -m unittest discover -s scenarios/SC-10/hardened -p 'test_*.py' -v

Run the service only in an owner-private, unprivileged, disposable directory.
Do not attach it to production network effects or frozen evidence directories.

The tests cover unauthorized writes, invalid schema, tightened policy with
decision receipts, restart replay, truncated or tampered journal rejection,
and actual concurrent Unix socket requests with replayed ordering.

## Remaining proof, runtime and review obligations

- Connect the real serialized socket requests and JSON receipts to a Lean
  machine, including parsers, exceptions and refusals.
- Pin source hashes and separately preregister tests of v2 semantics.
- Enforce decisions at the actual EFFECT, not when returning an authorization
  receipt. Disallow replay and effect-after-policy-update.
- Prove principal separation beyond same-UID peer PID, protected journal
  custody, and exclusive administration of the socket.
- Verify hash-chain custody (not a signature), disk/fsync and directory-entry
  durability, abrupt crash recovery, daemon lifecycle and multi-host identity.
- Independently review the English catastrophe specification, elaborated Lean
  statements, and every environment trust root.

No scenario manifest, historical evidence hash or DEPLOYMENT_ASSURED status is
altered or justified by this reference implementation.
