# Anti-rollback harness: a gate bound to an external monotonic anchor

This is a defensive, benign runtime check of the `anti_rollback` premise (ASSURANCE-LEDGER.md: SC-14, SC-28, and the
SC-26 nonce history). It is the runtime counterpart of `ControlStack/Core/AntiRollback.lean`.
Preregistration: [`prereg/ANTI-ROLLBACK.md`](../../../prereg/ANTI-ROLLBACK.md).

| file | role |
|---|---|
| `anchor.py` | Anchor service, the stand-in for a TPM NV counter or transparency-log head. Runs as its own numeric UID with a private 0700 directory. Holds `(version, digest)` with fsync on every change and keeps an append-only `anchor.log`. Over a Unix socket (SO_PEERCRED) it allows only `read` and `increment(to = version + 1)`, both from the gate UID. |
| `gate.py` | Gate: a budget + one-use-nonce ledger in SQLite (`synchronous=FULL`) with a SHA-256 digest chain. A spend checks store == anchor, commits `v+1`, increments the anchor, then performs the effect. The effect is a line in `effects.log`, which lives outside the store. The same check runs on every operation and at startup. When the store is exactly the next record (the crash window), the gate recovers; otherwise it fails closed. Crash points: `after_commit`, `after_anchor`, `after_effect`. `--anchor-off` (needs `AR_NEGATIVE_CONTROL=1`) is the negative control. |
| `run_ar.py` | H1–H4 runner. The harness is the operator: it takes snapshots, restores them (cold and hot), deletes the store and crashes the gate. Also handles independent reconciliation (anchor log + effect log only), receipts, preflight and cleanup with a `/proc` check. |
| `test_ar.py` | No-root unit tests of `GateCore` against an in-process `AnchorStore`. These include forged-record cases that the runtime operator does not attempt (see the prereg §1). |

**UIDs:** anchor 23921, gate 23922, client 23923. These are bare numbers; no accounts are created.

**Scope:** every case runs in a fresh `/var/tmp/ar-run-*/<case>` directory, and the whole directory is removed at
the end.

```sh
python3 -B experiments/anti-rollback/harness/test_ar.py
sudo -n /bin/python3 -B experiments/anti-rollback/harness/run_ar.py --kind dry --reps 1 --out /tmp/.../ar-dryN
# evidence, after the prereg is frozen and committed:
sudo -n /bin/python3 -B experiments/anti-rollback/harness/run_ar.py --kind evidence --reps 5 \
  --out experiments/anti-rollback/evidence/run-1
```

**What this does not cover:**
- A real TPM or transparency log; the anchor's own integrity is a premise.
- An operator who forges records rather than restoring old ones. Record integrity, for example a MAC with a key the
  operator lacks, is a separate premise, as in the Lean model.
- Restores of the anchor itself.
- Multiple gates sharing one anchor.
