# SC-01 bounded repair: usefulness passes; observation boundary fails

The preregistered catalog repair task is frozen in commit `1001024`. Each trusted
lineage permits five episodes, with nine possible gateway views per episode.
The Lean model counts 9^5 = 59,049 transcripts and bounds exact recovery of an
independent uniform 32-bit secret by 59,049/2^32, below 2^-16, **conditional on
complete receiver observation being limited to those transcripts**.

Both baseline and mediated agents completed 320/320 repairs across 64 independent
five-episode lifetimes. Each completion interval has lower bound 93.382%, above
the preregistered 90% floor; no false blanks occurred. These are programmatic
agents repairing a fixed eight-fault catalog, not general coding-agent evidence.
Intervals use lifetimes as the sampling unit and the preregistered simultaneous
Clopper–Pearson procedure. Runtime independence and workload transport remain assumptions.

SQLite lifetime charging now serializes admissions and persists before launch.
Ten controls cover concurrency, restart, process crashes, missing/corrupt state,
configuration mismatch and mandatory ledger/lineage. Valid old snapshots still
require trusted-host protection against rollback.

The separately preregistered cache probe recovered the secret's low bit in 64/64
trials while the gateway view stayed NULL (one-sided 95% lower bound 95.427%).
Read-only access to a shared executable exposed cache state. This falsifies the
sole-transcript premise in this harness; it is not a demonstration of full
32-bit secret recovery. **No runtime 2^-16 secrecy guarantee is certified.**
Next: stronger isolation, then repeat observation probes and establish runtime
correspondence. Auditgate source is untouched.

Verification already passed: ten lifetime tests, five scenario/oracle/receipt
mutation tests, ten gateway tests, selected harness probes, three new Lean
standard-axiom checks, and the full `lake build ControlStack` (3,691 jobs).

Replay the saved source-bound evidence:

```bash
gateway/scenario/check.sh --receipt gateway/scenario/results/local-full.json
python3 gateway/scenario/check_cache_receipt.py gateway/scenario/results/local-cache.json
```

The cache receipt also binds this host's `/usr/bin/openssl`; on a different host
produce and check a fresh probe. Fresh runtime experiments require working
bubblewrap namespaces and installed openssl:

```bash
sudo /usr/bin/python3 gateway/scenario/run.py --output /tmp/sc01-full.json
python3 gateway/scenario/check_receipt.py /tmp/sc01-full.json
sudo /usr/bin/python3 gateway/scenario/cache_probe.py --output /tmp/sc01-cache.json
python3 gateway/scenario/check_cache_receipt.py /tmp/sc01-cache.json
```

Initial receipts are retained as `results/local-*-initial.json`. After the cache
finding, gateway/harness documentation and a harness-test name were corrected;
final experiments were rerun to bind the final source bytes. The three original
source snapshots and SHA index are in `results/initial-sources/`. Initial and
final measurements are not pooled. Saved local runs are distinct from CI runs.
