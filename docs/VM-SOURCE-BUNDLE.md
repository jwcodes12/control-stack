# Source-bound SC-01 VM replay package (not a VM run)

To reproduce the *source inputs* for the QEMU TCG VM test on a machine with an authorized QEMU environment:

```bash
python3 tools/package_vm_replay.py --output /tmp/sc01-source-v1.tar.gz
python3 tools/package_vm_replay.py --verify /tmp/sc01-source-v1.tar.gz
python3 -m unittest tools.test_vm_package -v
```

The deterministic archive includes the SC-01 contract, VM scripts, image lock, prior reviewed configuration and source-only guidance, plus `SOURCE-MANIFEST.json` with SHA-256 hashes for every included file. No guest OS binaries, disk contents, old result receipts, preregistrations, experimental evidence, authentication credentials, or private SSH material is packaged. It refuses overwriting output. It does not claim the archived historical config is usable on another host: installed QEMU executable hashes, absolute paths, CPU/NUMA affinity, and provisioned image bytes require a host-specific, newly pinned configuration and separate inspection. Do not edit archived evidence.

On an approved VM host, run the steps in [gateway/vm/README.md](../gateway/vm/README.md) with a **new** output folder and receipt paths. Provision and re-check with `check_isolation.py --files`; only afterward, if an authorized protocol and guest are ready, run `run_usefulness.py` with a unique receipt, then `check_usefulness.py`. Never pass off static replay as measured channel leakage or a new preregistered run.

**Known blocker:** the original frozen 0.25-second SC-01 replay on QEMU TCG gave 0/64 baseline and 0/64 mediated lifetimes. This source package cannot cure hardware-virtualization availability, restore the usefulness floor or establish complete receiver observation. An authorized host and separately frozen valid experimental plan are required. All historical receipts and result hashes remain unchanged.
