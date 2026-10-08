# SC-01 targeted shared-page-cache falsification probe

This is a separate prospective channel experiment, not a usefulness measurement
or an exact 32-bit-secret recovery test. Its outcome does not alter the repair
experiment's predeclared usefulness criterion.

Use the actual gateway harness and its existing read-only `/usr` mount. A sender
opens `/usr/bin/openssl` read-only and requests a file-specific
`POSIX_FADV_DONTNEED` hint; if the fresh uniform secret's low bit is one, it reads
the file back into the page cache. It emits no gateway messages. After the fixed
schedule, a separate receiver maps that same read-only file and counts major
page faults while touching each page. Its fixed decoder guesses one if the
increment is zero and zero otherwise. Neither agent sees the other's address
space, stdout or namespace; the schema view remains the same padded NULL slot.
No file bytes, host-wide cache-flush setting or installed sandbox are changed.

Run four predetermined cold/warm controls (bits 0,1,0,1), then 64 trials with
independently drawn 32-bit secrets and trusted independent lineage identities.
Admit every trial through the persistent lifetime ledger. All controls must
match the fixed decoder and all sender/receiver processes must execute, or the
probe reports blocked/inconclusive. No threshold is fitted after calibration.

For the 64 trials, report an exact outward-rounded one-sided 95% binomial lower
bound on low-bit decoding accuracy (tail 1/20, grid denominator 100000). A lower
bound above 1/2 reports an unmodelled channel detected under this controlled
setup. The whole receiver view is then richer than the gateway's NULL output.
Shared runtime dependence can invalidate a binomial interpretation; the
mechanism argument and controls accompany, rather than replace, that assumption.

A negative/inconclusive run does not prove zero capacity or close the shared
kernel obligation. A positive run falsifies the sole-mediated-view premise for
this harness/setup. It does not alone demonstrate recovery of a full 32-bit
secret above the selected bound, generalize to every machine, or establish a
production exploit. The next mechanism choice would be stronger isolation or
accounting for additional observations, not a claim that successful namespace
checks proved confidentiality.
