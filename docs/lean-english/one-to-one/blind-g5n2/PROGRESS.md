# Phase B progress

Done:

- Verified all twelve Phase A hashes; compiled every back file as written.
- Saved identical typed files, no-repair diff records and typed SHA-256 hashes before opening originals.
- Compared all twelve original declaration types with the frozen Back statements.
- Saved pointwise comparisons and explicit scope reductions for claims 11 and 12.
- Deterministically gated all twelve claims and all twelve non-vacuity witnesses separately.
- Added gated counterexamples to over-readings: differing execution outcomes, reused confirmation, and a correct-guess weighted mass of 3/2.
- Saved RESULTS.md, source excerpts/hashes, proof hashes, gate receipts and reproducible regate.py.
- Ran regate.py from a clean receipt/cache/temp state: exit 0; 36 Lean checks passed. Its persistent writes were exactly the twelve receipts.

Not done / what could not be certified:

- No formal information measure is provided for claim 11's log-K bits gloss; only the exact-decoding bound is certified.
- Claim 12's probability interpretation is not certified without kernel normalisation. The formal inequality is certified.
- External runtime assumptions (true platform issuer, isolation without side channels, informed UI, actual TV/L estimates and phase rotation) are not established by these theorem comparisons.
- No mathematical claim remains unfinished or UNDECIDED.

Time:

- Typed statements frozen: 2026-10-13T05:13:08.885759+00:00 (UTC), before opening any original declaration.
- Completion: 2026-10-13T05:28:06.929771+00:00 (UTC).
- Elapsed since typed freeze: 15.0 minutes; initial hash checks and compilation preceded the freeze.

Protocol deviation:

An early Python import generated an automatic bytecode-cache file beside the original gate helper outside blind-g5n2/ at 05:16:53 UTC. Only that run-created cache was removed. The helper was subsequently copied byte-identically inside blind-g5n2/ and regate disables bytecode generation. No source outside blind-g5n2/ was edited, ControlStack/ was never changed, and git was never run. This historical output-directory violation is disclosed; the clean final regate stayed within the authorised directory. Excluded English/comparison documents were never read.
