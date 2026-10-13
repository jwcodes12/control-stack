# Phase B progress

Done: **10/10 claims**, all `EQUIVALENT` under the frozen Back readings; **10/10 separately gated witnesses**.

- Verified the original Phase A hashes; compiled every back file as written.
- Added only an import per claim; saved all 10 meaning-preserving diffs and compiler logs.
- Successfully compiled every repaired file and froze `typed/HASHES.json` at 2026-10-13T10:11:57.586985+00:00, before inspecting original declaration text.
- Found and inspected all originals; recorded their locations, headers and source hashes in `ORIGINALS.json`.
- Saved the literal frozen Back definitions and pointwise iff comparisons; all comparison proofs use definitional equality rather than the truth of the original theorems.
- Created the copied wrapper and byte-identical deterministic gate helper; froze the saved comparisons and proofs in `COMPARISON-HASHES.json`.
- Gated all claim and witness targets. Non-degenerate witnesses exercise successful commits, stale/current rollback, accepted manifests, multiple anchors, rejected tampering, whole-state halt, fork alarms and concrete empty-truncation silence.
- Wrote `RESULTS.md`, including the verdict/receipt table, English corrections, ambiguity analysis and a per-claim “Does NOT say” audit.
- Tested `regate.py` from the repository root with an empty initial `LEAN_PATH`: it rebuilt dependencies offline, re-gated all 20 targets, exited 0, cleaned its scratch directory and changed only receipts/receipt logs. `VALIDATION.receipt.json` records the checks.

Not done: **none of the requested work remains**. Proposed English replacements are only in `RESULTS.md`, as requested.

Time: first recorded checkpoint 2026-10-13T10:09:43.239309+00:00; typed freeze 2026-10-13T10:11:57.586985+00:00; completed 2026-10-13T10:25:39.498514+00:00. Elapsed since first recorded checkpoint: 15.9 minutes.

What I could not do: the checkout lacked `.olean` files for the required project modules, so direct imports initially failed. I resolved this by building the required modules and dependencies offline only under this directory. The build/import scanner processed source files without showing original declarations to the comparing agent before the typed freeze. The first gate attempt also found missing proof-namespace opens; these were repaired in the comparison proof files and all gates were rerun successfully. Neither issue prevented completion.

The original Back bodies, `ControlStack/`, and English input/part files were not edited. No git command, download, external publication, or sub-agent was used. The checks make no new claim about real hardware, Python correspondence, fsync behavior or SHA-256 beyond the modeled premises.
