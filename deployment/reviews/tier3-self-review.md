# Tier 3 adversarial self-review

Fresh scanning and archived v0 parsing are distinct. Fresh scans normalize JSON or
YAML, resolve actual source paths and record host custody and image observations.
The 44 static cases are configuration regressions; dangerous cases were never
started. Actual symlink tests use disposable directories, not invented aliases.

Review found that otherwise-separated Compose UIDs could disagree with the baked
entrypoint's literal principal policy. Agent UID 23700 with declared trusted UID
23800 would retain baked admin authority. The new guard checks source-matched
principal arguments and reference environment dispatch; the regression rejects
this assignment. Unknown code never supplies a guessed policy. This fix is also
applied when replaying old captures whose source pin establishes the known policy.

The first fresh seven-case run passed, but independent replay after this guard
changed failed on the UID-collision case (`IR differs`). That failed archive and
error remain unchanged. A new image/run was collected with the final guard;
independent reconstruction, relocation, actual sink-byte tampering and principal-
policy tampering tests pass. No stored certificate was edited to mask a difference.

Image scanning exports a stopped isolated container, never starts it and reads
metadata/selected regular source bytes without extracting the tar onto the host.
Nine actual exports yield identical semantic facts; tar acquisition hashes are
kept outside semantic IR. Unit tests compare identical IR and Python bundle bytes
under JSON key-order/whitespace changes and use actual Compose YAML normalization.
Their injected image observations are explicitly unit fixtures, not runtime evidence.
All nine final raw IR snapshots have independent kernel acceptance/refutation
certificates. The 44 fixtures plus 250 seeded mutations have zero differential
mismatches; 520 additive mutations preserve rejection.

Custody checks require own private directories and channel permissions. They do
not prove no rollback, no future permission changes, benign daemon behavior or
complete capture. Merged filesystem mode inspection does not verify native library
semantics or arbitrary image behavior. Unsupported features remain UNKNOWN, which
can over-reject safe configurations and never claims an attack was blocked.

Source/image policy equality, canonicalization, schema-only migration and strict
unknown-field rejection are covered. Original acquisition pins are retained outside
IR; migration invents no physical facts. The gaps document explicitly excludes
covert host/runtime divergence. Final cleanup shows no cstack-r2 resources; only
the pre-existing postgres image remains. Frozen artifacts and scenario status are
unchanged. Final-head CI must still pass before advancing to Tier 4.
