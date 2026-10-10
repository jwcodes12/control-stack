# Archive episode and Inspect-shaped JSON interfaces

`deployment/schemas/episodes-v0.1.json` describes the nine-episode analysis report.
Each observation retains its original JSON value, source path, JSON Pointer,
attribution class and reason. Image/IR/SQLite/sink source hashes remain in each
episode. Missing monitor/latency measurements are typed as null and UNASSESSED.

`tools/export_deployment_inspect.py` writes a restricted Inspect v2 JSON shape
with `eval`, `plan`, `stats` and nine `samples`. The official
[log API](https://inspect.aisi.org.uk/reference/inspect_ai.log.html) documents the
fields. `deployment/runs/tier7/inspect-reference.json` records the SHA-256 of the
[official source](https://github.com/UKGovernmentBEIS/inspect_ai/blob/main/src/inspect_ai/log/_log.py)
inspected on 2026-10-10, required fields and types. No remote source was executed
or installed. `inspect-export-v2.json` validates our restricted local export subset.

The model name is `scripted/archive`, an explicit placeholder for historical
scripted observations. No model request or synthetic conversation is created.
Sample metadata contains the complete original episode. Scores are strings of
recorded attribution classes, not security pass/fail grades or LLM capability.
`status=success` means the conversion completed. It does not claim a security gate
passed or an Inspect evaluation ran. Empty stats do not fabricate model usage.

`eval.created` comes from the first preregistration addition commit time, not an
invented episode execution timestamp. Export identifiers derive deterministically
from the analysis JSON. Original latency measurements remain in sample metadata;
unknown latency never becomes zero. Preregistered gaps and four-arm gating remain
in eval metadata. The output cannot overwrite its input.

The dependency-free local validator supports only the schema keywords used here,
rejects unknown keywords and external references, and requires integer values to
use integer JSON encoding. It is not a complete JSON Schema implementation.
It validates the committed analysis/export, including rejection of fake alert
counts and boolean counts. Runtime loading with inspect_ai is GATED because the
package is unavailable and installs are forbidden. No SDK-loader pass or future
Inspect-version compatibility is claimed. Actual integration should validate the
export with the pinned SDK when that resource becomes available.
