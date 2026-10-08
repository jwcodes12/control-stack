"""Trusted namespace/capability preflight, run without a secret."""
import json
from pathlib import Path

status = {}
for line in Path("/proc/self/status").read_text().splitlines():
    if ":" in line:
        key, value = line.split(":", 1)
        status[key] = value.strip()
print(json.dumps({
    "netns": Path("/proc/self/ns/net").stat().st_ino,
    "pidns": Path("/proc/self/ns/pid").stat().st_ino,
    "effective_capabilities": status["CapEff"],
    "no_new_privileges": status["NoNewPrivs"],
    "interfaces": [x.split(":")[0].strip() for x in Path("/proc/net/dev").read_text().splitlines()[2:]],
    "routes4": Path("/proc/net/route").read_text(),
}))
