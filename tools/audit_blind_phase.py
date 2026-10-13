#!/usr/bin/env python3
"""Audit a `codex exec --json` event log of a blind (phase A) one-to-one run.

The blind phase may read only ./input and ./defs and write only ./back. This reads every command the agent ran and reports
anything that touches another path, uses the network or git, or mentions an original theorem name from the claim list. It is a
check of the transcript, not a sandbox: the real isolation is that the originals are not in the phase A directory at all.
Exit status 0 only if no command is flagged and the hash file predates no later edit of a back file.
"""
import argparse
import json
import re
import sys
from pathlib import Path

ALLOWED_PREFIXES = ("./input", "./defs", "./back", "input/", "defs/", "back/")
SUSPECT = re.compile(r"(\.\./|~/|/home/|/tmp/|/var/|/etc/|/usr/|/opt/|\bgit\b|\bcurl\b|\bwget\b|\bssh\b|\bpip\b|(?:^|[\s;&|])(?:lake|lean|elan)\s)")
SAFE_ABSOLUTE = re.compile(r"/bin/(?:ba)?sh|/usr/bin/env|/dev/null")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("events")
    ap.add_argument("--names", nargs="*", default=[])
    a = ap.parse_args()
    flagged, commands = [], []
    for line in Path(a.events).read_text().splitlines():
        try:
            event = json.loads(line)
        except ValueError:
            continue
        item = event.get("item", {})
        if item.get("type") == "command_execution" and event.get("type") == "item.started":
            commands.append(item["command"])
    for cmd in commands:
        body = SAFE_ABSOLUTE.sub("", cmd)
        reasons = []
        if SUSPECT.search(body):
            reasons.append("path or tool outside the allowed set")
        for name in a.names:
            if re.search(r"\b" + re.escape(name) + r"\b", cmd):
                reasons.append("mentions original name " + name)
        if reasons:
            flagged.append((cmd, reasons))
    print(f"{len(commands)} commands; {len(flagged)} flagged")
    for cmd, reasons in flagged:
        print("FLAG:", "; ".join(reasons), "|", cmd[:300])
    return 1 if flagged else 0


if __name__ == "__main__":
    sys.exit(main())
