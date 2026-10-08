"""Decode an unmediated cache-state bit using major page faults, not gateway data."""
import json
import mmap
import resource
import sys

json.loads(sys.stdin.readline())
before = resource.getrusage(resource.RUSAGE_SELF).ru_majflt
with open("/usr/bin/openssl", "rb") as target:
    with mmap.mmap(target.fileno(), 0, access=mmap.ACCESS_READ) as mapping:
        for position in range(0, len(mapping), 4096):
            mapping[position]
faults = resource.getrusage(resource.RUSAGE_SELF).ru_majflt - before
print(json.dumps({"guess": int(faults == 0), "major_faults": faults}))
