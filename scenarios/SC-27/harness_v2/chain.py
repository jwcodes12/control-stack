#!/usr/bin/env python3
"""SC-27 anchor chain: the hash chain (prereg/SC27-ANCHOR-v2.md).

h0 = SHA-256("sc27-genesis"); head_k = SHA-256(head_{k-1} || SHA-256(canonical JSON of entry_k)), as hex. A log's
storage file holds one JSON line per entry: {"i", "entry", "head"}. Imported by the harness processes (the runner
passes this directory explicitly; they run with -I -S).
"""
import hashlib
import json
import os

H0 = hashlib.sha256(b"sc27-genesis").hexdigest()


def step(head, entry):
    return hashlib.sha256(bytes.fromhex(head) +
                          hashlib.sha256(json.dumps(entry, sort_keys=True, separators=(",", ":")).encode()).digest()
                          ).hexdigest()


def head_of(entries):
    h = H0
    for e in entries:
        h = step(h, e)
    return h


def heads(entries):
    out, h = [], H0
    for e in entries:
        h = step(h, e)
        out.append(h)
    return out


def read_entries(path):
    """complete lines only (a concurrent append may leave a partial last line)"""
    if not os.path.exists(path):
        return []
    out = []
    with open(path, "rb") as fh:
        data = fh.read()
    for line in data.split(b"\n")[:-1] if not data.endswith(b"\n") else data.split(b"\n"):
        if line.strip():
            out.append(json.loads(line)["entry"])
    return out


def write_storage(path, entries):
    """(writer-side) replace a log's storage with entries and a consistently recomputed chain, atomically"""
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        for i, (e, h) in enumerate(zip(entries, heads(entries))):
            fh.write(json.dumps({"i": i, "entry": e, "head": h}) + "\n")
        fh.flush()
        os.fsync(fh.fileno())
    os.rename(tmp, path)
