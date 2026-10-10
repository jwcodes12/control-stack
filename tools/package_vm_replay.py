#!/usr/bin/env python3
"""Reproducible, read-only SC-01 QEMU replay SOURCE bundle.

Includes the pinned input recipes, NOT the guest images, passwords, runtime
receipts or frozen evidence. Never runs a VM and never overwrites an archive.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCES = (
    "gateway/scenario/contract.json",
    "gateway/vm/README.md",
    "gateway/vm/STATUS.md",
    "gateway/vm/BOUND.md",
    "gateway/vm/image.lock.json",
    "gateway/vm/provision.py",
    "gateway/vm/pair.py",
    "gateway/vm/guest.py",
    "gateway/vm/init.sh",
    "gateway/vm/init_guest.sh",
    "gateway/vm/check_isolation.py",
    "gateway/vm/test_isolation.py",
    "gateway/vm/check_usefulness.py",
    "gateway/vm/run_usefulness.py",
    "gateway/vm/configs/local-20261008-final.json",
)
PREFIX = "sc01-vm-source-v1"


def manifest():
    result = []
    for rel in SOURCES:
        body = (ROOT / rel).read_bytes()
        result.append({"path": rel, "size": len(body),
                       "sha256": hashlib.sha256(body).hexdigest()})
    return {"schema": "control-stack/sc01-source-bundle-v1", "files": result,
            "limitations": "source only; no images, runtime receipts, evidence or VM proof"}


def build_bytes():
    data = manifest()
    manifest_bytes = (json.dumps(data, sort_keys=True, separators=(",", ":")) + "\n").encode()
    output = io.BytesIO()
    with gzip.GzipFile(fileobj=output, mode="wb", filename="", mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode="w", format=tarfile.USTAR_FORMAT) as archive:
            for name, body in [(rel, (ROOT / rel).read_bytes()) for rel in SOURCES] + [
                ("SOURCE-MANIFEST.json", manifest_bytes)]:
                entry = tarfile.TarInfo(PREFIX + "/" + name)
                entry.size, entry.mode, entry.mtime = len(body), 0o644, 0
                entry.uid = entry.gid = 0
                entry.uname = entry.gname = ""
                archive.addfile(entry, io.BytesIO(body))
    return output.getvalue()


def verify(path):
    payload = path.read_bytes()
    # Check both reproducibility and every archived member without extraction.
    if payload != build_bytes():
        raise ValueError("bundle bytes differ from deterministic current source inputs")
    with tarfile.open(fileobj=io.BytesIO(payload), mode="r:gz") as archive:
        expected = [PREFIX + "/" + rel for rel in SOURCES] + [PREFIX + "/SOURCE-MANIFEST.json"]
        members = archive.getmembers()
        if [m.name for m in members] != expected or not all(m.isfile() for m in members):
            raise ValueError("unsafe or unexpected archive entries")
        saved = json.loads(archive.extractfile(members[-1]).read())
        if saved != manifest():
            raise ValueError("source SHA-256 manifest mismatch")
    return hashlib.sha256(payload).hexdigest()


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--output", type=Path)
    p.add_argument("--verify", type=Path)
    a = p.parse_args()
    if (a.output is None) == (a.verify is None):
        p.error("specify exactly one of --output and --verify")
    if a.verify:
        print("verified source bundle sha256:", verify(a.verify))
        return
    if a.output.exists():
        raise SystemExit("refusing to overwrite existing source bundle")
    payload = build_bytes()
    with a.output.open("xb") as f:
        f.write(payload)
    print("wrote source-only bundle", a.output, "sha256:", hashlib.sha256(payload).hexdigest())


if __name__ == "__main__":
    main()
