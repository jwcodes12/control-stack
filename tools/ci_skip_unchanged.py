#!/usr/bin/env python3
"""Fast-tier CI helper: skip a check whose inputs have not changed since the last run of that check that passed on this runner.

    python3 tools/ci_skip_unchanged.py --name transcript --inputs 'ControlStack/**/*.lean' 'tools/x.py' -- python3 tools/x.py

The digest covers the bytes of every file matching the globs, the command line and the names of the globs. The check runs when the digest differs from the
recorded one, when nothing is recorded, or when CI_FORCE=1 / --force is given. Only a successful run records its digest. A skip prints SKIPPED
loudly: it is not a fresh verification. This is FEEDBACK ONLY (the self-hosted fast tier); the GitHub-hosted workflows never use it and always run everything.
"""
import argparse
import glob
import hashlib
import os
import subprocess
import sys
from pathlib import Path


def digest(root, patterns, command):
    h = hashlib.sha256()
    h.update(repr(command).encode())
    files = 0
    for pattern in sorted(patterns):
        h.update(b"\0glob\0" + pattern.encode())
        for name in sorted(glob.glob(str(Path(root) / pattern), recursive=True)):
            path = Path(name)
            if path.is_file() and not path.is_symlink():
                h.update(b"\0file\0" + str(path.relative_to(root)).encode() + b"\0")
                h.update(hashlib.sha256(path.read_bytes()).digest())
                files += 1
    return h.hexdigest(), files


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--name", required=True)
    p.add_argument("--inputs", nargs="+", required=True)
    p.add_argument("--cache-dir", default=os.environ.get("CI_CHECK_CACHE", str(Path.home() / ".ci-check-cache")))
    p.add_argument("--force", action="store_true")
    p.add_argument("--root", default=".")
    p.add_argument("command", nargs=argparse.REMAINDER)
    a = p.parse_args(argv)
    command = a.command[1:] if a.command[:1] == ["--"] else a.command
    if not command:
        p.error("a command is required after --")
    now, files = digest(a.root, a.inputs, command)
    record = Path(a.cache_dir) / (a.name + ".ok")
    if not (a.force or os.environ.get("CI_FORCE") == "1") and record.is_file() and record.read_text().strip() == now:
        print(f"SKIPPED {a.name}: {files} input files unchanged since the last green run on this runner (digest {now[:12]}); NOT re-verified")
        return 0
    code = subprocess.run(command).returncode
    if code == 0:
        record.parent.mkdir(parents=True, exist_ok=True)
        tmp = record.with_suffix(".tmp")
        tmp.write_text(now + "\n")
        tmp.replace(record)
    return code


if __name__ == "__main__":
    sys.exit(main())
