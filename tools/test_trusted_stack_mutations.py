#!/usr/bin/env python3
"""Check that independent admission controls reject weakened broker variants.

All mutations live in private temporary copies; the checkout is never changed.
--live additionally exercises the real socket disconnect regression as root.
"""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    if args.live and os.geteuid() != 0:
        parser.error("--live requires root for separate Linux UIDs")
    mutations = [
        ("global-cap", "controller.py", "or meta[2] + cost > meta[0]", "or False"),
        ("lease-cap", "controller.py", "lease[2] + cost > lease[1]", "False"),
        ("approval-expiry", "controller.py", "or approval[5] <= self._now()", "or False"),
        ("revocation", "controller.py", "or lease[4] or lease[3] <= self._now()", "or False or lease[3] <= self._now()"),
        ("halt", "controller.py", "meta is None or meta[1]", "meta is None"),
        ("artifact-integrity", "controller.py", "hashlib.sha256(body[0]).hexdigest() != digest", "False"),
    ]
    if args.live:
        mutations.append(("disconnect-kills-broker", "server.py",
            '                    try:\n                        conn.sendall((json.dumps(response, sort_keys=True) + "\\n").encode())\n                    except OSError:\n                        # A caller can disconnect after a transaction commits.\n                        # Never kill the trusted service or undo that commit;\n                        # subsequent retry is rejected by the consumed nonce.\n                        pass',
            '                    conn.sendall((json.dumps(response, sort_keys=True) + "\\n").encode())'))
    for name, file, before, after in mutations:
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            shutil.copytree(ROOT / "trusted_stack", work / "trusted_stack",
                            ignore=shutil.ignore_patterns("__pycache__"))
            target = work / "trusted_stack" / file
            text = target.read_text()
            if text.count(before) != 1:
                raise RuntimeError(f"{name}: mutation site drifted")
            target.write_text(text.replace(before, after))
            if file == "server.py":
                (work / "tools").mkdir()
                shutil.copy(ROOT / "tools/test_trusted_stack_broker.py", work / "tools")
                cmd = [sys.executable, "tools/test_trusted_stack_broker.py"]
            else:
                cmd = [sys.executable, "-m", "unittest",
                    "trusted_stack.test_transition.TransitionTests.test_boundaries_replay_roles_restart_and_halt",
                    "trusted_stack.test_transition.TransitionTests.test_corrupt_reviewed_bytes_rejected"]
            env = dict(os.environ, PYTHONPATH=str(work))
            result = subprocess.run(cmd, cwd=work, env=env, capture_output=True,
                                    text=True, timeout=30)
            if result.returncode == 0:
                raise RuntimeError(f"{name}: weakened implementation escaped the oracle")
            # A crash/import failure in the oracle is not a killed safety mutant.
            expected = ("AssertionError",) if file == "controller.py" else (
                "ConnectionRefusedError", "FileNotFoundError")
            if not any(marker in result.stderr for marker in expected):
                raise RuntimeError(f"{name}: unexpected failure: {result.stderr}")
            print(f"PASS: rejected {name} mutant")
    print(f"PASS: {len(mutations)} deliberately weakened variants rejected")


if __name__ == "__main__":
    main()
