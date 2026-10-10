#!/usr/bin/env python3
"""Offline experiment image entry point. Protocol implementation stays in trusted_stack."""
import os
import subprocess
import sys
import time
from pathlib import Path
role = os.environ['SLICE_ROLE']
if role == 'broker':
    cap = int(Path('/private/cap').read_text()) if Path('/private/cap').exists() else 1
    if cap <= 0:
        raise ValueError('positive shared cap required')
    os.execv(sys.executable, [sys.executable, '-m', 'trusted_stack.server', '--db', '/private/gate.db', '--socket', '/channel/broker.sock', '--agents', '23701,23702', '--reviewers', '23703', '--approvers', '23704', '--admins', '23700', '--bootstrap-cap', str(cap)])
# Receiver stays ready; the harness invokes its real deliver_record function
# after two independent agent contenders have released against the shared cap.
while True:
    time.sleep(1)
